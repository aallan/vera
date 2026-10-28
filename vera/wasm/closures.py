"""Closure and anonymous function translation mixin for WasmContext."""

from __future__ import annotations

from vera import ast, fold, naming
from vera.skip import CodegenInvariantError
from vera.types import NAT, FunctionType, RefinedType, base_type
from vera.wasm.helpers import (
    WasmSlotEnv,
    _align_up,
    field_layout,
    gc_shadow_push,
)


class ClosuresMixin:
    """Mixin providing closure and anonymous function translation methods."""

    def _translate_anon_fn(
        self, expr: ast.AnonFn, env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate an anonymous function to a closure value (i32 pointer).

        Creates a heap-allocated closure struct:
          [func_table_idx: i32] [capture_0] [capture_1] ...

        Records the AnonFn for later lifting by codegen.py.
        """
        # Collect free variables (captures from enclosing scope)
        captures = self._collect_free_vars(expr)

        # Assign closure ID and register for later lifting
        closure_id = self._next_closure_id
        self._next_closure_id += 1
        self._pending_closures.append((expr, captures, closure_id))

        # Compute closure struct layout
        # offset 0: func_table_idx (i32, 4 bytes)
        # The env block is laid out by the SAME rule a constructed object is
        # (`helpers.field_layout`), rather than by a copy of its widths: a
        # pair capture (#535) is ptr + len, two consecutive 4-byte-aligned
        # i32 fields, and `_compile_lifted_closure` reads them back through
        # the same rule.
        field_offsets: list[tuple[int, str]] = []
        offset = 4  # skip func_table_idx
        for _tname, _idx, cap_wt in captures:
            field_off, offset = field_layout(offset, cap_wt)
            field_offsets.append((field_off, cap_wt))
        total_size = max(_align_up(offset, 8), 8)  # at least 8 bytes

        # Emit allocation + stores
        self.needs_alloc = True
        instructions: list[str] = []
        tmp = self.alloc_local("i32")

        # Allocate closure struct
        instructions.append(f"i32.const {total_size}")
        instructions.append("call $alloc")
        instructions.append(f"local.set {tmp}")
        instructions.extend(gc_shadow_push(tmp))

        # Store func_table_idx at offset 0
        instructions.append(f"local.get {tmp}")
        instructions.append(f"i32.const {closure_id}")
        instructions.append("i32.store offset=0")

        # Store each captured value.  Pair captures (#535) live at
        # consecutive locals (env pushed `ptr_idx`; the matching `len`
        # is at `ptr_idx + 1`); the let-binding emit and the parameter
        # emit both use this convention.  We mirror it by writing two
        # i32 fields at `cap_offset` and `cap_offset + 4`.
        for i, (tname, cap_idx, cap_wt) in enumerate(captures):
            cap_offset, _wt = field_offsets[i]
            local_idx = env.resolve(tname, cap_idx)
            if local_idx is None:
                return None  # capture reference unresolvable
            if cap_wt == "i32_pair":
                # Store ptr at cap_offset
                instructions.append(f"local.get {tmp}")
                instructions.append(f"local.get {local_idx}")
                instructions.append(f"i32.store offset={cap_offset}")
                # Store len at cap_offset + 4
                instructions.append(f"local.get {tmp}")
                instructions.append(f"local.get {local_idx + 1}")
                instructions.append(f"i32.store offset={cap_offset + 4}")
            else:
                instructions.append(f"local.get {tmp}")
                instructions.append(f"local.get {local_idx}")
                store_op = (
                    "i64.store" if cap_wt == "i64"
                    else "f64.store" if cap_wt == "f64"
                    else "i32.store"
                )
                instructions.append(f"{store_op} offset={cap_offset}")

        # Leave closure pointer on stack
        instructions.append(f"local.get {tmp}")
        return instructions

    def _translate_apply_fn(
        self, call: ast.FnCall, env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate apply_fn(closure, arg0, arg1, ...) to call_indirect.

        The closure is an i32 pointer to:
          [func_table_idx: i32] [captures...]

        The lifted function signature is:
          (param $env i32) (param $p0 <type>) ... (result <type>)
        """
        instructions: list[str] = []
        closure_arg = call.args[0]
        value_args = call.args[1:]

        # The closure's type is the function type the checker gave the
        # argument, whatever its shape: a closure literal, a slot, a call
        # returning one, a cell read (#1516).  An argument it did not type
        # as a function is recorded for the [E616] diagnostic (#632) and
        # the function is skipped.
        fn_ty = self._type_of(closure_arg)
        if isinstance(fn_ty, RefinedType):
            fn_ty = base_type(fn_ty)
        if not isinstance(fn_ty, FunctionType):
            self._apply_fn_inference_failures.append(closure_arg)
            return None

        # Translate the closure argument — get i32 pointer
        closure_instrs = self.translate_expr(closure_arg, env)
        if closure_instrs is None:
            return None

        # Save closure pointer to temp local
        tmp = self.alloc_local("i32")
        instructions.extend(closure_instrs)
        instructions.append(f"local.set {tmp}")

        # Push closure pointer as first arg (env for lifted function)
        instructions.append(f"local.get {tmp}")

        # #820: the closure's formal types, so an argument narrowing into a
        # @Nat formal is runtime-guarded at the call boundary (the
        # call_indirect has no per-formal coercion otherwise).
        formal_types = fn_ty.params

        # Translate and push remaining arguments
        arg_wasm_types: list[str] = []
        for i, arg in enumerate(value_args):
            formal = formal_types[i] if i < len(formal_types) else None
            arg_instrs = self.translate_expr(arg, env)
            if arg_instrs is None:
                return None
            # #1017: the @Int -> @Nat NARROWING.
            # A negative @Int argument narrowing into a @Nat closure formal would
            # otherwise enter the formal reinterpreted (silently) — guard it at
            # the call_indirect boundary, exactly as the verifier's apply_fn
            # branch now obligates it.
            if (formal is not None and base_type(formal) == NAT
                    and self._narrows_into_nat(arg)):
                arg_instrs = self._emit_nat_bind_guard(arg_instrs, at=arg)
            instructions.extend(arg_instrs)
            # The parameter's width in the `call_indirect` signature is the
            # formal's, not the argument's (#1256): both sides of an
            # indirect call must name one type, and the lifted closure's own
            # signature is built from the same function type
            # (`_compile_lifted_closure`).  Deriving the call site's from the
            # argument registered a second, incompatible `$closure_sig` for a
            # `@Byte` formal fed an int literal, and `wasm trap: indirect
            # call type mismatch` at every call.  The RESULT comes from the
            # same type (`_closure_return_width` below).
            # Pair types (String, Array) push two i32 values onto the stack.
            wt = (
                self._width_of(formal) if formal is not None
                else self._expr_width(arg)
            )
            if wt == "i32_pair":
                arg_wasm_types.extend(["i32", "i32"])
            elif wt is None:
                # Unit formal: `translate_expr` pushed nothing onto the
                # stack above, so this entry must NOT contribute a phantom
                # param to the call_indirect sig.  The closure-lift side
                # (`vera/codegen/closures.py`) likewise skips Unit params,
                # so the two sides agree on omitting them (#586).
                #
                # `None` still means Unit and nothing else on BOTH branches
                # of the width above (#1256 moved the common one).  Through
                # `_canonical_wasm_type` it is the `Unit` arm of
                # `_named_type_to_wasm`, the one name mapped to `None` —
                # every other resolution returns a width string, and a
                # walker that reaches no `NamedType` defaults to `"i64"`.
                # Through the `_expr_width` fallback it is the
                # type-checker invariant that the only well-typed
                # expression it answers `None` for is a Unit-typed one.
                # Either way an explicit branch documents the intent
                # without a runtime assert (which would have to re-run
                # type inference to verify Unit-ness, defeating the point).
                pass
            else:
                arg_wasm_types.append(wt)

        # Load func_table_idx from closure struct
        instructions.append(f"local.get {tmp}")
        instructions.append("i32.load offset=0")

        # Build call_indirect type signature
        # Return type: infer from the enclosing function's expected return
        # or from the closure's type if available
        ret_wt = self._closure_return_width(closure_arg)
        param_parts = " ".join(
            f"(param {wt})" for wt in ["i32"] + arg_wasm_types
        )
        if ret_wt == "i32_pair":
            result_part = " (result i32 i32)"
        elif ret_wt:
            result_part = f" (result {ret_wt})"
        else:
            result_part = ""
        sig_key = f"{param_parts}{result_part}"

        # Register this signature for the codegen to emit as a type decl
        if sig_key not in self._closure_sigs:
            sig_name = f"$closure_sig_{len(self._closure_sigs)}"
            self._closure_sigs[sig_key] = sig_name

        sig_name = self._closure_sigs[sig_key]
        instructions.append(f"call_indirect (type {sig_name})")
        return instructions

    def _collect_free_vars(
        self,
        anon: ast.AnonFn,
    ) -> list[tuple[str, int, str]]:
        """Collect free variables in an anonymous function body.

        Walks *anon* with the fold's scope walk (:func:`vera.fold.scoped`),
        which has the closure's parameters and every binder its body declares
        in scope where each reference is read, and finds the SlotRef nodes
        that resolve to none of them: those reference bindings from the
        enclosing scope.  Returns list of (type_name, adjusted_index,
        wasm_type).  The adjusted_index is the De Bruijn index in the OUTER
        scope: the reference's index less the binders of its name the closure
        holds where it is read.

        After walking, the captures are normalised per type so that the
        lift-side env push (in `_compile_lifted_closure`) yields a
        per-type stack where De Bruijn resolution works correctly.  Two
        normalisations are applied (#615):

        1. **Prefix fill.**  If the body references `@T.k` (outer_idx K)
           while leaving some `@T.j` (j<K) unreferenced, the lift-side
           stack is short by (K-j) entries and `env.resolve("T", k)`
           returns None.  Synthetic entries for the unreferenced outer
           indices in [0, max] are added so the prefix is contiguous.
           Their `wasm_type` matches the type's other captures (same
           `type_name` always maps to the same WAT type).
        2. **Descending sort within type.**  `WasmSlotEnv.resolve` uses
           `pos = len(stack) - 1 - index`, so the captured outer_idx K
           must be at the bottom of the per-type stack and outer_idx 0
           at the top (just below the closure's own param pushes).
           Walker-order is determined by source position of the SlotRef
           (DFS); body shapes like `@Int.1 - @Int.2` add (Int, 0) before
           (Int, 1), producing an ascending list that pushes them in
           the wrong order — body's `@Int.k` then resolves to the WRONG
           captured local.  Pre-fix this manifested as a silent
           miscompute (no trap, wrong result) for any closure capturing
           multiple slots of the same type when walk order happened to
           be ascending.  Sorting each per-type group in *descending*
           outer_idx order before push gives the correct stack layout.
        """
        free: list[tuple[str, int, str]] = []
        seen: set[tuple[str, int]] = set()
        for node, scope in fold.scoped(anon, self._type_expr_name):
            if not isinstance(node, ast.SlotRef):
                continue
            # #1208: the ONE renderer, against this context's alias
            # environment — a captured slot must key its capture under the
            # SAME name `_translate_slot_ref` resolves and the closure's
            # binders were named by (`_type_expr_name`), or the capture
            # desyncs and the enclosing function drops (`unknown func`).
            # Nested composites stay fully qualified (#914 finding 2).
            type_name = naming.slot_ref_key(node, self._alias_env)
            if scope.resolve(type_name, node.index) is not None:
                continue
            # This refers to an outer scope binding
            outer_idx = node.index - scope.count(type_name)
            key = (type_name, outer_idx)
            if key in seen:
                continue
            seen.add(key)
            # The capture's serialisation width is the captured value's,
            # the width of the type the checker gave the reference (#1525):
            # String / Array<T> values live as two consecutive i32 slots
            # (ptr, len) and a capture must serialise both (#535), a
            # `Future<T>` is held as `T` is (#841, #1044), and a
            # parameterised alias is its target under its arguments, which
            # the slot name's spelling had no width for.  Both
            # `_translate_anon_fn` (layout + store) and
            # `_compile_lifted_closure` (layout + load) read this `wt` back
            # from the capture tuple, so the two sides agree by
            # construction.  A zero-size value is captured as the i32 its
            # absent local reads as, as the capture path always did.
            captured = self._type_of(node)
            if captured is None:
                raise CodegenInvariantError(
                    "a captured slot reference the check did not type", node)
            wt = self._width_of(captured) or "i32"
            free.append((type_name, outer_idx, wt))

        # Group by type so we can fill prefix and sort within each type
        # independently.  `dict` preserves insertion order, so the
        # cross-type ordering follows first-encounter order in the walk
        # (irrelevant for resolution since each type has its own stack).
        by_type: dict[str, list[tuple[int, str]]] = {}
        for tname, idx, wt in free:
            by_type.setdefault(tname, []).append((idx, wt))

        result: list[tuple[str, int, str]] = []
        for tname, entries in by_type.items():
            # Same `type_name` → same `wasm_type` (the wt computation in
            # the loop above is deterministic per type_name); use the
            # first entry's wt for any synthetic prefix fills.
            wt = entries[0][1]
            seen_idxs = {idx for idx, _ in entries}
            max_idx = max(seen_idxs)
            for j in range(max_idx + 1):
                if j not in seen_idxs:
                    entries.append((j, wt))
            # Descending outer_idx so the lift-side push lands the
            # highest outer_idx at the deepest position in the stack.
            entries.sort(key=lambda e: e[0], reverse=True)
            for idx, ewt in entries:
                result.append((tname, idx, ewt))

        return result
