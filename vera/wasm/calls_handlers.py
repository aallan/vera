"""Ability and effect handler translation mixin for WasmContext.

Handles: Show ability (_translate_show), Hash ability (_translate_hash,
_translate_hash_string), structural show/hash for composite types (#911),
and effect handlers (State<T>, Exn<E>).
"""

from __future__ import annotations

from dataclasses import fields, is_dataclass

from vera import ast
from vera.monomorphize import mangle_type_name
from vera.skip import CodegenSkip
from vera.wasm.helpers import (
    WasmSlotEnv,
    _element_load_op,
    _element_mem_size,
    _is_pair_element_type,
    gc_shadow_push,
)


class _ShowHashUnsupported(Exception):  # noqa: N818
    """Internal signal: a field is not showable/hashable here (#911).

    Raised mid-traversal from a nested field render/fold and caught by the
    top-level `_show_adt` / `_hash_adt` so the whole composite falls back to
    `CodegenSkip` (unchanged behaviour) rather than emitting partial code.
    Not a diagnostic — a control-flow unwind, hence the plain `Exception`.
    """


class CallsHandlersMixin:
    """Methods for translating Show/Hash dispatch and effect handlers."""

    # -----------------------------------------------------------------
    # Ability operation dispatch: show and hash (§9.8)
    # -----------------------------------------------------------------

    # Dispatch map: Vera type → to_string builtin name
    _SHOW_DISPATCH: dict[str, str] = {
        "Int": "to_string",
        "Nat": "nat_to_string",
        "Bool": "bool_to_string",
        "Byte": "byte_to_string",
        "Float64": "float_to_string",
    }

    def _translate_show(
        self, arg: ast.Expr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate show(x) to the appropriate to_string builtin.

        Dispatches based on the inferred Vera type of the argument:
        - Int/Nat/Bool/Byte/Float64 → corresponding to_string call
        - String → identity (the string IS its own representation)
        - Unit → literal "unit"
        """
        vera_type = self._infer_vera_type(arg)
        if vera_type is None:
            raise CodegenSkip(
                arg, "could not infer show() argument type"
            )

        # String → identity: show("hello") == "hello"
        if vera_type == "String":
            return self.translate_expr(arg, env)

        # Unit → literal "unit" string
        if vera_type == "Unit":
            offset, length = self.string_pool.intern("unit")
            return [f"i32.const {offset}", f"i32.const {length}"]

        # Decimal → decimal_to_string host import
        if vera_type == "Decimal":
            desugared = ast.FnCall(
                name="decimal_to_string", args=(arg,), span=arg.span,
            )
            return self._translate_call(desugared, env)

        # Dispatch to existing to_string builtins
        builtin = self._SHOW_DISPATCH.get(vera_type)
        if builtin is not None:
            # Reuse existing translate methods by constructing a FnCall
            desugared = ast.FnCall(
                name=builtin, args=(arg,), span=arg.span,
            )
            return self._translate_call(desugared, env)

        # Composite (#911): ADT / Tuple / Option / Result / Array.  Render
        # structurally, recursing into each field's own `show`.  Recover the
        # PARAMETERIZED type (`Option<Int>`, `Array<String>`) so inner field
        # types resolve — `_infer_vera_type` only reports the bare head.
        param_type = self._parameterized_arg_type(arg, vera_type)
        value_instrs = self.translate_expr(arg, env)
        if value_instrs is None:
            return None
        composite = self._show_value(param_type, value_instrs, arg)
        if composite is not None:
            return composite

        raise CodegenSkip(
            arg, f"show() not supported for type {vera_type!r}"
        )

    def _translate_hash(
        self, arg: ast.Expr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate hash(x) to a type-specific hash implementation.

        Returns an i64 hash value:
        - Int/Nat → identity (the value IS the hash)
        - Bool/Byte → i64.extend_i32_u (widen to i64)
        - Float64 → i64.reinterpret_f64 (bit pattern)
        - Unit → i64.const 0
        - String → FNV-1a hash
        """
        vera_type = self._infer_vera_type(arg)
        if vera_type is None:
            raise CodegenSkip(
                arg, "could not infer hash() argument type"
            )

        arg_instrs = self.translate_expr(arg, env)
        if arg_instrs is None:
            return None

        # Int/Nat → identity: hash(42) == 42
        if vera_type in ("Int", "Nat"):
            return arg_instrs

        # Bool/Byte → extend to i64
        if vera_type in ("Bool", "Byte"):
            return arg_instrs + ["i64.extend_i32_u"]

        # Float64 → bit-level reinterpretation
        if vera_type == "Float64":
            return arg_instrs + ["i64.reinterpret_f64"]

        # Unit → constant 0
        if vera_type == "Unit":
            return ["i64.const 0"]

        # String → FNV-1a hash
        if vera_type == "String":
            return self._translate_hash_string(arg_instrs)

        # Composite (#911): fold the constructor tag with each field's own
        # hash.  Parameterized type recovers inner field types (see show).
        param_type = self._parameterized_arg_type(arg, vera_type)
        composite = self._hash_value(param_type, arg_instrs, arg)
        if composite is not None:
            return composite

        raise CodegenSkip(
            arg, f"hash() not supported for type {vera_type!r}"
        )

    def _translate_hash_string(
        self, arg_instrs: list[str],
    ) -> list[str]:
        """Generate FNV-1a hash for a string (ptr, len) pair.

        FNV-1a: for each byte, hash = (hash XOR byte) * FNV_prime.
        Uses the 64-bit FNV-1a variant:
        - offset basis: 14695981039346656037
        - prime: 1099511628211
        """
        ptr = self.alloc_local("i32")
        slen = self.alloc_local("i32")
        idx = self.alloc_local("i32")
        hash_val = self.alloc_local("i64")

        # FNV-1a offset basis (as signed i64)
        fnv_basis = -3750763034362895579  # 14695981039346656037 as signed
        fnv_prime = 1099511628211

        instructions: list[str] = []
        # Evaluate arg → (ptr, len) on stack
        instructions.extend(arg_instrs)
        instructions.append(f"local.set {slen}")
        instructions.append(f"local.set {ptr}")

        # Initialize hash to FNV offset basis
        instructions.append(f"i64.const {fnv_basis}")
        instructions.append(f"local.set {hash_val}")

        # idx = 0
        instructions.append("i32.const 0")
        instructions.append(f"local.set {idx}")

        # Loop over each byte
        instructions.append("block $hbreak")
        instructions.append("  loop $hloop")
        # if idx >= len → break
        instructions.append(f"    local.get {idx}")
        instructions.append(f"    local.get {slen}")
        instructions.append("    i32.ge_u")
        instructions.append("    br_if $hbreak")
        # byte = mem[ptr + idx]
        instructions.append(f"    local.get {ptr}")
        instructions.append(f"    local.get {idx}")
        instructions.append("    i32.add")
        instructions.append("    i32.load8_u")
        instructions.append("    i64.extend_i32_u")
        # hash = hash XOR byte
        instructions.append(f"    local.get {hash_val}")
        instructions.append("    i64.xor")
        # hash = hash * FNV_prime
        instructions.append(f"    i64.const {fnv_prime}")
        instructions.append("    i64.mul")
        instructions.append(f"    local.set {hash_val}")
        # idx++
        instructions.append(f"    local.get {idx}")
        instructions.append("    i32.const 1")
        instructions.append("    i32.add")
        instructions.append(f"    local.set {idx}")
        instructions.append("    br $hloop")
        instructions.append("  end")
        instructions.append("end")

        # Push result
        instructions.append(f"local.get {hash_val}")
        return instructions

    # -----------------------------------------------------------------
    # Structural show / hash for composite types (#911)
    # -----------------------------------------------------------------
    #
    # `show`/`hash` are registered as universal builtins (§9.8), but codegen
    # historically only handled primitives — every composite `show`/`hash`
    # site tripped `CodegenSkip` and the enclosing function was dropped.
    #
    # These helpers render / fold a composite value INLINE, recursing into
    # each field by its own `show`/`hash`.  Recursion terminates on the
    # value's static type structure; a type that (transitively) contains
    # itself (a recursive ADT like `List<T>`) is detected via `_seen` and
    # cleanly skipped — those need generated helper functions, out of scope
    # for #911 (whose repros are all finite-depth composites).
    #
    # This mirrors the structural-`Eq` traversal in `operators.py`
    # (`_generate_adt_eq_fn` / `_emit_field_eq`): tag at offset 0, fields at
    # concrete offsets recomputed from their concrete WASM types via the same
    # `_concrete_field_layout`, and per-field dispatch by resolved Vera type.

    def _parameterized_arg_type(
        self, arg: ast.Expr, bare: str,
    ) -> str:
        """Recover a show/hash argument's PARAMETERIZED type name.

        `_infer_vera_type` reports the bare head (`"Option"`, `"Array"`);
        the structural traversal needs the type arguments to resolve inner
        field types.  Reuses `_get_arg_type_info_wasm` (the same routine the
        generic-call rewriter and structural-`==` use).  Falls back to the
        bare name when the type arguments cannot be inferred.
        """
        # Array literal: recover the element type directly from its elements
        # (`_get_arg_type_info_wasm` does not special-case a bare `ArrayLit`).
        # Resolve the first element's FULL parameterized type recursively so an
        # array of composites (`[Tuple(1, 2), …]`, `[Some(1), …]`) carries the
        # nested type args rather than a bare `Array<Tuple>` head.
        if isinstance(arg, ast.ArrayLit):
            if arg.elements:
                first = arg.elements[0]
                elem_bare = self._infer_vera_type(first)
                if elem_bare is not None:
                    elem = self._parameterized_arg_type(first, elem_bare)
                    return f"Array<{elem}>"
            elem = self._infer_array_element_type(arg)
            if elem is not None:
                return f"Array<{elem}>"
            return bare

        # SlotRef and FnCall carry a DECLARED type expression that formats
        # nested generics in full (`Option<Tuple<Int, Int>>`), which the flat
        # `_get_arg_type_info_wasm` list cannot (it Nones-out any type arg that
        # is itself parameterized).  Prefer it when present.
        declared = self._declared_type_expr_for_show(arg)
        if declared is not None:
            formatted = self._format_named_type(declared)
            # Only trust it if it is fully ground (no bare type-parameter head).
            if "<" in formatted or formatted == bare:
                return formatted

        # A direct constructor literal's flat `_get_arg_type_info_wasm` result
        # Nones-out (or bare-heads) any type arg that is itself a composite —
        # so inline `Some(Tuple(1, 2))` / `Ok(Some(1))` lose the nested type
        # args.  Recover the FULL parameterized type by resolving each argument
        # recursively.  `Tuple` is variadic (its type args ARE its element
        # types, one per arg); every other constructor maps args to the ADT's
        # type-parameter slots via `_ctor_adt_tp_indices`.
        if isinstance(arg, ast.ConstructorCall):
            recovered = self._recover_ctor_ptype(arg, bare)
            if recovered is not None:
                return recovered

        info = self._get_arg_type_info_wasm(arg)
        if info is None:
            return bare
        base_name, arg_names = info
        if arg_names and all(a is not None for a in arg_names):
            resolved = [a for a in arg_names if a is not None]
            return f"{base_name}<{', '.join(resolved)}>"
        return base_name

    def _recover_ctor_ptype(
        self, arg: ast.ConstructorCall, bare: str,
        _seen: frozenset[str] = frozenset(),
    ) -> str | None:
        """Recover a constructor call's FULL parameterized type, recursively.

        `Tuple(a, b, …)` → ``Tuple<Ta, Tb, …>`` (element types are the args'
        own parameterized types).  Any other constructor maps each argument to
        its ADT type-parameter slot (via ``_ctor_adt_tp_indices``) and resolves
        that slot's argument recursively, so `Some(Tuple(1, 2))` yields
        ``Option<Tuple<Int, Int>>``.

        A slot that no argument pins DIRECTLY (its field is not a bare ``T``)
        is recovered by DESCENDING into a NESTED generic field whose declared
        type carries the parameter (#934): `Grove(Rose<T>, Forest<T>)` has no
        bare-``T`` field, but the field-0 argument `Bloom(1, …)` is a `Rose<T>`
        whose own `Bloom(T, …)` pins `T = Int` from the literal `1` — so
        `Grove(Bloom(1, Empty), Empty)` recovers `Forest<Int>`.  ``_seen``
        bounds the descent (the ADTs are mutually recursive).

        Returns None when the recovery is not fully ground (a slot arg whose
        type can't be inferred), leaving the caller on its existing fallbacks.
        """
        if arg.name == "Tuple":
            elem_types = [
                self._parameterized_arg_type(a, self._infer_vera_type(a) or "")
                for a in arg.args
            ]
            if all(elem_types):
                return f"Tuple<{', '.join(elem_types)}>"
            return None

        adt_name = self._ctor_to_adt_name(arg.name)
        if adt_name is None:
            return None
        tp_count = self._adt_tp_counts.get(adt_name, 0)
        if tp_count == 0:
            return None  # non-generic ADT — bare name already correct
        field_tp_idx = self._ctor_adt_tp_indices.get(arg.name)
        if field_tp_idx is None:
            return None
        slots: list[str | None] = [None] * tp_count
        # Direct pass: a field that IS a bare type parameter pins its slot.
        for field_i, tp_idx in enumerate(field_tp_idx):
            if tp_idx is not None and field_i < len(arg.args):
                a = arg.args[field_i]
                a_bare = self._infer_vera_type(a)
                if a_bare is not None:
                    slots[tp_idx] = self._parameterized_arg_type(a, a_bare)
        # Nested-descent pass (#934): fill any slot the direct pass left None
        # by digging the parameter out of a nested generic field's argument.
        if not all(s is not None for s in slots):
            self._recover_ptype_via_nested_fields(
                arg, adt_name, tp_count, slots, _seen,
            )
        if all(s is not None for s in slots):
            return f"{adt_name}<{', '.join(s for s in slots if s)}>"
        return None

    def _recover_ptype_via_nested_fields(
        self,
        arg: ast.ConstructorCall,
        adt_name: str,
        tp_count: int,
        slots: list[str | None],
        _seen: frozenset[str],
    ) -> None:
        """Fill still-``None`` type-param slots via nested generic fields (#934).

        For each field whose DECLARED type is a generic ADT that places a
        parent type PARAMETER at some position (e.g. `Rose<T>` under
        `Forest<T>`, or the recursive `Forest<T>` itself), recover that field
        ARGUMENT's own parameterized type (`Rose<Int>` / `Forest<Int>`) and
        read the concrete argument sitting where the parent parameter appears —
        pinning that parent slot.  Mutates ``slots`` in place.  Bounded by
        ``_seen`` (the mutually-recursive ADTs) to guarantee termination.
        """
        if adt_name in _seen:
            return
        seen = _seen | {adt_name}
        tp_names = self._adt_tp_param_names.get(adt_name, ())
        # Parent parameter NAME → its slot index (`T` → 0).
        name_to_slot = {name: i for i, name in enumerate(tp_names)}
        layout = self._ctor_layouts.get(arg.name)
        field_types = layout.field_types if layout else ()
        for field_i, decl in enumerate(field_types):
            if field_i >= len(arg.args):
                break
            fbase, fargs = self._split_param_type(decl)
            # Only nested GENERIC ADT fields carry a recoverable parameter.
            if not fargs or fbase not in self._adt_type_names:
                continue
            # Which nested type-arg positions ARE a parent parameter still
            # needing a value?  (`Rose<T>` → position 0 holds `T`.)
            wanted = {
                pos: name_to_slot[fa]
                for pos, fa in enumerate(fargs)
                if fa in name_to_slot and slots[name_to_slot[fa]] is None
            }
            if not wanted:
                continue
            field_arg = arg.args[field_i]
            if not isinstance(field_arg, ast.ConstructorCall):
                continue
            nested_bare = self._infer_vera_type(field_arg)
            recovered = self._recover_ctor_ptype(
                field_arg, nested_bare or fbase, seen,
            )
            if recovered is None:
                continue
            _, rargs = self._split_param_type(recovered)
            for pos, slot in wanted.items():
                if pos < len(rargs):
                    slots[slot] = rargs[pos]

    def _declared_type_expr_for_show(
        self, arg: ast.Expr,
    ) -> ast.NamedType | None:
        """The declared/annotated NamedType of a show/hash argument, if any.

        A ``SlotRef`` carries its bound type (with type args); a non-generic
        user ``FnCall`` carries its declared return TypeExpr (registered by
        ``_register_fn``).  Both format nested generics in full via
        ``_format_named_type``.  Generic calls are excluded — their return
        type is over the callee's own type vars, not concrete types.
        """
        if isinstance(arg, ast.SlotRef):
            return ast.NamedType(name=arg.type_name, type_args=arg.type_args)
        if isinstance(arg, ast.FnCall) and arg.name not in self._generic_fn_info:
            ret_te = self._fn_ret_type_exprs.get(arg.name)
            if isinstance(ret_te, ast.RefinementType):
                ret_te = ret_te.base_type
            if isinstance(ret_te, ast.NamedType):
                return ret_te
        return None

    @staticmethod
    def _ptype_nesting_depth(ptype: str) -> int:
        """Max angle-bracket nesting depth of a parameterized type name (#933).

        ``Int`` → 0, ``List<Int>`` → 1, ``List<List<Int>>`` → 2.  This is the
        structural measure the derived-helper generators bound on: a UNIFORMLY-
        recursive ADT recurs at CONSTANT nesting depth (the `List<T>` tail is
        again `List<T>`, depth 1), whereas a POLYMORPHICALLY-recursive one
        (`Box<T>` field `Box<Box<T>>`) climbs one level per descent without
        limit.  Capping this depth (``DERIVED_HELPER_DEPTH_CAP``) turns that
        runaway into a clean skip while leaving every hand-writable finite
        nesting far below the bound.
        """
        depth = 0
        max_depth = 0
        for c in ptype:
            if c == "<":
                depth += 1
                max_depth = max(max_depth, depth)
            elif c == ">":
                depth -= 1
        return max_depth

    @staticmethod
    def _split_param_type(ptype: str) -> tuple[str, list[str]]:
        """Split ``"Option<Int>"`` → ``("Option", ["Int"])`` (top level only).

        Nested generics in the last argument keep their closing ``>``:
        ``"Result<Int, Option<Int>>"`` → ``("Result", ["Int", "Option<Int>"])``.
        """
        if "<" not in ptype:
            return ptype, []
        base, rest = ptype.split("<", 1)
        # Drop exactly ONE trailing ``>`` (the one matching this ``<``).  A
        # bare `rstrip(">")` strips EVERY trailing ``>``, corrupting a nested
        # generic in the last arg (`Option<Int>>` → `Option<Int`).
        inner = rest[:-1] if rest.endswith(">") else rest
        # Split on top-level commas (nested generics keep their commas).
        args: list[str] = []
        depth = 0
        cur = ""
        for ch in inner:
            if ch == "<":
                depth += 1
                cur += ch
            elif ch == ">":
                depth -= 1
                cur += ch
            elif ch == "," and depth == 0:
                args.append(cur.strip())
                cur = ""
            else:
                cur += ch
        if cur.strip():
            args.append(cur.strip())
        return base.strip(), args

    def _composite_ctor_plans(
        self, ptype: str,
    ) -> list[tuple[str, int, list[tuple[int, str, str]]]] | None:
        """Per-constructor field plan for a composite type.

        Returns ``[(ctor_name, tag, [(offset, wasm_type, field_vera_type)])]``
        sorted by tag, or None when ``ptype`` is not a known composite (its
        head is not in `_adt_type_names`, or it has no registered
        constructors).  Field offsets / WASM types are recomputed from the
        CONCRETE field types (type parameters substituted) exactly as the
        construction site and `$eq_<type>` helper do, so a `String`
        instantiation lays out an i32_pair, not a bare pointer.
        """
        base, type_args = self._split_param_type(ptype)
        if base not in self._adt_type_names:
            return None

        # Tuple is a VARIADIC product with an empty registered layout — its
        # fields come from the instantiation's type args, laid out exactly as
        # the construction site does (`_concrete_field_layout`).  A missing /
        # unparameterized Tuple type (no args recovered) is not showable here.
        if base == "Tuple":
            if not type_args:
                return None
            concrete = self._concrete_field_layout(type_args)
            fields = [
                (offset, wt, ftype)
                for (offset, wt), ftype in zip(concrete, type_args)
            ]
            return [("Tuple", 0, fields)]

        tp_names = self._adt_tp_param_names.get(base, ())
        tp_mapping = dict(zip(tp_names, type_args))

        ctors = sorted(
            (
                (cname, self._ctor_layouts[cname])
                for cname, parent in self._ctor_to_adt.items()
                if parent == base and cname in self._ctor_layouts
            ),
            key=lambda x: x[1].tag,
        )
        if not ctors:
            return None

        plans: list[tuple[str, int, list[tuple[int, str, str]]]] = []
        for cname, layout in ctors:
            n_fields = len(layout.field_offsets)
            tp_idx = self._ctor_adt_tp_indices.get(cname)
            raw_types = (
                layout.field_types
                if layout.field_types
                else ("<opaque>",) * n_fields
            )
            field_type_names = [
                self._resolve_field_type_for_eq(
                    raw, i, tp_idx, type_args, tp_mapping,
                )
                for i, raw in enumerate(raw_types)
            ]
            concrete = self._concrete_field_layout(field_type_names)
            fields = [
                (offset, wt, ftype)
                for (offset, wt), ftype in zip(concrete, field_type_names)
            ]
            plans.append((cname, layout.tag, fields))
        return plans

    def _const_string(self, text: str) -> list[str]:
        """Instructions leaving an interned literal String (ptr, len)."""
        offset, length = self.string_pool.intern(text)
        return [f"i32.const {offset}", f"i32.const {length}"]

    # ---- recursive-ADT helper generation (#924) -----------------------
    #
    # A directly- (or mutually-) recursive ADT cannot be rendered / folded
    # INLINE — the traversal would expand forever at COMPILE time.  #911
    # detected this via the full-ptype `_seen` guard and cleanly skipped
    # (E602), dropping the enclosing function.  #924 upgrades the skip to an
    # actually-emitted, self-calling helper function `$show_<type>` /
    # `$hash_<type>` — one per recursive type — that recurses over the finite
    # VALUE at run time.  This mirrors the structural-`$eq_<type>` machinery
    # (operators.py `_generate_adt_eq_fn` / `_request_adt_eq_helper`).

    def _show_hash_fn_name(self, kind: str, ptype: str) -> str:
        """Mangle ``ptype`` into its ``$show_<type>`` / ``$hash_<type>`` name.

        Uses the shared `mangle_type_name` escape — the same injective
        convention the `$eq_<type>` helpers and mono-clone symbols use, so a
        `List<Int>` helper and a bare ADT literally named `List_LInt_R` cannot
        collide.
        """
        return f"${kind}_{mangle_type_name(ptype)}"

    def _request_show_hash_helper(
        self, kind: str, ptype: str, node: ast.Expr,
    ) -> str | None:
        """Ensure a recursive ``$show``/``$hash`` helper exists; return its name.

        ``kind`` is ``"show"`` or ``"hash"``.  Deduped by name and guarded
        against re-entry via ``_show_hash_pending`` so a self- (or mutually-)
        recursive ADT emits exactly one helper per type.  Returns None when the
        body cannot be generated (an unrenderable / unhashable field), leaving
        the caller to fall back to the clean E602 skip.
        """
        fn_name = self._show_hash_fn_name(kind, ptype)
        if fn_name in self._show_hash_helpers or fn_name in self._show_hash_pending:
            return fn_name
        self._show_hash_pending.add(fn_name)
        body = self._generate_show_hash_helper(kind, fn_name, ptype, node)
        if body is None:
            self._show_hash_pending.discard(fn_name)
            return None
        self._show_hash_helpers[fn_name] = body
        return fn_name

    def _generate_show_hash_helper(
        self, kind: str, fn_name: str, ptype: str, node: ast.Expr,
    ) -> str | None:
        """Generate the full WAT of a recursive ``$show``/``$hash`` helper.

        The helper takes the ADT pointer as ``$p`` (local 0) and returns the
        rendered String ``(result i32 i32)`` (show) or the i64 hash (hash).
        The body reuses the inline `_show_adt` / `_hash_adt` emitters (so there
        is exactly ONE structural-render implementation) run in a FRESH
        local-allocation scope with an EMPTY ``_seen`` — the emitter renders one
        full level and adds ``ptype`` to ``_seen`` before descending, so the
        recursive field (same ``ptype``) routes back through this same helper (a
        ``call $show_<type>`` self-reference) rather than re-expanding inline.
        The emitters allocate into the swapped-in scope, set ``needs_alloc``
        when they build strings, and their shadow-stack rooting is wrapped by a
        GC prologue/epilogue that saves and restores ``$gc_sp`` around the frame.

        Bounded against POLYMORPHIC recursion (#933): a non-uniform ADT
        (`Box<T>` with a `Box<Box<T>>` field) mints a strictly deeper type at
        each descent, so the `_seen` guard never routes back to a self-call and
        this generation recurs unboundedly.  The shared
        ``_derived_helper_depth`` cap catches that runaway and returns None → the
        caller falls back to the clean E602 skip (unchanged from the pre-#924
        behaviour for such types).  Uniform shapes recur on the SAME ptype and
        never reach the cap (measured generation depth 1).
        """
        if self._derived_helper_depth >= self._derived_helper_depth_cap:
            return None
        self._derived_helper_depth += 1
        try:
            return self._generate_show_hash_helper_body(kind, fn_name, ptype, node)
        finally:
            self._derived_helper_depth -= 1

    def _generate_show_hash_helper_body(
        self, kind: str, fn_name: str, ptype: str, node: ast.Expr,
    ) -> str | None:
        """Body of :meth:`_generate_show_hash_helper` (depth-bound wrapper above)."""
        base, _ = self._split_param_type(ptype)

        # Swap in a fresh local-allocation scope so the inline emitters'
        # `alloc_local` calls land in THIS helper's frame, not the caller's.
        # Local 0 is the `$p` parameter; body locals and the GC epilogue's
        # save/return locals are allocated from index 1 up.
        saved_locals = self._locals
        saved_next = self._next_local
        saved_needs_alloc = self.needs_alloc
        self._locals = []
        self._next_local = 1
        self.needs_alloc = False
        body_allocates = False
        try:
            # `_seen` starts EMPTY so `_show_adt` renders ONE full level of the
            # constructor (it adds `ptype` to `seen` before descending into
            # fields).  The recursive field — same `ptype`, now in `seen` — then
            # hits the guard and emits a `call $<kind>_<type>` self-reference
            # back into THIS helper, so the recursion runs over the value at run
            # time rather than expanding inline at compile time.
            value_instrs = ["local.get 0"]
            if kind == "show":
                inner = self._show_adt(base, ptype, value_instrs, node, frozenset())
                result_part = "(result i32 i32)"
            else:
                inner = self._hash_adt(base, ptype, value_instrs, node, frozenset())
                result_part = "(result i64)"
            if inner is None:
                return None
            body_allocates = self.needs_alloc
            gc_prologue, gc_epilogue = self._show_hash_gc_frame(kind)
            local_decls = self.extra_locals_wat()
        finally:
            self._locals = saved_locals
            self._next_local = saved_next
            # A helper that allocates forces the CALLER's frame to carry a GC
            # prologue too (the call site sees the returned pointer as a root).
            self.needs_alloc = saved_needs_alloc or body_allocates

        lines = [f"  (func {fn_name} (param $p i32) {result_part}"]
        lines.extend(f"    {d}" for d in local_decls)
        lines.extend(f"    {i}" for i in gc_prologue)
        lines.extend(f"    {i}" for i in inner)
        lines.extend(f"    {i}" for i in gc_epilogue)
        lines.append("  )")
        return "\n".join(lines)

    def _show_hash_gc_frame(
        self, kind: str,
    ) -> tuple[list[str], list[str]]:
        """Build the GC prologue/epilogue for a recursive show/hash helper.

        ALWAYS emitted — the inline `_show_adt` / `_hash_adt` body
        unconditionally shadow-pushes its struct pointer (`gc_shadow_push`),
        and each recursive `call $<kind>_<type>` re-enters and pushes again, so
        without a per-call ``$gc_sp`` restore a deep recursive value leaks one
        shadow slot per level and overflows the 4 096-slot shadow stack (a
        `hash` over a `List<Int>` allocates nothing yet still leaks the pointer
        push).  The frame saves ``$gc_sp`` on entry, roots the pointer
        parameter (local 0), and restores ``$gc_sp`` on exit — re-rooting the
        returned String pointer for ``show`` so the caller does not sweep it
        before consuming it.  Allocates its save/return locals from the CURRENT
        (swapped-in) scope, so they share the helper's index space with the
        body locals.
        """
        gc_sp_save = self.alloc_local("i32")
        prologue = [
            "global.get $gc_sp",
            f"local.set {gc_sp_save}",
            *gc_shadow_push(0),
        ]
        if kind == "show":
            ret_ptr = self.alloc_local("i32")
            ret_len = self.alloc_local("i32")
            epilogue = [
                f"local.set {ret_len}",
                f"local.set {ret_ptr}",
                f"local.get {gc_sp_save}",
                "global.set $gc_sp",
                *gc_shadow_push(ret_ptr),
                f"local.get {ret_ptr}",
                f"local.get {ret_len}",
            ]
        else:
            ret_i64 = self.alloc_local("i64")
            epilogue = [
                f"local.set {ret_i64}",
                f"local.get {gc_sp_save}",
                "global.set $gc_sp",
                f"local.get {ret_i64}",
            ]
        return prologue, epilogue

    # ---- show ---------------------------------------------------------

    def _show_value(
        self,
        ptype: str,
        value_instrs: list[str],
        node: ast.Expr,
        _seen: frozenset[str] | None = None,
    ) -> list[str] | None:
        """Render a value of parameterized type ``ptype`` to a String.

        ``value_instrs`` leaves the value on the stack in its natural WASM
        shape (i64 for Int/Nat, f64 for Float64, i32 for Bool/Byte/ADT
        pointer, i32_pair for String/Array).  Returns instructions that
        leave the rendered String (ptr, len) on the stack, or None if the
        type is not showable here (recursive ADT, opaque field).
        """
        base, type_args = self._split_param_type(ptype)

        # Primitives — reuse the value-instruction cores factored out for
        # #911.  These behave exactly as the top-level primitive show paths.
        if base == "Int" or base == "Nat":
            return self._to_string_core(value_instrs)
        if base == "Bool":
            return self._bool_to_string_core(value_instrs)
        if base == "Byte":
            return self._byte_to_string_core(value_instrs)
        if base == "Float64":
            return self._float_to_string_core(value_instrs)
        if base == "String":
            return value_instrs  # a String is its own representation
        if base == "Unit":
            # value_instrs leaves nothing useful; drop it and emit "unit".
            return self._const_string("unit")

        if base == "Array":
            elem_type = type_args[0] if type_args else None
            if elem_type is None:
                return None
            return self._show_array(elem_type, value_instrs, node, _seen)

        # ADT / Tuple / Option / Result — heap pointer, tag-dispatched.
        return self._show_adt(base, ptype, value_instrs, node, _seen)

    def _show_adt(
        self,
        base: str,
        ptype: str,
        value_instrs: list[str],
        node: ast.Expr,
        _seen: frozenset[str] | None,
    ) -> list[str] | None:
        seen = _seen or frozenset()
        # Key the recursion guard on the FULL parameterized type, not the bare
        # head: `Option<Option<Int>>` nests `Option<Int>` — a DIFFERENT type,
        # finite depth — and must render INLINE, whereas a directly-recursive
        # ADT (`List<Int>` whose `Cons` field is again `List<Int>`) recurs on
        # the SAME parameterized type.  #911 collapsed the recursive case to a
        # clean skip; #924 routes it to a GENERATED self-calling helper
        # (`call $show_<type>`) so the finite value renders at run time.
        if ptype in seen:
            fn_name = self._request_show_hash_helper("show", ptype, node)
            if fn_name is None:
                return None
            return value_instrs + [f"call {fn_name}"]
        # #933: bound POLYMORPHIC recursion.  A non-uniform ADT (`Box<T>` field
        # `Box<Box<T>>`) never repeats a `ptype`, so the same-type guard above
        # never routes to a self-call: each descent renders INLINE on a
        # strictly-deeper, DISTINCT type whose generic NESTING climbs one level
        # per step without limit, until the walk (and `_parse_type_name` on the
        # ever-deeper type name) blows the Python stack on a check-green program.
        # Past the cap, return None → the enclosing `show` falls back to the
        # clean E602 skip (the same degradation an unrenderable field already
        # gets).  Uniform shapes recur at CONSTANT nesting depth and never
        # approach the cap.
        if self._ptype_nesting_depth(ptype) >= self._derived_helper_depth_cap:
            return None
        seen = seen | {ptype}

        plans = self._composite_ctor_plans(ptype)
        if plans is None:
            return None

        ptr = self.alloc_local("i32")
        acc_ptr = self.alloc_local("i32")
        acc_len = self.alloc_local("i32")
        result_ptr = self.alloc_local("i32")
        result_len = self.alloc_local("i32")

        instrs: list[str] = []
        instrs.extend(value_instrs)
        instrs.append(f"local.set {ptr}")
        instrs.extend(gc_shadow_push(ptr))
        # One shadow slot roots the running accumulator across the per-field
        # concat allocations (seeded with the struct pointer, overwritten with
        # the accumulator on first re-root).
        root_slot = self._reserve_root_slot(instrs, ptr)

        is_tuple = base == "Tuple"

        # Build a nested if/else on the tag.  Each branch renders one
        # constructor's String into (result_ptr, result_len).
        def render_ctor(cname: str, fields: list[tuple[int, str, str]]) -> None:
            # Head: `Ctor(` (or `(` for a Tuple; bare `Ctor` for nullary).
            if is_tuple:
                head = "("
            elif fields:
                head = f"{cname}("
            else:
                head = cname
            piece = self._const_string(head)
            instrs.extend(f"  {i}" for i in piece)
            instrs.append(f"  local.set {acc_len}")
            instrs.append(f"  local.set {acc_ptr}")
            self._reroot(instrs, root_slot, acc_ptr, indent="  ")
            for fi, (offset, wt, ftype) in enumerate(fields):
                if fi > 0:
                    self._concat_into(instrs, acc_ptr, acc_len,
                                      self._const_string(", "), indent="  ",
                                      root_slot=root_slot)
                load = self._load_field(ptr, offset, wt)
                rendered = self._show_value(ftype, load, node, seen)
                if rendered is None:
                    # Unrenderable field — abandon this whole show.
                    raise _ShowHashUnsupported
                self._concat_into(instrs, acc_ptr, acc_len,
                                  rendered, indent="  ", root_slot=root_slot)
            if fields:
                self._concat_into(instrs, acc_ptr, acc_len,
                                  self._const_string(")"), indent="  ",
                                  root_slot=root_slot)
            instrs.append(f"  local.get {acc_ptr}")
            instrs.append(f"  local.set {result_ptr}")
            instrs.append(f"  local.get {acc_len}")
            instrs.append(f"  local.set {result_len}")

        try:
            # tag = mem[ptr]
            n = len(plans)
            for depth, (cname, tag, fields) in enumerate(plans):
                if depth < n - 1:
                    instrs.append(f"local.get {ptr}")
                    instrs.append("i32.load")
                    instrs.append(f"i32.const {tag}")
                    instrs.append("i32.eq")
                    instrs.append("if")
                    render_ctor(cname, fields)
                    instrs.append("else")
                else:
                    # Last constructor: the fall-through else.
                    render_ctor(cname, fields)
            for _ in range(n - 1):
                instrs.append("end")
        except _ShowHashUnsupported:
            return None

        instrs.append(f"local.get {result_ptr}")
        instrs.append(f"local.get {result_len}")
        return instrs

    def _show_array(
        self,
        elem_type: str,
        value_instrs: list[str],
        node: ast.Expr,
        _seen: frozenset[str] | None,
    ) -> list[str] | None:
        # Render a probe element to confirm the element type is showable and
        # to reuse its instruction shape inside the loop body.
        arr_ptr = self.alloc_local("i32")
        arr_len = self.alloc_local("i32")
        idx = self.alloc_local("i32")
        acc_ptr = self.alloc_local("i32")
        acc_len = self.alloc_local("i32")
        sp_save = self.alloc_local("i32")

        elem_size = _element_mem_size(elem_type)
        if elem_size is None:
            return None

        # Element load: address = arr_ptr + idx*elem_size, then load per type.
        elem_load = self._load_array_element(arr_ptr, idx, elem_type, elem_size)
        if elem_load is None:
            return None
        elem_rendered = self._show_value(elem_type, elem_load, node, _seen)
        if elem_rendered is None:
            return None

        instrs: list[str] = []
        instrs.extend(value_instrs)  # (ptr, len)
        instrs.append(f"local.set {arr_len}")
        instrs.append(f"local.set {arr_ptr}")
        instrs.extend(gc_shadow_push(arr_ptr))

        # acc = "["
        opening = self._const_string("[")
        instrs.extend(opening)
        instrs.append(f"local.set {acc_len}")
        instrs.append(f"local.set {acc_ptr}")
        # Root the accumulator across the per-element concat allocations.
        root_slot = self._reserve_root_slot(instrs, acc_ptr)

        # idx = 0
        instrs.append("i32.const 0")
        instrs.append(f"local.set {idx}")
        instrs.append("block $show_arr_brk")
        instrs.append("  loop $show_arr_lp")
        instrs.append(f"    local.get {idx}")
        instrs.append(f"    local.get {arr_len}")
        instrs.append("    i32.ge_u")
        instrs.append("    br_if $show_arr_brk")
        # Snapshot $gc_sp at the top of the body.  Every string built this
        # iteration (the separator, the element render, the concat results)
        # shadow-pushes its buffer with NO matching pop — those slots unwind
        # only at function exit, so in this loop they leak one-plus per element
        # and overflow the 4 096-slot shadow stack on large arrays.  Restoring
        # $gc_sp to the snapshot at the end of the body reclaims them all; the
        # accumulator is separately rooted in `root_slot` (reserved BELOW the
        # snapshot), so the restore never orphans the live result.
        instrs.append("    global.get $gc_sp")
        instrs.append(f"    local.set {sp_save}")
        # separator ", " for idx > 0
        instrs.append(f"    local.get {idx}")
        instrs.append("    i32.const 0")
        instrs.append("    i32.gt_u")
        instrs.append("    if")
        self._concat_into(instrs, acc_ptr, acc_len,
                          self._const_string(", "), indent="      ",
                          root_slot=root_slot)
        instrs.append("    end")
        # render element
        self._concat_into(instrs, acc_ptr, acc_len,
                          elem_rendered, indent="    ", root_slot=root_slot)
        # Unwind this iteration's shadow slots (accumulator stays in root_slot).
        instrs.append(f"    local.get {sp_save}")
        instrs.append("    global.set $gc_sp")
        # idx++
        instrs.append(f"    local.get {idx}")
        instrs.append("    i32.const 1")
        instrs.append("    i32.add")
        instrs.append(f"    local.set {idx}")
        instrs.append("    br $show_arr_lp")
        instrs.append("  end")
        instrs.append("end")
        # acc = acc ++ "]"
        self._concat_into(instrs, acc_ptr, acc_len,
                          self._const_string("]"), indent="",
                          root_slot=root_slot)

        instrs.append(f"local.get {acc_ptr}")
        instrs.append(f"local.get {acc_len}")
        return instrs

    def _reserve_root_slot(
        self, instrs: list[str], init_ptr: int, indent: str = "",
    ) -> int:
        """Reserve one shadow-stack slot for a loop accumulator; return the
        local holding its address.

        A loop accumulator (`_show_adt` / `_show_array`) lives in a plain
        local across many per-concat `$alloc`s — between iterations it is
        neither on the operand stack nor a GC root, so a collection would
        sweep it.  This pushes ONE slot (via the standard `gc_shadow_push`,
        seeded with the initial accumulator ``init_ptr``) and captures its
        address so the caller re-stores the current accumulator into that
        FIXED slot after each concat (`_reroot`) — exactly one live root
        regardless of loop length (unlike per-iteration pushes, which would
        exhaust the shadow stack).  The slot unwinds at function exit with
        the rest of the frame's shadow region — the same lifetime the
        existing `gc_shadow_push` roots already have.
        """
        slot_addr = self.alloc_local("i32")
        # Capture the slot address (current $gc_sp) BEFORE the push advances it.
        instrs.append(f"{indent}global.get $gc_sp")
        instrs.append(f"{indent}local.set {slot_addr}")
        instrs.extend(indent + i for i in gc_shadow_push(init_ptr))
        return slot_addr

    def _reroot(
        self, instrs: list[str], slot_addr: int, ptr_local: int, indent: str,
    ) -> None:
        """Store ``ptr_local`` into the reserved shadow slot ``slot_addr``."""
        instrs.append(f"{indent}local.get {slot_addr}")
        instrs.append(f"{indent}local.get {ptr_local}")
        instrs.append(f"{indent}i32.store")

    def _concat_into(
        self,
        instrs: list[str],
        acc_ptr: int,
        acc_len: int,
        piece_instrs: list[str],
        indent: str,
        root_slot: int | None = None,
    ) -> None:
        """Append ``acc = concat(acc, piece)`` to ``instrs``, in place.

        ``acc_ptr`` / ``acc_len`` hold the running String; ``piece_instrs``
        leaves the piece (ptr, len) on the stack.  Rebinds the accumulator
        locals to the freshly allocated concatenation, then (when
        ``root_slot`` is given) re-roots the new accumulator into that fixed
        shadow slot so it survives the NEXT concat's allocation.
        """
        concat = self._string_concat_core(
            [f"local.get {acc_ptr}", f"local.get {acc_len}"],
            piece_instrs,
        )
        instrs.extend(indent + i for i in concat)
        instrs.append(f"{indent}local.set {acc_len}")
        instrs.append(f"{indent}local.set {acc_ptr}")
        if root_slot is not None:
            self._reroot(instrs, root_slot, acc_ptr, indent)

    def _load_field(
        self, ptr_local: int, offset: int, wt: str,
    ) -> list[str]:
        """Instructions leaving field at ``offset`` on the stack (by WASM type)."""
        if wt == "i64":
            return [f"local.get {ptr_local}", f"i64.load offset={offset}"]
        if wt == "f64":
            return [f"local.get {ptr_local}", f"f64.load offset={offset}"]
        if wt == "i32_pair":
            return [
                f"local.get {ptr_local}", f"i32.load offset={offset}",
                f"local.get {ptr_local}", f"i32.load offset={offset + 4}",
            ]
        # i32 (Bool/Byte/Unit/ADT pointer)
        return [f"local.get {ptr_local}", f"i32.load offset={offset}"]

    def _load_array_element(
        self, arr_ptr: int, idx: int, elem_type: str, elem_size: int,
    ) -> list[str] | None:
        """Instructions leaving arr[idx] on the stack (natural WASM shape)."""
        is_pair = _is_pair_element_type(elem_type)
        load_op = _element_load_op(elem_type)
        if load_op is None and not is_pair:
            return None
        addr: list[str] = [f"local.get {arr_ptr}", f"local.get {idx}"]
        if elem_size == 1:
            addr.append("i32.add")
        else:
            addr.append(f"i32.const {elem_size}")
            addr.append("i32.mul")
            addr.append("i32.add")
        if is_pair:
            # addr on stack → duplicate via a temp local to load (ptr, len).
            tmp = self.alloc_local("i32")
            return addr + [
                f"local.set {tmp}",
                f"local.get {tmp}", "i32.load offset=0",
                f"local.get {tmp}", "i32.load offset=4",
            ]
        return addr + [load_op]  # type: ignore[list-item]

    # ---- hash ---------------------------------------------------------

    # 64-bit FNV constants, shared with the String hash above.
    _FNV_BASIS = -3750763034362895579  # 14695981039346656037 as signed i64
    _FNV_PRIME = 1099511628211

    def _hash_value(
        self,
        ptype: str,
        value_instrs: list[str],
        node: ast.Expr,
        _seen: frozenset[str] | None = None,
    ) -> list[str] | None:
        """Fold a value of type ``ptype`` into an i64 hash.

        Deterministic: primitives hash as their top-level `hash` does;
        composites seed with the constructor tag and mix each field's hash
        (FNV-style).  Returns None for unhashable / recursive types.
        """
        base, type_args = self._split_param_type(ptype)

        if base in ("Int", "Nat"):
            return value_instrs
        if base in ("Bool", "Byte"):
            return value_instrs + ["i64.extend_i32_u"]
        if base == "Float64":
            return value_instrs + ["i64.reinterpret_f64"]
        if base == "Unit":
            return ["i64.const 0"]
        if base == "String":
            return self._translate_hash_string(value_instrs)
        if base == "Array":
            elem_type = type_args[0] if type_args else None
            if elem_type is None:
                return None
            return self._hash_array(elem_type, value_instrs, node, _seen)
        return self._hash_adt(base, ptype, value_instrs, node, _seen)

    def _mix_hash(self, acc: int, field_hash: list[str]) -> list[str]:
        """``acc = (acc XOR field_hash) * FNV_PRIME`` — one fold step."""
        return [
            f"local.get {acc}",
            *field_hash,
            "i64.xor",
            f"i64.const {self._FNV_PRIME}",
            "i64.mul",
            f"local.set {acc}",
        ]

    def _hash_adt(
        self,
        base: str,
        ptype: str,
        value_instrs: list[str],
        node: ast.Expr,
        _seen: frozenset[str] | None,
    ) -> list[str] | None:
        seen = _seen or frozenset()
        # Full-ptype recursion guard (see `_show_adt`): distinguishes finite
        # same-base nesting (`Option<Option<Int>>`) from genuine self-reference
        # (`List<Int>`).  The former folds inline; the latter routes to a
        # generated self-calling helper (`call $hash_<type>`) that folds the
        # finite value at run time (#924).
        if ptype in seen:
            fn_name = self._request_show_hash_helper("hash", ptype, node)
            if fn_name is None:
                return None
            return value_instrs + [f"call {fn_name}"]
        # #933: bound POLYMORPHIC recursion (see `_show_adt`).  A non-uniform
        # ADT grows a strictly-deeper, DISTINCT `ptype` (one more nesting level)
        # at each inline descent, so the same-type guard above never fires and
        # the fold recurs unboundedly.  Past the cap, return None → the
        # enclosing `hash` falls back to the clean E602 skip.  Uniform shapes
        # recur at constant nesting depth and never approach the cap.
        if self._ptype_nesting_depth(ptype) >= self._derived_helper_depth_cap:
            return None
        seen = seen | {ptype}

        plans = self._composite_ctor_plans(ptype)
        if plans is None:
            return None

        ptr = self.alloc_local("i32")
        acc = self.alloc_local("i64")

        instrs: list[str] = []
        instrs.extend(value_instrs)
        instrs.append(f"local.set {ptr}")
        instrs.extend(gc_shadow_push(ptr))
        # Seed with the FNV basis, then mix the tag (distinguishes
        # constructors) and each field's hash.
        instrs.append(f"i64.const {self._FNV_BASIS}")
        instrs.append(f"local.set {acc}")
        instrs.extend(self._mix_hash(
            acc, [f"local.get {ptr}", "i32.load", "i64.extend_i32_u"]))

        def mix_ctor(fields: list[tuple[int, str, str]]) -> None:
            for offset, wt, ftype in fields:
                load = self._load_field(ptr, offset, wt)
                fh = self._hash_value(ftype, load, node, seen)
                if fh is None:
                    raise _ShowHashUnsupported
                fh_local = self.alloc_local("i64")
                instrs.extend(f"  {i}" for i in fh)
                instrs.append(f"  local.set {fh_local}")
                mix = self._mix_hash(acc, [f"local.get {fh_local}"])
                instrs.extend(f"  {i}" for i in mix)

        try:
            n = len(plans)
            for depth, (_cname, tag, fields) in enumerate(plans):
                if depth < n - 1:
                    instrs.append(f"local.get {ptr}")
                    instrs.append("i32.load")
                    instrs.append(f"i32.const {tag}")
                    instrs.append("i32.eq")
                    instrs.append("if")
                    mix_ctor(fields)
                    instrs.append("else")
                else:
                    mix_ctor(fields)
            for _ in range(n - 1):
                instrs.append("end")
        except _ShowHashUnsupported:
            return None

        instrs.append(f"local.get {acc}")
        return instrs

    def _hash_array(
        self,
        elem_type: str,
        value_instrs: list[str],
        node: ast.Expr,
        _seen: frozenset[str] | None,
    ) -> list[str] | None:
        arr_ptr = self.alloc_local("i32")
        arr_len = self.alloc_local("i32")
        idx = self.alloc_local("i32")
        acc = self.alloc_local("i64")
        sp_save = self.alloc_local("i32")

        elem_size = _element_mem_size(elem_type)
        if elem_size is None:
            return None
        elem_load = self._load_array_element(arr_ptr, idx, elem_type, elem_size)
        if elem_load is None:
            return None
        elem_hash = self._hash_value(elem_type, elem_load, node, _seen)
        if elem_hash is None:
            return None

        instrs: list[str] = []
        instrs.extend(value_instrs)  # (ptr, len)
        instrs.append(f"local.set {arr_len}")
        instrs.append(f"local.set {arr_ptr}")
        instrs.extend(gc_shadow_push(arr_ptr))
        # Seed with basis, mix the length, then each element hash.
        instrs.append(f"i64.const {self._FNV_BASIS}")
        instrs.append(f"local.set {acc}")
        instrs.extend(self._mix_hash(
            acc, [f"local.get {arr_len}", "i64.extend_i32_u"]))

        instrs.append("i32.const 0")
        instrs.append(f"local.set {idx}")
        instrs.append("block $hash_arr_brk")
        instrs.append("  loop $hash_arr_lp")
        instrs.append(f"    local.get {idx}")
        instrs.append(f"    local.get {arr_len}")
        instrs.append("    i32.ge_u")
        instrs.append("    br_if $hash_arr_brk")
        # A COMPOSITE element's hash shadow-pushes its struct pointer with no
        # matching pop; snapshot/restore $gc_sp around the element hash to
        # unwind those per-iteration slots (the i64 accumulator is a value, not
        # a heap root, so nothing here needs rooting).
        instrs.append("    global.get $gc_sp")
        instrs.append(f"    local.set {sp_save}")
        eh_local = self.alloc_local("i64")
        instrs.extend(f"    {i}" for i in elem_hash)
        instrs.append(f"    local.set {eh_local}")
        mix = self._mix_hash(acc, [f"local.get {eh_local}"])
        instrs.extend(f"    {i}" for i in mix)
        instrs.append(f"    local.get {sp_save}")
        instrs.append("    global.set $gc_sp")
        instrs.append(f"    local.get {idx}")
        instrs.append("    i32.const 1")
        instrs.append("    i32.add")
        instrs.append(f"    local.set {idx}")
        instrs.append("    br $hash_arr_lp")
        instrs.append("  end")
        instrs.append("end")

        instrs.append(f"local.get {acc}")
        return instrs

    # -----------------------------------------------------------------
    # Effect handlers: State<T> and Exn<E>
    # -----------------------------------------------------------------

    def _translate_handle_expr(
        self, expr: ast.HandleExpr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate a handle expression to WASM.

        Supports State<T> handlers via host imports and Exn<E>
        handlers via WASM exception handling (try_table/catch/throw).
        Other handler types cause the function to be skipped.
        """
        effect = expr.effect
        if not isinstance(effect, ast.EffectRef):
            raise CodegenSkip(
                expr, "handle expression effect must be an EffectRef"
            )

        if effect.name == "State" and effect.type_args and len(effect.type_args) == 1:
            return self._translate_handle_state(expr, env)

        if effect.name == "Exn" and effect.type_args and len(effect.type_args) == 1:
            return self._translate_handle_exn(expr, env)

        # Unsupported handler type
        raise CodegenSkip(
            expr,
            f"only State<T> and Exn<E> handlers supported (got {effect.name})",
        )

    def _translate_handle_state(
        self, expr: ast.HandleExpr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate handle[State<T>](@T = init) { ... } in { body }.

        Compiles by:
        1. Evaluating init_expr and calling state_put_T to set initial state
        2. Temporarily injecting get/put effect ops for the body
        3. Compiling the body with these ops active
        4. Restoring the previous effect ops
        """
        assert isinstance(expr.effect, ast.EffectRef)  # noqa: S101
        type_arg = expr.effect.type_args[0]  # type: ignore[index]
        if not isinstance(type_arg, ast.NamedType):
            raise CodegenSkip(
                expr, "State<T> type argument must be a named type"
            )
        # #914: use the FULL canonical slot name (`Tuple<Int, Int>`, not the
        # base `Tuple`) so the handler-body get/put/push/pop calls match the
        # `(import …)` decls emitted from `_state_types` (also full names) —
        # pre-fix the two diverged for composite T (`state_push_Option` vs
        # `state_push_Option<Int>`).  Then route through the injective
        # `mangle_type_name` (#775) so the WAT identifier is legal.
        type_name = self._type_expr_to_slot_name(type_arg)
        if type_name is None:  # pragma: no cover — NamedType always resolves
            raise CodegenSkip(
                expr, "State<T> type argument has no slot name"
            )
        mangled = mangle_type_name(type_name)

        put_import = f"$vera.state_put_{mangled}"
        get_import = f"$vera.state_get_{mangled}"
        push_import = f"$vera.state_push_{mangled}"
        pop_import = f"$vera.state_pop_{mangled}"

        instructions: list[str] = []

        # 1. Push a fresh state cell (isolates this handler from any outer
        #    handler of the same type — fixes #417).
        instructions.append(f"call {push_import}")

        # 2. Initialize state: compile init_expr, call state_put
        if expr.state is not None:
            init_instrs = self.translate_expr(expr.state.init_expr, env)
            if init_instrs is None:
                return None
            instructions.extend(init_instrs)
            instructions.append(f"call {put_import}")
        # If no state clause, state starts at default (0)

        # 3. Save current effect_ops and inject handler ops.  Record `get`'s
        #    result WAT type (#914 A2: a `match get(())` inside the body needs
        #    it to type the scrutinee — State<T>'s T is validated non-pair by
        #    the checker, so `_type_name_to_wasm` yields the op's result WT).
        saved_ops = dict(self._effect_ops)
        saved_result_wt = dict(self._effect_op_result_wt)
        saved_clause_ops = dict(self._state_clause_ops)
        self._effect_ops["get"] = (get_import, False)
        self._effect_ops["put"] = (put_import, True)
        self._effect_op_result_wt["get"] = self._type_name_to_wasm(type_name)
        # #976 option C: register the clauses so each get/put CALL SITE in
        # the body inlines its clause body (intrinsic-hybrid semantics)
        # instead of the bare host-cell call.  An op with no clause keeps the
        # bare path via the `_effect_ops` entry above.
        for clause in expr.clauses:
            self._state_clause_ops[clause.op_name] = (
                clause, type_name, get_import, put_import,
            )

        # 4. Compile handler body
        body_instrs = self.translate_block(expr.body, env)

        # 5. Restore effect_ops (and the clause registry — nested handlers)
        self._effect_ops = saved_ops
        self._effect_op_result_wt = saved_result_wt
        self._state_clause_ops = saved_clause_ops

        if body_instrs is None:
            return None

        instructions.extend(body_instrs)

        # 6. Pop the state cell (restores outer handler's value).
        # pop is stack-neutral so the body's return value is already on the
        # WASM value stack and is unaffected.
        instructions.append(f"call {pop_import}")

        return instructions

    def _translate_state_clause_op(
        self, call: ast.FnCall, env: WasmSlotEnv,
    ) -> list[str] | None:
        """Inline a ``handle[State<T>]`` clause at a get/put call site (#976).

        The pinned intrinsic-hybrid semantics:

        1. ``put(x)`` stores ``x`` intrinsically; ``get`` reads intrinsically.
        2. The clause body EXECUTES; its ``resume(v)`` value IS the op's
           result at this call site (single-shot, tail position — enforced
           below).
        3. ``with @T = <expr>`` OVERRIDES the intrinsic store.
        4. The clause's ``@T.0`` is captured BEFORE the intrinsic store, so
           ``with @T = @T.0`` means *keep the old state*.

        Emission per site (all over the existing host-cell imports — no host
        changes): eval put's argument to a local; ``call get`` into a capture
        local (the clause's ``@T.0``); for put, ``call put`` with the
        argument (intrinsic store); inline the clause body with the op param
        bound FIRST and the captured state LAST (checker binding order:
        ``@T.0`` = state, ``@T.1`` = put's argument); then, if the clause
        carries ``with``, eval the override in the same scope and ``call
        put``.  Stack discipline: the body's net effect is exactly resume's
        value (``[]`` for put — ``resume(())`` is a ``UnitLit``; one ``T``
        for get), and the override's value is consumed by its own put, so
        the site's net stack effect equals the bare host-call it replaces.

        A get clause's ``@Unit`` op param carries no value and gets no env
        binding — a body referencing it fails slot resolution loudly rather
        than resolving to something wrong.
        """
        clause, type_name, get_import, put_import = (
            self._state_clause_ops[call.name]
        )
        total, tail = self._clause_resume_counts(clause.body)
        if total == 0 or total != tail:
            raise CodegenSkip(
                call,
                "State clause requires resume(...) in tail position "
                "(single-shot); a missing, repeated, or non-tail resume "
                "is not lowerable",
            )
        state_wt = self._type_name_to_wasm(type_name)
        instructions: list[str] = []

        # put's argument — the clause's @T.1 (op params bind first).
        arg_local: int | None = None
        if call.name == "put":
            arg_instrs = self.translate_expr(call.args[0], env)
            if arg_instrs is None:
                return None
            arg_local = self.alloc_local(state_wt)
            instructions.extend(arg_instrs)
            instructions.append(f"local.set {arg_local}")

        # Capture the PRE-store state — the clause's @T.0 (bound last).
        state_local = self.alloc_local(state_wt)
        instructions.append(f"call {get_import}")
        instructions.append(f"local.set {state_local}")

        # Intrinsic store: put stores its argument regardless of the clause.
        if call.name == "put":
            instructions.append(f"local.get {arg_local}")
            instructions.append(f"call {put_import}")

        clause_env = env
        if arg_local is not None:
            clause_env = clause_env.push(type_name, arg_local)
        clause_env = clause_env.push(type_name, state_local)

        saved_in_clause = self._in_state_clause
        self._in_state_clause = True
        try:
            body_instrs = self.translate_expr(clause.body, clause_env)
            upd_instrs = (
                self.translate_expr(clause.state_update[1], clause_env)
                if clause.state_update is not None else None
            )
        finally:
            self._in_state_clause = saved_in_clause
        if body_instrs is None:
            return None
        instructions.extend(body_instrs)
        if clause.state_update is not None:
            if upd_instrs is None:
                return None
            instructions.extend(upd_instrs)
            instructions.append(f"call {put_import}")
        return instructions

    def _clause_resume_counts(self, body: ast.Expr) -> tuple[int, int]:
        """(total, tail-position) ``resume(...)`` call counts in a clause
        body.

        Tail positions: the body itself, a Block's trailing expression, and
        both/all arms of a tail ``if``/``match``.  Anything else (a resume in
        a statement, an operand, a nested handler's body, …) is non-tail:
        the inline lowering's stack shape requires every execution path to
        end in exactly one resume, so ``total == tail`` (and ``total >= 1``)
        is the lowerable condition.
        """
        def total_count(node: object) -> int:
            if isinstance(node, ast.FnCall) and node.name == "resume":
                # resume's own arguments cannot contain another resume in a
                # checkable program (resume returns Unit); count args anyway
                # so a pathological nesting is rejected, not miscounted.
                return 1 + sum(total_count(a) for a in node.args)
            if isinstance(node, (list, tuple)):
                return sum(total_count(item) for item in node)
            if is_dataclass(node) and not isinstance(node, type):
                return sum(
                    total_count(getattr(node, f.name))
                    for f in fields(node)
                )
            return 0

        def tail_count(expr: object) -> int:
            if isinstance(expr, ast.FnCall) and expr.name == "resume":
                return 1
            if isinstance(expr, ast.Block):
                return tail_count(expr.expr)
            if isinstance(expr, ast.IfExpr):
                return tail_count(expr.then_branch) + tail_count(
                    expr.else_branch)
            if isinstance(expr, ast.MatchExpr):
                return sum(tail_count(arm.body) for arm in expr.arms)
            return 0

        return total_count(body), tail_count(body)

    def _translate_handle_exn(
        self, expr: ast.HandleExpr, env: WasmSlotEnv,
    ) -> list[str] | None:
        """Translate handle[Exn<E>] { throw(@E) -> handler } in { body }.

        Uses WASM exception handling (try_table/catch/throw):
          block $done (result T)
            block $catch (result E)
              try_table (result T) (catch $exn_E $catch)
                <body>
              end
              br $done
            end
            ;; caught value on stack
            local.set $thrown
            <handler clause body>
          end
        """
        assert isinstance(expr.effect, ast.EffectRef)  # noqa: S101
        type_arg = expr.effect.type_args[0]  # type: ignore[index]
        if not isinstance(type_arg, ast.NamedType):
            raise CodegenSkip(
                expr, "Exn<E> type argument must be a named type"
            )
        # #914: use the FULL canonical slot name (`Option<Int>`, not `Option`)
        # so the caught-payload slot env binds under the same key a
        # `@Option<Int>.n` ref in the handler body resolves against (root
        # cause C — pre-fix the push used the base name and the ref dangled,
        # E699).  The tag identifier is escaped via `mangle_type_name` (#775)
        # so a composite E yields a legal WAT tag name (root cause B3).
        type_name = self._type_expr_to_slot_name(type_arg)
        if type_name is None:  # pragma: no cover — NamedType always resolves
            raise CodegenSkip(
                expr, "Exn<E> type argument has no slot name"
            )
        tag_name = f"$exn_{mangle_type_name(type_name)}"
        is_pair = self._is_pair_type_name(type_name)

        # Unique label ids for nested handlers
        hid = self._next_handle_id
        self._next_handle_id += 1
        done_label = f"$hd_{hid}"
        catch_label = f"$hc_{hid}"

        # Infer result type: try handler clause first (body may always
        # throw, making its inferred type None), then fall back to body.
        # Use `_infer_expr_wasm_type` rather than `_infer_block_result_type`
        # so expression-bodied handler clauses (e.g. `throw(@String) -> None`,
        # `throw(@Int) -> @Int.0 + 1`, etc.) are inferred correctly — pre-fix
        # only `ast.Block` clause bodies got their result type inferred,
        # leaving `result_wt = None` for any expression-bodied handler and
        # omitting the `(result ...)` annotation in emitted WAT.  #475 (1).
        # `expr.body` is statically typed `Block` (ast.py:481), so passing
        # it to `_infer_expr_wasm_type` produces the same answer as the
        # Block-specific helper would — using one helper for both call
        # sites is uniformity for free.
        result_wt = None
        if expr.clauses:
            result_wt = self._infer_expr_wasm_type(expr.clauses[0].body)
        if result_wt is None:
            result_wt = self._infer_expr_wasm_type(expr.body)

        # Save/inject throw as an effect op for the body
        saved_ops = dict(self._effect_ops)
        self._effect_ops["throw"] = (tag_name, False)

        # Compile body
        body_instrs = self.translate_block(expr.body, env)

        # Restore effect_ops
        self._effect_ops = saved_ops

        if body_instrs is None:
            return None

        # Compile handler clause body
        if not expr.clauses:
            raise CodegenSkip(
                expr, "handle[Exn<E>] requires at least one clause"
            )
        clause = expr.clauses[0]  # Exn<E> has exactly one op: throw

        # Allocate locals for the caught exception value.
        # Pair types (String, Array<T>) use two consecutive i32 locals
        # (ptr at thrown_local, len at thrown_local + 1) matching the
        # convention used by _translate_slot_ref for pair types.
        if is_pair:
            thrown_local = self.alloc_local("i32")  # ptr
            _len_local = self.alloc_local("i32")    # len (consecutive: thrown_local + 1)
        else:
            thrown_wt = self._type_name_to_wasm(type_name)
            thrown_local = self.alloc_local(thrown_wt)

        # Push caught value into slot env for handler body
        handler_env = env.push(type_name, thrown_local)
        handler_instrs = self.translate_expr(clause.body, handler_env)
        if handler_instrs is None:
            return None  # pragma: no cover

        # Assemble the try_table structure.
        # i32_pair (String, Array<T>) must expand to "i32 i32" in WAT result
        # annotations; "i32_pair" is an internal representation, not valid WAT.
        if result_wt == "i32_pair":
            result_spec = " (result i32 i32)"
        elif result_wt:
            result_spec = f" (result {result_wt})"
        else:
            result_spec = ""  # pragma: no cover
        if is_pair:
            thrown_spec = " (result i32 i32)"
        else:
            thrown_spec = f" (result {thrown_wt})" if thrown_wt else ""

        instructions: list[str] = []
        instructions.append(f"block {done_label}{result_spec}")
        instructions.append(f"  block {catch_label}{thrown_spec}")
        instructions.append(
            f"    try_table{result_spec}"
            f" (catch {tag_name} {catch_label})"
        )
        instructions.extend(f"      {i}" for i in body_instrs)
        instructions.append("    end")
        instructions.append(f"    br {done_label}")
        instructions.append("  end")
        # Caught value(s) are on the stack — store into local(s).
        # Pair types: catch pushes (ptr, len); set len first (LIFO), then ptr.
        if is_pair:
            instructions.append(f"  local.set {_len_local}")
            instructions.append(f"  local.set {thrown_local}")
        else:
            instructions.append(f"  local.set {thrown_local}")
        instructions.extend(f"  {i}" for i in handler_instrs)
        instructions.append("end")

        return instructions
