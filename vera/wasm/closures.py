"""Closure and anonymous function translation mixin for WasmContext."""

from __future__ import annotations

from vera import ast
from vera.wasm.helpers import WasmSlotEnv, _align_up, gc_shadow_push


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
        param_type_counts: dict[str, int] = {}
        for p in expr.params:
            pname = self._type_expr_name(p)
            if pname:
                param_type_counts[pname] = param_type_counts.get(pname, 0) + 1

        captures = self._collect_free_vars(expr.body, param_type_counts)

        # Assign closure ID and register for later lifting
        closure_id = self._next_closure_id
        self._next_closure_id += 1
        self._pending_closures.append((expr, captures, closure_id))

        # Compute closure struct layout
        # offset 0: func_table_idx (i32, 4 bytes)
        # Pair-type captures (#535) take 8 bytes: ptr + len, two
        # consecutive i32 fields, 4-byte aligned.  The matching layout
        # in `_compile_lifted_closure` reads them back as two i32 loads.
        field_offsets: list[tuple[int, str]] = []
        offset = 4  # skip func_table_idx
        for _tname, _idx, cap_wt in captures:
            if cap_wt == "i32_pair":
                offset = _align_up(offset, 4)
                field_offsets.append((offset, cap_wt))
                offset += 8  # ptr (4) + len (4)
            elif cap_wt in ("i64", "f64"):
                offset = _align_up(offset, 8)
                field_offsets.append((offset, cap_wt))
                offset += 8
            else:  # i32
                offset = _align_up(offset, 4)
                field_offsets.append((offset, cap_wt))
                offset += 4
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

        # Translate and push remaining arguments
        arg_wasm_types: list[str] = []
        for arg in value_args:
            arg_instrs = self.translate_expr(arg, env)
            if arg_instrs is None:
                return None
            instructions.extend(arg_instrs)
            # Infer WASM type for call_indirect type signature.
            # Pair types (String, Array) push two i32 values onto the stack.
            wt = self._infer_expr_wasm_type(arg)
            if wt == "i32_pair":
                arg_wasm_types.extend(["i32", "i32"])
            elif wt is None:
                # Unit arg: `_infer_expr_wasm_type` returns None and
                # `translate_expr` pushed nothing onto the stack
                # above, so this entry must NOT contribute a phantom
                # param to the call_indirect sig.  The closure-lift
                # side at `vera/codegen/closures.py:85` likewise skips
                # Unit params, so the two sides agree on omitting
                # them (#586).  Per the type-checker invariant, the
                # only well-typed expression for which
                # `_infer_expr_wasm_type` returns None is a Unit-typed
                # one — anything else would have failed type-check
                # before reaching codegen, so an explicit branch here
                # documents the intent without needing a runtime
                # assert (which would have to re-run type inference
                # to verify Unit-typedness, defeating the purpose).
                pass
            else:
                arg_wasm_types.append(wt)

        # Load func_table_idx from closure struct
        instructions.append(f"local.get {tmp}")
        instructions.append("i32.load offset=0")

        # Build call_indirect type signature
        # Return type: infer from the enclosing function's expected return
        # or from the closure's type if available
        ret_wt = self._infer_apply_fn_return_type(closure_arg)
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
        body: ast.Expr,
        param_counts: dict[str, int],
    ) -> list[tuple[str, int, str]]:
        """Collect free variables in an anonymous function body.

        Walks the body and finds SlotRef nodes that reference bindings
        from the enclosing scope (De Bruijn index >= param count for
        that type). Returns list of (type_name, adjusted_index, wasm_type).
        The adjusted_index is the De Bruijn index in the OUTER scope.
        """
        free: list[tuple[str, int, str]] = []
        seen: set[tuple[str, int]] = set()
        self._walk_free_vars(body, param_counts, free, seen)
        return free

    def _walk_free_vars(
        self,
        expr: ast.Expr,
        param_counts: dict[str, int],
        free: list[tuple[str, int, str]],
        seen: set[tuple[str, int]],
    ) -> None:
        """Recursively walk an expression to find free variable references."""
        if isinstance(expr, ast.SlotRef):
            type_name = expr.type_name
            if expr.type_args:
                arg_names = []
                for ta in expr.type_args:
                    if isinstance(ta, ast.NamedType):
                        arg_names.append(ta.name)
                    else:
                        return
                type_name = f"{expr.type_name}<{', '.join(arg_names)}>"
            count = param_counts.get(type_name, 0)
            if expr.index >= count:
                # This refers to an outer scope binding
                outer_idx = expr.index - count
                key = (type_name, outer_idx)
                if key not in seen:
                    seen.add(key)
                    # Infer wasm type from type name.  `_type_name_to_wasm`
                    # collapses every composite type to a single ``"i32"``
                    # for handler-callsite compatibility, so we re-detect
                    # the pair shape here (#535): String / Array<T> values
                    # live as two consecutive i32 slots (ptr, len) and a
                    # closure capture must serialise both.  Pre-fix the
                    # capture path used the bare ``"i32"`` and stored only
                    # the ptr — the body then read len from adjacent
                    # struct memory (typically zero), making the captured
                    # value silently appear empty.
                    if (
                        type_name == "String"
                        or type_name == "Array"
                        or type_name.startswith("Array<")
                    ):
                        wt = "i32_pair"
                    else:
                        wt = self._type_name_to_wasm(type_name)
                    free.append((type_name, outer_idx, wt))
            return

        if isinstance(expr, ast.BinaryExpr):
            self._walk_free_vars(expr.left, param_counts, free, seen)
            self._walk_free_vars(expr.right, param_counts, free, seen)
        elif isinstance(expr, ast.UnaryExpr):
            self._walk_free_vars(expr.operand, param_counts, free, seen)
        elif isinstance(expr, ast.IfExpr):
            self._walk_free_vars(expr.condition, param_counts, free, seen)
            self._walk_free_vars(expr.then_branch, param_counts, free, seen)
            self._walk_free_vars(expr.else_branch, param_counts, free, seen)
        elif isinstance(expr, ast.Block):
            extra = dict(param_counts)
            for stmt in expr.statements:
                if isinstance(stmt, ast.LetStmt):
                    self._walk_free_vars(stmt.value, extra, free, seen)
                    # The let binding adds to the local scope
                    let_name = self._type_expr_name(stmt.type_expr)
                    if let_name:
                        extra[let_name] = extra.get(let_name, 0) + 1
                elif isinstance(stmt, ast.ExprStmt):
                    self._walk_free_vars(stmt.expr, extra, free, seen)
            if expr.expr:
                self._walk_free_vars(expr.expr, extra, free, seen)
        elif isinstance(expr, ast.FnCall):
            for arg in expr.args:
                self._walk_free_vars(arg, param_counts, free, seen)
        elif isinstance(expr, ast.QualifiedCall):
            for arg in expr.args:
                self._walk_free_vars(arg, param_counts, free, seen)
        elif isinstance(expr, ast.ConstructorCall):
            for arg in expr.args:
                self._walk_free_vars(arg, param_counts, free, seen)
        elif isinstance(expr, ast.MatchExpr):
            self._walk_free_vars(expr.scrutinee, param_counts, free, seen)
            for arm in expr.arms:
                arm_extra = dict(param_counts)
                # Match arm bindings add to scope
                self._collect_pattern_bindings(
                    arm.pattern, arm_extra,
                )
                self._walk_free_vars(arm.body, arm_extra, free, seen)
        elif isinstance(expr, ast.AnonFn):
            # #514: nested closures may reference outer-scope bindings
            # via De Bruijn indices that exceed the inner closure's own
            # parameter count for that type.  From the OUTER's
            # perspective, anything an inner closure captures from the
            # outer's scope is also a capture for the outer.  Recurse
            # with the inner's params added to the count so its own
            # parameter refs are excluded; remaining refs bubble up.
            inner_counts = dict(param_counts)
            for p in expr.params:
                pname = self._type_expr_name(p)
                if pname:
                    inner_counts[pname] = inner_counts.get(pname, 0) + 1
            self._walk_free_vars(expr.body, inner_counts, free, seen)
        elif isinstance(expr, ast.IndexExpr):
            # #588: indexing inside a closure body — `coll[idx]`.  Both
            # the collection and index sub-expressions can reference
            # captured outer slots (e.g. `@Array<Int>.0[@Nat.1]` where
            # both halves come from the outer scope).  Pre-fix this
            # branch was missing entirely: the walker fell through the
            # if/elif chain, the outer-scope SlotRef inside `[]` was
            # never recognised as a capture, so `captures` was empty
            # at the lift site.  The body translation then failed
            # (the SlotRef couldn't be resolved against the empty
            # capture-only env) and `_compile_lifted_closure` returned
            # None — but the call site had already emitted a
            # `call_indirect` to the now-absent function-table entry,
            # producing "unknown table 0: table index out of bounds"
            # at WASM validation (flat case) or runtime "indirect call
            # type mismatch" (nested case).
            self._walk_free_vars(expr.collection, param_counts, free, seen)
            self._walk_free_vars(expr.index, param_counts, free, seen)
        elif isinstance(expr, ast.ArrayLit):
            # Array literals may contain captured slots in their
            # elements (e.g. `[@Int.0, @Int.1, @Int.2]`).  Same silent-
            # fail class as IndexExpr above — missing branch silently
            # drops the captures.
            for elem in expr.elements:
                self._walk_free_vars(elem, param_counts, free, seen)
        elif isinstance(expr, ast.InterpolatedString):
            # Interpolated string parts alternate `str | Expr`.
            # Captured slots can appear in the Expr parts
            # (e.g. `"value: \(@Int.0)"`); the str fragments have none.
            for part in expr.parts:
                if isinstance(part, ast.Expr):
                    self._walk_free_vars(part, param_counts, free, seen)
        elif isinstance(expr, ast.HandleExpr):
            # Handle expression: walk the handled body, the optional
            # initial state expression, and each clause's body and
            # optional state-update expression.  Clause params add to
            # the scope before the clause body is walked so the op's
            # own parameters aren't treated as captures.
            self._walk_free_vars(expr.body, param_counts, free, seen)
            if expr.state is not None:
                self._walk_free_vars(
                    expr.state.init_expr, param_counts, free, seen,
                )
            for clause in expr.clauses:
                clause_counts = dict(param_counts)
                for p in clause.params:
                    pname = self._type_expr_name(p)
                    if pname:
                        clause_counts[pname] = (
                            clause_counts.get(pname, 0) + 1
                        )
                # Handler state (@T) is also in scope inside the clause
                # body so references to it aren't captures.
                if expr.state is not None:
                    sname = self._type_expr_name(expr.state.type_expr)
                    if sname:
                        clause_counts[sname] = (
                            clause_counts.get(sname, 0) + 1
                        )
                self._walk_free_vars(
                    clause.body, clause_counts, free, seen,
                )
                if clause.state_update is not None:
                    _, update_expr = clause.state_update
                    self._walk_free_vars(
                        update_expr, clause_counts, free, seen,
                    )
        elif isinstance(expr, (ast.AssertExpr, ast.AssumeExpr)):
            # assert/assume wrap a Bool predicate that can reference
            # outer slots.
            self._walk_free_vars(expr.expr, param_counts, free, seen)
        elif isinstance(expr, (ast.ForallExpr, ast.ExistsExpr)):
            # Quantifiers walk both the domain (which may reference
            # captures) and the predicate (an AnonFn — the existing
            # AnonFn branch above already handles param-shadowing).
            self._walk_free_vars(expr.domain, param_counts, free, seen)
            self._walk_free_vars(expr.predicate, param_counts, free, seen)
        elif isinstance(expr, ast.ModuleCall):
            # Cross-module call: arguments may contain captured slots.
            for arg in expr.args:
                self._walk_free_vars(arg, param_counts, free, seen)
        # Other expression types (literals: Int / Float / Bool / Unit /
        # String / NullaryConstructor / HoleExpr / ResultRef / Old /
        # New) have no sub-expressions that could reference captures.

    def _collect_pattern_bindings(
        self,
        pattern: ast.Pattern,
        counts: dict[str, int],
    ) -> None:
        """Collect type bindings introduced by a match pattern."""
        if isinstance(pattern, ast.BindingPattern):
            b_name = self._type_expr_name(pattern.type_expr)
            if b_name:
                counts[b_name] = counts.get(b_name, 0) + 1
        elif isinstance(pattern, ast.ConstructorPattern):
            for sub in pattern.sub_patterns:
                self._collect_pattern_bindings(sub, counts)
