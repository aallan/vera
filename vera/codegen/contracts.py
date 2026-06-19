"""Mixin for runtime contract insertion.

Compiles requires/ensures clauses into WASM precondition and
postcondition checks with informative failure messages.
"""

from __future__ import annotations

from vera import ast
from vera.wasm import WasmContext, WasmSlotEnv


class ContractsMixin:
    """Methods for compiling runtime contract checks."""

    def _refinement_guard_parts(
        self, te: ast.TypeExpr,
    ) -> tuple[ast.Expr, str] | None:
        """(predicate, base slot-name) if *te* is a refinement, else None
        (#746) — the codegen counterpart of the verifier's ``_refined_parts``.

        Resolves an alias chain (``type PosInt = { @Int | ... }``; also
        ``type P2 = PosInt``) to the underlying ``RefinementType`` and returns
        its predicate plus the base type's *name* (the binder slot, e.g.
        ``Int`` for ``{ @Int | ... }`` or the canonical ``Array<Int>`` for
        ``{ @Array<Int> | array_length(@Array<Int>.0) > 0 }`` — matching
        ``_translate_slot_ref``'s key, since a bare ``Array`` would never
        resolve).  Unlike the
        verify side — where Z3 cannot decide ``array_length`` so a collection
        base is Tier 3 — the runtime guard compiles the predicate to WASM
        directly, so it covers any base whose predicate
        :py:meth:`WasmContext.translate_expr` can lower (:py:meth:`_emit_refinement_check`
        returns None and emits no guard when it cannot)."""
        node: ast.TypeExpr = te
        seen: set[str] = set()
        while (isinstance(node, ast.NamedType)
               and node.name in self._type_aliases
               and node.name not in seen):
            seen.add(node.name)
            node = self._type_aliases[node.name]
        if isinstance(node, ast.RefinementType):
            base = node.base_type
            if isinstance(base, ast.NamedType):
                # Build the canonical slot name the predicate's binder uses —
                # ``Array<Int>`` for a parameterised base, ``Int`` otherwise —
                # matching `_translate_slot_ref`'s key (a bare ``Array`` would
                # never resolve).
                name = base.name
                if base.type_args:
                    arg_names: list[str] = []
                    for ta in base.type_args:
                        if isinstance(ta, ast.NamedType):
                            arg_names.append(ta.name)
                        else:
                            return None
                    name = f"{base.name}<{', '.join(arg_names)}>"
                predicate = node.predicate
                # Conjoin the `@Nat` base's implicit `>= 0` when the base
                # resolves to `@Nat` — directly OR through an alias chain
                # (`type Age = Nat`).  The *decision* follows the base's
                # aliases, but the synthetic slot ref uses `name` (the binder
                # key the predicate uses and the guard pushes the value under,
                # e.g. `@Age.0`), NOT a literal `@Nat.0` which wouldn't resolve.
                # Mirrors the verifier's `_translate_refined_predicate` so the
                # runtime guard (and its trap message, both derived here) reject
                # a negative value satisfying P — `-1` for `{ @Age | @Age.0 < 10
                # }` — at an FFI/public boundary (CR f1f2a26, db24433).
                base_node: ast.TypeExpr = base
                bseen: set[str] = set()
                while (isinstance(base_node, ast.NamedType)
                       and base_node.name in self._type_aliases
                       and base_node.name not in bseen):
                    bseen.add(base_node.name)
                    base_node = self._type_aliases[base_node.name]
                if (isinstance(base_node, ast.NamedType)
                        and base_node.name == "Unit"):
                    # `@Unit` is zero-size / erased: there is no value to load
                    # into a boundary predicate check, so emit NO guard (the
                    # verifier records such a refinement `tier3_unguarded`
                    # rather than claiming a runtime check; CR db24433).
                    return None
                if (isinstance(base_node, ast.NamedType)
                        and base_node.name == "Nat"):
                    predicate = ast.BinaryExpr(
                        op=ast.BinOp.AND,
                        left=ast.BinaryExpr(
                            op=ast.BinOp.GE,
                            left=ast.SlotRef(
                                type_name=name, type_args=None, index=0),
                            right=ast.IntLit(value=0),
                        ),
                        right=predicate,
                    )
                return (predicate, name)
        return None

    def _emit_refinement_check(
        self,
        ctx: WasmContext,
        predicate: ast.Expr,
        base_name: str,
        value_local: int,
        message: str,
        base_env: WasmSlotEnv,
    ) -> list[str] | None:
        """Compile a refinement-predicate runtime guard over *value_local*
        (#746).

        The predicate is closed over the binder ``@<base>.0``; translating it
        against *base_env* extended with that base bound to *value_local* reads
        the value and yields an i32 boolean, exactly like a ``requires``
        clause.  Extending the function's own slot env (rather than a bare one)
        preserves the surrounding type context a pair value such as ``Array``
        needs — its ``(ptr, len)`` representation — so ``array_length`` and the
        like translate.  Traps via the ``$vera.contract_fail`` host import (the
        same channel used for precondition / postcondition failures) when the
        predicate is false.  Returns None when the predicate falls outside the
        compilable fragment (no guard emitted)."""
        guard_env = base_env.push(base_name, value_local)
        cond = ctx.translate_expr(predicate, guard_env)
        if cond is None:
            return None
        ptr, length = self.string_pool.intern(message)
        self._needs_contract_fail = True
        self._needs_memory = True
        return [
            *cond,
            "i32.eqz",
            "if",
            f"  i32.const {ptr}",
            f"  i32.const {length}",
            "  call $vera.contract_fail",
            "  unreachable",
            "end",
        ]

    def _format_contract_message(
        self,
        decl: ast.FnDecl,
        contract: ast.Requires | ast.Ensures,
    ) -> str:
        """Build a human-readable contract failure message string.

        For a Requires:
          Precondition violation in clamp(@Int, @Int, @Int -> @Int)
            requires(@Int.1 <= @Int.2) failed

        For an Ensures:
          Postcondition violation in double(@Int -> @Int)
            ensures(@Int.result >= 0) failed
        """
        if isinstance(contract, ast.Requires):
            kind = "Precondition"
            clause = "requires"
        else:
            kind = "Postcondition"
            clause = "ensures"
        sig = ast.format_fn_signature(decl)
        expr_text = ast.format_expr(contract.expr)
        return f"{kind} violation in {sig}\n  {clause}({expr_text}) failed"

    def _format_refinement_message(
        self,
        decl: ast.FnDecl,
        te: ast.TypeExpr,
        role: str,
    ) -> str:
        """Build a refinement-violation message for a runtime guard (#746).

        e.g. ``Refinement violation in clamp(@Int -> @Percentage)
        / return value: @Int.0 >= 0 && @Int.0 <= 100 failed``.  *role* is
        ``"parameter"`` or ``"return value"``.
        """
        sig = ast.format_fn_signature(decl)
        parts = self._refinement_guard_parts(te)
        pred_text = ast.format_expr(parts[0]) if parts is not None else "?"
        return (
            f"Refinement violation in {sig}\n"
            f"  {role}: {pred_text} failed"
        )

    def _compile_preconditions(
        self,
        ctx: WasmContext,
        decl: ast.FnDecl,
        env: WasmSlotEnv,
    ) -> list[str]:
        """Compile runtime precondition checks.

        Non-trivial requires() clauses are compiled as:
            [condition]
            i32.eqz
            if
              i32.const <msg_ptr>
              i32.const <msg_len>
              call $vera.contract_fail
              unreachable  ;; trap on precondition violation
            end
        """
        instrs: list[str] = []
        for contract in decl.contracts:
            if not isinstance(contract, ast.Requires):
                continue
            if self._is_trivial_contract(contract):
                continue

            # Translate the precondition expression
            cond_instrs = ctx.translate_expr(contract.expr, env)
            if cond_instrs is None:
                # Can't compile this contract — skip silently
                # (verifier already classified it as Tier 3)
                continue

            instrs.extend(cond_instrs)
            instrs.append("i32.eqz")
            instrs.append("if")

            # Report which contract failed before trapping
            msg = self._format_contract_message(decl, contract)
            ptr, length = self.string_pool.intern(msg)
            self._needs_contract_fail = True
            self._needs_memory = True
            instrs.append(f"  i32.const {ptr}")
            instrs.append(f"  i32.const {length}")
            instrs.append("  call $vera.contract_fail")

            instrs.append("  unreachable")
            instrs.append("end")
        return instrs

    def _compile_postconditions(
        self,
        ctx: WasmContext,
        decl: ast.FnDecl,
        env: WasmSlotEnv,
        ret_wt: str | None,
    ) -> list[str]:
        """Compile runtime postcondition checks.

        For functions returning a value:
            local.set $result_tmp    ;; save body result
            [condition with @T.result → local.get $result_tmp]
            i32.eqz
            if
              unreachable            ;; trap on postcondition violation
            end
            local.get $result_tmp    ;; push result back

        For Unit-returning functions, no result to save/restore.
        """
        # Collect non-trivial ensures clauses
        ensures_clauses: list[ast.Ensures] = []
        for contract in decl.contracts:
            if isinstance(contract, ast.Ensures):
                if not self._is_trivial_contract(contract):
                    ensures_clauses.append(contract)

        # #746: a refined return type is an implicit postcondition on the
        # result — guarded here alongside the explicit ensures, so a function
        # returning a refinement-violating value traps even with trivial
        # ensures.
        refined_ret = self._refinement_guard_parts(decl.return_type)

        if not ensures_clauses and refined_ret is None:
            return []

        # Pair returns (String/Array) don't support general ensures checks
        # — can't bind `@T.result` to a two-value result.  A refinement guard,
        # however, needs only the value's primary local (the ptr; the length
        # is read from memory, as the param-guard path shows), so a refined
        # String *or* Array return IS guarded by saving both halves around the
        # check.  `_refinement_guard_parts` resolves the canonical base name
        # for a collection base too, so a `@NonEmptyArray` return is guarded
        # here despite being Tier-3 *statically* (#746) — see
        # test_array_return_guard_traps_on_empty.
        if ret_wt == "i32_pair":
            if refined_ret is None:
                return []
            predicate, base_name = refined_ret
            ptr_l = ctx.alloc_local("i32")
            len_l = ctx.alloc_local("i32")
            msg = self._format_refinement_message(
                decl, decl.return_type, "return value")
            guard = self._emit_refinement_check(
                ctx, predicate, base_name, ptr_l, msg, env)
            if guard is None:
                return []
            # Result is (ptr, len) with len on top of the stack.
            return [
                f"local.set {len_l}",
                f"local.set {ptr_l}",
                *guard,
                f"local.get {ptr_l}",
                f"local.get {len_l}",
            ]

        instrs: list[str] = []

        if ret_wt is not None:
            # Function returns a value — save it to a temp local
            result_local = ctx.alloc_local(ret_wt)
            ctx.set_result_local(result_local)
            instrs.append(f"local.set {result_local}")

            # #746: emit the refined-return guard BEFORE the explicit ensures
            # — an `ensures(...)` may depend on the return's refinement
            # invariant (e.g. divide by `@NonZero.result`), so the guard must
            # establish it first and report the boundary violation via
            # $vera.contract_fail rather than letting the postcondition trap on
            # the bad value (symmetric with the param-guard ordering in
            # functions.py).
            if refined_ret is not None:
                predicate, base_name = refined_ret
                msg = self._format_refinement_message(
                    decl, decl.return_type, "return value")
                guard = self._emit_refinement_check(
                    ctx, predicate, base_name, result_local, msg, env)
                if guard is not None:
                    instrs.extend(guard)

            for ensures in ensures_clauses:
                cond_instrs = ctx.translate_expr(ensures.expr, env)
                if cond_instrs is None:
                    # Can't compile — skip
                    continue
                instrs.extend(cond_instrs)
                instrs.append("i32.eqz")
                instrs.append("if")

                msg = self._format_contract_message(decl, ensures)
                ptr, length = self.string_pool.intern(msg)
                self._needs_contract_fail = True
                self._needs_memory = True
                instrs.append(f"  i32.const {ptr}")
                instrs.append(f"  i32.const {length}")
                instrs.append("  call $vera.contract_fail")

                instrs.append("  unreachable")
                instrs.append("end")

            # Push result back
            instrs.append(f"local.get {result_local}")
        else:
            # Unit return — no result to save, just check
            for ensures in ensures_clauses:
                cond_instrs = ctx.translate_expr(ensures.expr, env)
                if cond_instrs is None:
                    continue
                instrs.extend(cond_instrs)
                instrs.append("i32.eqz")
                instrs.append("if")

                msg = self._format_contract_message(decl, ensures)
                ptr, length = self.string_pool.intern(msg)
                self._needs_contract_fail = True
                self._needs_memory = True
                instrs.append(f"  i32.const {ptr}")
                instrs.append(f"  i32.const {length}")
                instrs.append("  call $vera.contract_fail")

                instrs.append("  unreachable")
                instrs.append("end")

        return instrs

    @staticmethod
    def _is_trivial_contract(contract: ast.Contract) -> bool:
        """Check if a contract is trivially true (literal true).

        Trivial contracts are skipped — no runtime check needed.
        """
        if isinstance(contract, ast.Requires):
            return isinstance(contract.expr, ast.BoolLit) and contract.expr.value
        if isinstance(contract, ast.Ensures):
            return isinstance(contract.expr, ast.BoolLit) and contract.expr.value
        return False

    def _snapshot_old_state(
        self,
        ctx: WasmContext,
        decl: ast.FnDecl,
    ) -> list[str]:
        """Emit instructions to snapshot state at function entry for old().

        Walks ensures clauses to find old(State<T>) references.
        For each unique State<T>, calls the host state_get import and
        saves the result to a temp local. Registers the mapping on ctx
        so translate_expr can resolve OldExpr later.

        Returns WASM instructions (call + local.set) to insert after
        preconditions and before the function body.
        """
        old_types = self._find_old_state_types(decl)
        if not old_types:
            return []

        instrs: list[str] = []
        old_locals: dict[str, int] = {}

        for type_name in sorted(old_types):
            # Determine the WASM type for this State<T>
            wasm_t = self._state_type_to_wasm(type_name)
            if wasm_t is None:
                continue
            # Allocate a temp local for the snapshot
            local_idx = ctx.alloc_local(wasm_t)
            # Emit: call $vera.state_get_<Type> ; local.set <idx>
            instrs.append(f"call $vera.state_get_{type_name}")
            instrs.append(f"local.set {local_idx}")
            old_locals[type_name] = local_idx

        if old_locals:
            ctx.set_old_state_locals(old_locals)

        return instrs

    def _find_old_state_types(self, decl: ast.FnDecl) -> set[str]:
        """Find all State<T> type names referenced by old() in ensures clauses.

        Walks each non-trivial ensures expression looking for OldExpr nodes.
        Returns a set of type names, e.g. {"Int"}.
        """
        types: set[str] = set()
        for contract in decl.contracts:
            if not isinstance(contract, ast.Ensures):
                continue
            if self._is_trivial_contract(contract):
                continue
            self._collect_old_types(contract.expr, types)
        return types

    def _collect_old_types(
        self, expr: ast.Expr, types: set[str],
    ) -> None:
        """Recursively collect State<T> type names from OldExpr nodes."""
        if isinstance(expr, ast.OldExpr):
            type_name = WasmContext._extract_state_type_name(
                expr.effect_ref,
            )
            if type_name is not None:
                types.add(type_name)
            return
        # Walk child expressions
        for child in self._expr_children(expr):
            self._collect_old_types(child, types)

    @staticmethod
    def _expr_children(expr: ast.Expr) -> list[ast.Expr]:
        """Return direct child expressions for AST walking."""
        children: list[ast.Expr] = []
        if isinstance(expr, ast.BinaryExpr):
            children.extend([expr.left, expr.right])
        elif isinstance(expr, ast.UnaryExpr):
            children.append(expr.operand)
        elif isinstance(expr, ast.FnCall):
            children.extend(expr.args)
        elif isinstance(expr, ast.IfExpr):
            children.append(expr.condition)
        elif isinstance(expr, ast.NewExpr):
            pass  # No child expressions to walk
        elif isinstance(expr, ast.OldExpr):
            pass  # Already handled by caller
        return children

    def _state_type_to_wasm(self, type_name: str) -> str | None:
        """Map a State type name (e.g. 'Int') to its WASM type."""
        for registered_name, wasm_t in self._state_types:
            if registered_name == type_name:
                return wasm_t
        return None
