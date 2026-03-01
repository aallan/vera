"""Mixin for runtime contract insertion.

Compiles requires/ensures clauses into WASM precondition and
postcondition checks with informative failure messages.
"""

from __future__ import annotations

from vera import ast
from vera.wasm import WasmContext, WasmSlotEnv


class ContractsMixin:
    """Methods for compiling runtime contract checks."""

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

        if not ensures_clauses:
            return []

        # Pair returns (String/Array) don't support postcondition checks
        # — can't save/restore a two-value result with a single local
        if ret_wt == "i32_pair":
            return []

        instrs: list[str] = []

        if ret_wt is not None:
            # Function returns a value — save it to a temp local
            result_local = ctx.alloc_local(ret_wt)
            ctx.set_result_local(result_local)
            instrs.append(f"local.set {result_local}")

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
