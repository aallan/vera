"""Mixin for function compilability checks.

Determines whether a function can be compiled to WASM based on its
effects, parameter types, and return type.  Also scans function bodies
for State handler expressions.
"""

from __future__ import annotations

from vera import ast


class CompilabilityMixin:
    """Methods for checking if functions are compilable to WASM."""

    def _is_compilable(self, decl: ast.FnDecl) -> bool:
        """Check if a function can be compiled to WASM.

        Accepts pure functions, IO effects, and State<T> where T is
        a compilable primitive type (Int, Nat, Bool, Float64).
        """
        # Check effect: must be pure, <IO>, or <State<T>>
        effect = decl.effect
        if isinstance(effect, ast.PureEffect):
            pass  # OK
        elif isinstance(effect, ast.EffectSet):
            for eff in effect.effects:
                if isinstance(eff, ast.EffectRef):
                    if eff.name == "IO":
                        self._needs_io_print = True
                        self._needs_memory = True
                    elif eff.name == "State":
                        # State<T> — T must be a compilable primitive
                        if not self._check_state_type(decl, eff):
                            return False
                    else:
                        self._warning(
                            decl,
                            f"Function '{decl.name}' uses unsupported "
                            f"effect '{eff.name}' — skipped.",
                            rationale="Only pure, IO, and State<T> effects "
                            "are compilable.",
                            error_code="E603",
                        )
                        return False
                else:
                    return False
        else:
            return False

        # Check parameter types
        for p in decl.params:
            wt = self._type_expr_to_wasm_type(p)
            if wt == "unsupported":
                self._warning(
                    decl,
                    f"Function '{decl.name}' has unsupported parameter type "
                    f"— skipped.",
                    error_code="E604",
                )
                return False

        # Check return type
        ret_wt = self._type_expr_to_wasm_type(decl.return_type)
        if ret_wt == "unsupported":
            self._warning(
                decl,
                f"Function '{decl.name}' has unsupported return type "
                f"— skipped.",
                error_code="E605",
            )
            return False

        return True

    def _check_state_type(
        self, decl: ast.FnDecl, eff: ast.EffectRef
    ) -> bool:
        """Validate a State<T> effect and register its type.

        Returns True if compilable, False otherwise.
        """
        if not eff.type_args or len(eff.type_args) != 1:
            self._warning(
                decl,
                f"Function '{decl.name}' uses State without "
                f"a type argument — skipped.",
                rationale="State<T> requires exactly one type argument.",
                error_code="E606",
            )
            return False
        type_arg = eff.type_args[0]
        wt = self._type_expr_to_wasm_type(type_arg)
        if wt is None or wt in ("unsupported", "i32_pair"):
            self._warning(
                decl,
                f"Function '{decl.name}' uses State with "
                f"unsupported type — skipped.",
                rationale="State<T> requires a compilable primitive type "
                "(Int, Nat, Bool, Float64).",
                error_code="E607",
            )
            return False
        type_name = self._type_expr_to_slot_name(type_arg)
        if type_name and (type_name, wt) not in self._state_types:
            self._state_types.append((type_name, wt))
        return True

    def _scan_body_for_state_handlers(self, node: ast.Node) -> None:
        """Walk a function body looking for handle[State<T>] expressions.

        When found, registers the State<T> type for host import generation.
        """
        if isinstance(node, ast.HandleExpr):
            if (isinstance(node.effect, ast.EffectRef)
                    and node.effect.name == "State"):
                if node.effect.type_args and len(node.effect.type_args) == 1:
                    type_arg = node.effect.type_args[0]
                    wt = self._type_expr_to_wasm_type(type_arg)
                    if wt and wt not in ("unsupported", "i32_pair"):
                        type_name = self._type_expr_to_slot_name(type_arg)
                        if type_name and (type_name, wt) not in self._state_types:
                            self._state_types.append((type_name, wt))
            self._scan_expr_for_handlers(node.body)
            return
        self._scan_expr_for_handlers(node)

    def _scan_expr_for_handlers(self, node: ast.Node) -> None:
        """Recurse into expressions looking for HandleExpr nodes."""
        if isinstance(node, ast.HandleExpr):
            self._scan_body_for_state_handlers(node)
            return
        if isinstance(node, ast.Block):
            for stmt in node.statements:
                if isinstance(stmt, ast.LetStmt):
                    self._scan_expr_for_handlers(stmt.value)
                elif isinstance(stmt, ast.ExprStmt):
                    self._scan_expr_for_handlers(stmt.expr)
            self._scan_expr_for_handlers(node.expr)
        elif isinstance(node, ast.FnCall):
            for arg in node.args:
                self._scan_expr_for_handlers(arg)
        elif isinstance(node, ast.ConstructorCall):
            for arg in node.args:
                self._scan_expr_for_handlers(arg)
        elif isinstance(node, ast.BinaryExpr):
            self._scan_expr_for_handlers(node.left)
            self._scan_expr_for_handlers(node.right)
        elif isinstance(node, ast.UnaryExpr):
            self._scan_expr_for_handlers(node.operand)
        elif isinstance(node, ast.IfExpr):
            self._scan_expr_for_handlers(node.condition)
            self._scan_expr_for_handlers(node.then_branch)
            if node.else_branch:
                self._scan_expr_for_handlers(node.else_branch)
        elif isinstance(node, ast.MatchExpr):
            self._scan_expr_for_handlers(node.scrutinee)
            for arm in node.arms:
                self._scan_expr_for_handlers(arm.body)
