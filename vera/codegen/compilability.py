"""Mixin for function compilability checks.

Determines whether a function can be compiled to WASM based on its
effects, parameter types, and return type.  Also scans function bodies
for State handler expressions.
"""

from __future__ import annotations

from vera import ast
from vera.wasm.async_fusion import await_needs_check, fused_async_target


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
                        self._needs_memory = True
                    elif eff.name == "State":
                        # State<T> — T must be a compilable primitive
                        if not self._check_state_type(decl, eff):
                            return False
                    elif eff.name == "Exn":
                        # Exn<E> — E must be a compilable type
                        if not self._check_exn_type(decl, eff):
                            return False
                    elif eff.name == "Http":
                        self._needs_memory = True
                    elif eff.name == "Async":
                        pass  # Sequential execution, no host imports
                    elif eff.name == "Inference":
                        self._needs_memory = True
                    elif eff.name == "Random":
                        # #465 — host-import effect, no memory need
                        # (no allocations or heap returns).
                        pass
                    else:
                        self._warning(
                            decl,
                            f"Function '{decl.name}' uses unsupported "
                            f"effect '{eff.name}' — skipped.",
                            rationale="Only pure, IO, Http, Inference, "
                            "Random, State<T>, Exn<E>, and Async "
                            "effects are compilable.",
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
                    rationale=(
                        "WASM code generation supports a fixed set of "
                        "parameter types; this parameter's type is not among "
                        "them, so the function is skipped rather than "
                        "miscompiled."
                    ),
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
                rationale=(
                    "WASM code generation supports a fixed set of return "
                    "types; this function's return type is not among them, "
                    "so the function is skipped rather than miscompiled."
                ),
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

    def _check_exn_type(
        self, decl: ast.FnDecl, eff: ast.EffectRef
    ) -> bool:
        """Validate an Exn<E> effect and register its type.

        Returns True if compilable, False otherwise.
        """
        if not eff.type_args or len(eff.type_args) != 1:
            self._warning(
                decl,
                f"Function '{decl.name}' uses Exn without "
                f"a type argument — skipped.",
                rationale="Exn<E> requires exactly one type argument.",
                error_code="E611",
            )
            return False
        type_arg = eff.type_args[0]
        wt = self._type_expr_to_wasm_type(type_arg)
        if wt is None or wt == "unsupported":
            self._warning(
                decl,
                f"Function '{decl.name}' uses Exn with "
                f"unsupported type — skipped.",
                rationale="Exn<E> requires a compilable type "
                "(Int, Nat, Bool, Float64, String).",
                error_code="E612",
            )
            return False
        # i32_pair (String, Array<T>) → WASM exception tag uses two i32 params
        wasm_tag_t = "i32 i32" if wt == "i32_pair" else wt
        type_name = self._type_expr_to_slot_name(type_arg)
        if type_name and (type_name, wasm_tag_t) not in self._exn_types:
            self._exn_types.append((type_name, wasm_tag_t))
        return True

    _MD_BUILTINS = frozenset({
        "md_parse", "md_render", "md_has_heading",
        "md_has_code_block", "md_extract_code_blocks",
    })

    _REGEX_BUILTINS = frozenset({
        "regex_match", "regex_find", "regex_find_all", "regex_replace",
    })

    _MAP_BUILTINS = frozenset({
        "map_new", "map_insert", "map_get", "map_contains",
        "map_remove", "map_size", "map_keys", "map_values",
    })

    _SET_BUILTINS = frozenset({
        "set_new", "set_add", "set_contains",
        "set_remove", "set_size", "set_to_array",
    })

    _DECIMAL_BUILTINS = frozenset({
        "decimal_from_int", "decimal_from_float", "decimal_from_string",
        "decimal_to_string", "decimal_to_float",
        "decimal_add", "decimal_sub", "decimal_mul", "decimal_div",
        "decimal_neg", "decimal_compare", "decimal_eq",
        "decimal_round", "decimal_abs",
    })

    _JSON_BUILTINS = frozenset({
        "json_parse", "json_stringify",
    })

    _HTML_BUILTINS = frozenset({
        "html_parse", "html_to_string", "html_query", "html_text",
    })

    # Math host-imported builtins (#467).  Only the log/trig ops —
    # pi/e and sign/clamp/float_clamp are inlined as WAT, no
    # host import needed.
    _MATH_BUILTINS = frozenset({
        "log", "log2", "log10",
        "sin", "cos", "tan", "asin", "acos", "atan", "atan2",
    })

    def _scan_io_ops(self, node: ast.Node) -> None:
        """Walk a function body looking for IO, Markdown, and Regex builtins.

        Registers each distinct IO operation name (print, read_line, etc.)
        into ``_io_ops_used`` for per-operation import emission.  Also
        registers Markdown host-import builtins into ``_md_ops_used``
        and regex host-import builtins into ``_regex_ops_used``.

        # WALKER_COVERAGE: (#597 — every Expr subclass below has a
        # disposition; check_walker_coverage.py enforces completeness.)
        #
        # Handled (recurses into sub-exprs that may contain registrable calls):
        #   QualifiedCall     → registers IO/Http/Inference/Random op
        #                       then recurses into args
        #   FnCall            → registers Markdown/Regex/Map/Set/Decimal/
        #                       Json/Html/Math builtin then recurses args
        #   Block             → recurses into each stmt + trailing expr
        #   ConstructorCall   → recurses into each arg
        #   BinaryExpr        → recurses into left + right
        #   UnaryExpr         → recurses into operand
        #   IfExpr            → recurses into cond + then + else
        #   MatchExpr         → recurses into scrutinee + arm bodies
        #   HandleExpr        → recurses into body
        #   IndexExpr         → recurses into collection + index
        #                       (defensive add #597 — masked today by
        #                       type checker rejecting IO in index
        #                       positions, but plugs the gap if a
        #                       host-imported Int-returning builtin
        #                       lands in the future)
        #   ArrayLit          → recurses into each element (defensive
        #                       add #597 — masked today by the [E602]
        #                       path dropping IO-in-ArrayLit functions)
        #   InterpolatedString → recurses into each Expr part
        #                       (defensive add #597 — same masking as
        #                       ArrayLit)
        #   AnonFn            → recurses into body (defensive add
        #                       #597 — IS the primary defence: pr-
        #                       review of #668 surfaced that
        #                       `_compile_lifted_closure` in
        #                       `vera/codegen/closures.py` does NOT
        #                       call this scanner on lifted bodies,
        #                       so without this branch IO ops
        #                       inside a closure body would silently
        #                       miss their host-import registration)
        #
        # Intentionally ignored (leaves — no sub-exprs to recurse into):
        #   IntLit            → leaf
        #   FloatLit          → leaf
        #   BoolLit           → leaf
        #   StringLit         → leaf
        #   UnitLit           → leaf
        #   SlotRef           → leaf
        #   ResultRef         → leaf
        #   NullaryConstructor → zero-arg, no sub-exprs
        #   ModuleCall        → cross-module IO tracked separately
        #                       via the imported module's own scan
        #
        # Cannot occur (contract-only or pure-by-construction):
        #   AssertExpr        → predicate is pure, no IO
        #   AssumeExpr        → predicate is pure, no IO
        #   ForallExpr        → quantifier body is pure
        #   ExistsExpr        → quantifier body is pure
        #   OldExpr           → contract-only
        #   NewExpr           → contract-only
        #   HoleExpr          → parser placeholder, check-time rejects
        """
        if isinstance(node, ast.QualifiedCall):
            if node.qualifier == "IO":
                self._io_ops_used.add(node.name)
            elif node.qualifier == "Http":
                self._http_ops_used.add(f"http_{node.name}")
            elif node.qualifier == "Inference":
                self._inference_ops_used.add(f"inference_{node.name}")
            elif node.qualifier == "Random":
                # #465 — op names already begin with `random_`
                # (`random_int`/`random_float`/`random_bool`), which
                # both reads naturally at the call site and prevents
                # collision with bare `int`/`float`/`bool` user
                # effect ops.  Track the name directly.
                self._random_ops_used.add(node.name)
            for arg in node.args:
                self._scan_io_ops(arg)
            return
        if isinstance(node, ast.Block):
            for stmt in node.statements:
                if isinstance(stmt, ast.LetStmt):
                    self._scan_io_ops(stmt.value)
                elif isinstance(stmt, ast.ExprStmt):
                    self._scan_io_ops(stmt.expr)
            self._scan_io_ops(node.expr)
        elif isinstance(node, ast.FnCall):
            # #841: fused-async interception — must agree exactly with
            # the WasmContext translation (shared predicates in
            # vera/wasm/async_fusion.py).  A fused async(Http.get(...))
            # registers the async_http_* import INSTEAD of the sync
            # http_* the QualifiedCall branch would register when the
            # walk reached the inner call; an await that needs the
            # fused-handle runtime check additionally registers
            # async_await (its argument is still scanned normally).
            fused = fused_async_target(node)
            if fused is not None:
                self._async_ops_used.add(fused)
                inner = node.args[0]
                assert isinstance(inner, ast.QualifiedCall)
                for arg in inner.args:
                    self._scan_io_ops(arg)
                return
            if (
                node.name == "await"
                and len(node.args) == 1
                and await_needs_check(node.args[0], self._future_ret_fns)
            ):
                self._async_ops_used.add("async_await")
            if node.name in self._MD_BUILTINS:
                self._md_ops_used.add(node.name)
            if node.name in self._REGEX_BUILTINS:
                self._regex_ops_used.add(node.name)
            if node.name in self._MAP_BUILTINS:
                self._map_ops_used.add(node.name)
            if node.name in self._SET_BUILTINS:
                self._set_ops_used.add(node.name)
            if node.name in self._DECIMAL_BUILTINS:
                self._decimal_ops_used.add(node.name)
            if node.name in self._JSON_BUILTINS:
                self._json_ops_used.add(node.name)
            if node.name in self._HTML_BUILTINS:
                self._html_ops_used.add(node.name)
            if node.name in self._MATH_BUILTINS:
                self._math_ops_used.add(node.name)
            for arg in node.args:
                self._scan_io_ops(arg)
        elif isinstance(node, ast.ConstructorCall):
            for arg in node.args:
                self._scan_io_ops(arg)
        elif isinstance(node, ast.BinaryExpr):
            self._scan_io_ops(node.left)
            self._scan_io_ops(node.right)
        elif isinstance(node, ast.UnaryExpr):
            self._scan_io_ops(node.operand)
        elif isinstance(node, ast.IfExpr):
            self._scan_io_ops(node.condition)
            self._scan_io_ops(node.then_branch)
            if node.else_branch:
                self._scan_io_ops(node.else_branch)
        elif isinstance(node, ast.MatchExpr):
            self._scan_io_ops(node.scrutinee)
            for arm in node.arms:
                self._scan_io_ops(arm.body)
        elif isinstance(node, ast.HandleExpr):
            self._scan_io_ops(node.body)
        # Defensive sub-expr recursion (#597) — three of the four
        # branches below (IndexExpr, ArrayLit, InterpolatedString)
        # are masked today by type-checker rules and the [E602]
        # codegen-skip path; the AnonFn branch is the PRIMARY
        # defence — the closure compile pipeline does not call
        # this scanner on lifted bodies (verified by pr-review
        # audit on #668), so IO ops inside a closure body would
        # silently miss their host-import registration without
        # this branch.
        elif isinstance(node, ast.IndexExpr):
            self._scan_io_ops(node.collection)
            self._scan_io_ops(node.index)
        elif isinstance(node, ast.ArrayLit):
            for elem in node.elements:
                self._scan_io_ops(elem)
        elif isinstance(node, ast.InterpolatedString):
            for part in node.parts:
                # Parts are str (literal) or Expr (interpolated).
                if not isinstance(part, str):
                    self._scan_io_ops(part)
        elif isinstance(node, ast.AnonFn):
            self._scan_io_ops(node.body)

    def _scan_body_for_state_handlers(self, node: ast.Node) -> None:
        """Walk a function body looking for handle expressions.

        Registers State<T> types for host import generation and
        Exn<E> types for exception tag generation.
        """
        if isinstance(node, ast.HandleExpr):
            if isinstance(node.effect, ast.EffectRef):
                if node.effect.name == "State":
                    if node.effect.type_args and len(node.effect.type_args) == 1:
                        type_arg = node.effect.type_args[0]
                        wt = self._type_expr_to_wasm_type(type_arg)
                        if wt and wt not in ("unsupported", "i32_pair"):
                            type_name = self._type_expr_to_slot_name(type_arg)
                            if type_name and (type_name, wt) not in self._state_types:
                                self._state_types.append((type_name, wt))
                elif node.effect.name == "Exn":
                    if node.effect.type_args and len(node.effect.type_args) == 1:
                        type_arg = node.effect.type_args[0]
                        wt = self._type_expr_to_wasm_type(type_arg)
                        if wt and wt != "unsupported":
                            wasm_tag_t = "i32 i32" if wt == "i32_pair" else wt
                            type_name = self._type_expr_to_slot_name(type_arg)
                            if type_name and (type_name, wasm_tag_t) not in self._exn_types:
                                self._exn_types.append((type_name, wasm_tag_t))
            self._scan_expr_for_handlers(node.body)
            return
        self._scan_expr_for_handlers(node)

    def _scan_expr_for_handlers(self, node: ast.Node) -> None:
        """Recurse into expressions looking for HandleExpr nodes.

        # WALKER_COVERAGE: (#597 — every Expr subclass below has a
        # disposition; check_walker_coverage.py enforces completeness.)
        #
        # Handled (recurses into sub-exprs that may contain HandleExpr):
        #   HandleExpr        → registers State<T>/Exn<E> types + recurses
        #   Block             → recurses into stmts + trailing expr
        #   FnCall            → recurses into each arg
        #   ConstructorCall   → recurses into each arg
        #   BinaryExpr        → recurses into left + right
        #   UnaryExpr         → recurses into operand
        #   IfExpr            → recurses into cond + then + else
        #   MatchExpr         → recurses into scrutinee + arm bodies
        #   QualifiedCall     → recurses into args (defensive add #597)
        #   IndexExpr         → recurses into collection + index
        #                       (defensive add #597)
        #   ArrayLit          → recurses into each element
        #                       (defensive add #597)
        #   InterpolatedString → recurses into each Expr part
        #                       (defensive add #597)
        #   AnonFn            → recurses into body (defensive add #597 —
        #                       IS the primary defence: the closure
        #                       compile pipeline does not run its own
        #                       handler scan on lifted bodies, so
        #                       without this branch HandleExprs inside
        #                       a closure body would silently miss
        #                       their State/Exn host-import
        #                       registration)
        #
        # Intentionally ignored (leaves — no sub-exprs to walk):
        #   IntLit            → leaf
        #   FloatLit          → leaf
        #   BoolLit           → leaf
        #   StringLit         → leaf
        #   UnitLit           → leaf
        #   SlotRef           → leaf
        #   ResultRef         → leaf
        #   NullaryConstructor → zero-arg, no sub-exprs
        #   ModuleCall        → handlers in imported module tracked
        #                       by that module's own scan
        #
        # Cannot occur (contract-only or pure):
        #   AssertExpr        → predicate is pure; no handle in pred
        #   AssumeExpr        → predicate is pure
        #   ForallExpr        → quantifier body is pure
        #   ExistsExpr        → quantifier body is pure
        #   OldExpr           → contract-only
        #   NewExpr           → contract-only
        #   HoleExpr          → parser placeholder, check-time rejects
        """
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
        # Defensive sub-expr recursion (#597) — symmetrical with
        # `_scan_io_ops`.  The QualifiedCall / IndexExpr / ArrayLit
        # / InterpolatedString branches are masked today by type-
        # checker rules and the [E602] codegen-skip path.  The
        # AnonFn branch is the PRIMARY defence — the closure
        # compile pipeline does not call this scanner on lifted
        # bodies, so HandleExprs inside a closure body would
        # silently miss their State/Exn host-import registration
        # without this branch.
        elif isinstance(node, ast.QualifiedCall):
            for arg in node.args:
                self._scan_expr_for_handlers(arg)
        elif isinstance(node, ast.IndexExpr):
            self._scan_expr_for_handlers(node.collection)
            self._scan_expr_for_handlers(node.index)
        elif isinstance(node, ast.ArrayLit):
            for elem in node.elements:
                self._scan_expr_for_handlers(elem)
        elif isinstance(node, ast.InterpolatedString):
            for part in node.parts:
                if not isinstance(part, str):
                    self._scan_expr_for_handlers(part)
        elif isinstance(node, ast.AnonFn):
            self._scan_expr_for_handlers(node.body)
