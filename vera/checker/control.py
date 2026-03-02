"""Control-flow, pattern, and handler type-checking mix-in."""

from __future__ import annotations

from vera import ast
from vera.environment import Binding, FunctionInfo
from vera.types import (
    BOOL,
    NEVER,
    UNIT,
    AdtType,
    ConcreteEffectRow,
    PrimitiveType,
    PureEffectRow,
    Type,
    UnknownType,
    base_type,
    contains_typevar,
    is_subtype,
    pretty_type,
    substitute,
    types_equal,
)


class ControlFlowMixin:

    # -----------------------------------------------------------------
    # Control flow
    # -----------------------------------------------------------------

    def _check_if(self, expr: ast.IfExpr) -> Type | None:
        """Type-check if-then-else."""
        cond_ty = self._synth_expr(expr.condition)
        if cond_ty and not isinstance(cond_ty, UnknownType):
            if not is_subtype(base_type(cond_ty), BOOL):
                self._error(
                    expr.condition,
                    f"If condition must be Bool, found "
                    f"{pretty_type(cond_ty)}.",
                    spec_ref='Chapter 4, Section 4.8 "Conditional Expressions"',
                    error_code="E300",
                )

        then_ty = self._synth_expr(expr.then_branch)
        else_ty = self._synth_expr(expr.else_branch)

        if then_ty is None or else_ty is None:
            return then_ty or else_ty
        if isinstance(then_ty, UnknownType):
            return else_ty
        if isinstance(else_ty, UnknownType):
            return then_ty

        # Never propagation
        if types_equal(then_ty, NEVER):
            return else_ty
        if types_equal(else_ty, NEVER):
            return then_ty

        # Branches must have compatible types
        if is_subtype(then_ty, else_ty):
            return else_ty
        if is_subtype(else_ty, then_ty):
            return then_ty

        # Unresolved TypeVars from nullary constructors — pick the
        # branch with concrete types when possible.
        if contains_typevar(then_ty) or contains_typevar(else_ty):
            return else_ty if contains_typevar(then_ty) else then_ty

        self._error(
            expr,
            f"If branches have incompatible types: then-branch is "
            f"{pretty_type(then_ty)}, else-branch is "
            f"{pretty_type(else_ty)}.",
            rationale="Both branches of an if-expression must have "
                      "the same type.",
            spec_ref='Chapter 4, Section 4.8 "Conditional Expressions"',
            error_code="E301",
        )
        return then_ty  # use then-branch type as best guess

    def _check_match(self, expr: ast.MatchExpr) -> Type | None:
        """Type-check a match expression."""
        scrutinee_ty = self._synth_expr(expr.scrutinee)
        if scrutinee_ty is None:
            return None

        result_type: Type | None = None
        for arm in expr.arms:
            # Check pattern and collect bindings
            bindings = self._check_pattern(arm.pattern, scrutinee_ty)

            # Push scope with pattern bindings
            self.env.push_scope()
            for b in bindings:
                self.env.bind(b.type_name, b.resolved_type, "match")

            # Synth arm body type
            arm_ty = self._synth_expr(arm.body)
            self.env.pop_scope()

            if arm_ty is None or isinstance(arm_ty, UnknownType):
                continue

            if result_type is None or isinstance(result_type, UnknownType):
                result_type = arm_ty
            elif types_equal(result_type, NEVER):
                result_type = arm_ty
            elif not types_equal(arm_ty, NEVER):
                if contains_typevar(arm_ty) or contains_typevar(result_type):
                    # Prefer the concrete type over the TypeVar-bearing one
                    if contains_typevar(result_type) and not contains_typevar(arm_ty):
                        result_type = arm_ty
                elif not (is_subtype(arm_ty, result_type)
                          or is_subtype(result_type, arm_ty)):
                    self._error(
                        arm.body if hasattr(arm, 'body') else expr,
                        f"Match arm type {pretty_type(arm_ty)} is "
                        f"incompatible with previous arm type "
                        f"{pretty_type(result_type)}.",
                        rationale="All match arms must have the same type.",
                        spec_ref='Chapter 4, Section 4.9 "Pattern Matching"',
                        error_code="E302",
                    )

        self._check_exhaustiveness(expr, scrutinee_ty)
        return result_type or UnknownType()

    def _check_exhaustiveness(
        self, expr: ast.MatchExpr, scrutinee_ty: Type
    ) -> None:
        """Check that match arms cover all possible values of the scrutinee.

        Spec Section 4.9.2: compiler MUST verify match is exhaustive.
        Spec Section 4.9.3: compiler SHOULD warn about unreachable arms.
        """
        raw_ty = base_type(scrutinee_ty)

        # --- Unreachable arm detection ---
        catch_all_idx: int | None = None
        for i, arm in enumerate(expr.arms):
            pat = arm.pattern
            if isinstance(pat, (ast.WildcardPattern, ast.BindingPattern)):
                catch_all_idx = i
                break

        if catch_all_idx is not None:
            # Warn about arms after the catch-all
            for j in range(catch_all_idx + 1, len(expr.arms)):
                self._error(
                    expr.arms[j].pattern,
                    "Unreachable match arm: pattern after catch-all "
                    "will never match.",
                    severity="warning",
                    rationale="A wildcard or binding pattern already "
                    "matches all remaining values.",
                    fix="Remove this arm or move it before the catch-all.",
                    spec_ref='Chapter 4, Section 4.9.3 "Unreachable Arms"',
                    error_code="E310",
                )
            return  # catch-all guarantees exhaustiveness

        # --- ADT exhaustiveness ---
        if isinstance(raw_ty, AdtType):
            adt_info = self.env.data_types.get(raw_ty.name)
            if adt_info is None:
                return  # unknown ADT, can't check
            all_ctors = set(adt_info.constructors.keys())
            covered: set[str] = set()
            for arm in expr.arms:
                pat = arm.pattern
                if isinstance(pat, ast.ConstructorPattern):
                    covered.add(pat.name)
                elif isinstance(pat, ast.NullaryPattern):
                    covered.add(pat.name)
            missing = sorted(all_ctors - covered)
            if missing:
                self._error(
                    expr,
                    f"Non-exhaustive match: missing patterns for "
                    f"{', '.join(missing)}.",
                    rationale="All constructors of the matched type "
                    "must be covered.",
                    fix="Add a wildcard '_' arm or cover all cases.",
                    spec_ref='Chapter 4, Section 4.9.2 '
                    '"Exhaustiveness Checking"',
                    error_code="E311",
                )
            return

        # --- Bool exhaustiveness ---
        if isinstance(raw_ty, PrimitiveType) and raw_ty.name == "Bool":
            covered_bools: set[bool] = set()
            for arm in expr.arms:
                pat = arm.pattern
                if isinstance(pat, ast.BoolPattern):
                    covered_bools.add(pat.value)
            missing_bools = []
            if True not in covered_bools:
                missing_bools.append("true")
            if False not in covered_bools:
                missing_bools.append("false")
            if missing_bools:
                self._error(
                    expr,
                    f"Non-exhaustive match: missing patterns for "
                    f"{', '.join(missing_bools)}.",
                    rationale="Bool matches must cover both true and false.",
                    fix="Add a wildcard '_' arm or cover all cases.",
                    spec_ref='Chapter 4, Section 4.9.2 '
                    '"Exhaustiveness Checking"',
                    error_code="E312",
                )
            return

        # --- Infinite types (Int, String, Float64, Nat, etc.) ---
        # No catch-all found and type has infinite domain → non-exhaustive
        self._error(
            expr,
            "Non-exhaustive match: type has infinite domain, "
            "a wildcard '_' or binding pattern is required.",
            rationale="Matches on types with infinite values cannot "
            "enumerate all cases.",
            fix="Add a wildcard '_' arm or a binding pattern.",
            spec_ref='Chapter 4, Section 4.9.2 '
            '"Exhaustiveness Checking"',
            error_code="E313",
        )

    # -----------------------------------------------------------------
    # Patterns
    # -----------------------------------------------------------------

    def _check_pattern(self, pat: ast.Pattern,
                       expected: Type | None) -> list[Binding]:
        """Check a pattern against an expected type, return bindings."""
        if isinstance(pat, ast.ConstructorPattern):
            return self._check_ctor_pattern(pat, expected)
        if isinstance(pat, ast.NullaryPattern):
            return self._check_nullary_pattern(pat, expected)
        if isinstance(pat, ast.BindingPattern):
            return self._check_binding_pattern(pat, expected)
        if isinstance(pat, ast.WildcardPattern):
            return []
        if isinstance(pat, ast.IntPattern):
            return []
        if isinstance(pat, ast.StringPattern):
            return []
        if isinstance(pat, ast.BoolPattern):
            return []
        return []

    def _check_ctor_pattern(self, pat: ast.ConstructorPattern,
                            expected: Type | None) -> list[Binding]:
        """Check a constructor pattern."""
        ci = self.env.lookup_constructor(pat.name)
        if ci is None:
            self._error(pat, f"Unknown constructor '{pat.name}' in pattern.",
                        severity="warning", error_code="E320")
            return []

        # Infer type args from expected type
        mapping: dict[str, Type] = {}
        if (isinstance(expected, AdtType) and ci.parent_type_params
                and expected.type_args):
            for tv, arg in zip(ci.parent_type_params, expected.type_args):
                mapping[tv] = arg

        field_types = ci.field_types or ()
        if mapping:
            field_types = tuple(substitute(ft, mapping) for ft in field_types)

        if len(pat.sub_patterns) != len(field_types):
            self._error(
                pat,
                f"Constructor '{pat.name}' has {len(field_types)} field(s), "
                f"pattern has {len(pat.sub_patterns)} sub-pattern(s).",
                error_code="E321",
            )
            return []

        bindings: list[Binding] = []
        for sub_pat, field_ty in zip(pat.sub_patterns, field_types):
            bindings.extend(self._check_pattern(sub_pat, field_ty))
        return bindings

    def _check_nullary_pattern(self, pat: ast.NullaryPattern,
                               expected: Type | None) -> list[Binding]:
        """Check a nullary constructor pattern."""
        ci = self.env.lookup_constructor(pat.name)
        if ci is None:
            self._error(pat, f"Unknown constructor '{pat.name}' in pattern.",
                        severity="warning", error_code="E322")
        return []

    def _check_binding_pattern(self, pat: ast.BindingPattern,
                               expected: Type | None) -> list[Binding]:
        """Check a binding pattern (@Type)."""
        resolved = self._resolve_type(pat.type_expr)
        tname = self._type_expr_to_slot_name(pat.type_expr)
        return [Binding(tname, resolved, "match")]

    # -----------------------------------------------------------------
    # Handlers
    # -----------------------------------------------------------------

    def _check_handle(self, expr: ast.HandleExpr) -> Type | None:
        """Type-check a handler expression."""
        # Resolve the handled effect
        effect_inst = self._resolve_effect_ref(expr.effect)
        if effect_inst is None:
            return UnknownType()

        eff_info = self.env.lookup_effect(effect_inst.name)
        if eff_info is None:
            self._error(
                expr.effect,
                f"Unknown effect '{effect_inst.name}' in handler.",
                error_code="E330",
            )
            return UnknownType()

        # Build type mapping for effect type params
        mapping: dict[str, Type] = {}
        if eff_info.type_params and effect_inst.type_args:
            mapping = dict(zip(eff_info.type_params, effect_inst.type_args))

        # Check handler state
        state_type: Type | None = None
        if expr.state:
            state_type = self._resolve_type(expr.state.type_expr)
            init_type = self._synth_expr(expr.state.init_expr)
            if init_type and not isinstance(init_type, UnknownType):
                if not is_subtype(init_type, state_type):
                    self._error(
                        expr.state.init_expr,
                        f"Handler state initial value has type "
                        f"{pretty_type(init_type)}, expected "
                        f"{pretty_type(state_type)}.",
                        error_code="E331",
                    )

        # Compute handler state canonical type name (for with-clause checks)
        state_tname_outer: str | None = None
        if state_type and expr.state:
            state_tname_outer = self._type_expr_to_slot_name(
                expr.state.type_expr)

        # Check handler clauses
        for clause in expr.clauses:
            op_info = eff_info.operations.get(clause.op_name)
            if op_info is None:
                self._error(
                    clause if hasattr(clause, 'span') else expr,
                    f"Effect '{eff_info.name}' has no operation "
                    f"'{clause.op_name}'.",
                    error_code="E332",
                )
                continue

            self.env.push_scope()
            # Bind operation parameters
            op_param_types = tuple(
                substitute(p, mapping) for p in op_info.param_types)
            for param_te, param_ty in zip(clause.params, op_param_types):
                tname = self._type_expr_to_slot_name(param_te)
                self.env.bind(tname, param_ty, "handler")

            # Bind handler state if present
            if state_type:
                state_tname = self._type_expr_to_slot_name(
                    expr.state.type_expr) if expr.state else "?"
                self.env.bind(state_tname, state_type, "handler")

            # Bind resume — takes the operation's return type, returns Unit.
            # resume is only available inside handler clause bodies.
            op_return_type = substitute(op_info.return_type, mapping)
            saved_resume = self.env.functions.get("resume")
            self.env.functions["resume"] = FunctionInfo(
                name="resume",
                forall_vars=None,
                param_types=(op_return_type,),
                return_type=UNIT,
                effect=PureEffectRow(),
            )

            self._synth_expr(clause.body)

            # Type-check with clause (state update) if present
            if clause.state_update is not None:
                upd_te, upd_expr = clause.state_update
                if state_type is None:
                    self._error(
                        clause,
                        "Handler clause has 'with' state update but "
                        "handler has no state declaration.",
                        error_code="E333",
                    )
                else:
                    upd_slot = self._type_expr_to_slot_name(upd_te)
                    if upd_slot != state_tname_outer:
                        self._error(
                            clause,
                            f"State update type '{upd_slot}' does not "
                            f"match handler state type "
                            f"'{state_tname_outer}'.",
                            error_code="E334",
                        )
                    upd_type = self._synth_expr(upd_expr)
                    if (upd_type and state_type
                            and not isinstance(upd_type, UnknownType)
                            and not is_subtype(upd_type, state_type)):
                        self._error(
                            upd_expr,
                            f"State update expression has type "
                            f"{pretty_type(upd_type)}, expected "
                            f"{pretty_type(state_type)}.",
                            error_code="E335",
                        )

            # Restore previous resume binding (if any)
            if saved_resume is not None:
                self.env.functions["resume"] = saved_resume
            else:
                del self.env.functions["resume"]

            self.env.pop_scope()

        # Check handler body — temporarily add handled effect to context
        # so effect operations resolve correctly inside the body
        saved_effect = self.env.current_effect_row
        saved_ops = self._effect_ops_used

        # Add the handled effect to the current effect row
        handler_effects = frozenset({effect_inst})
        if isinstance(self.env.current_effect_row, ConcreteEffectRow):
            handler_effects = handler_effects | self.env.current_effect_row.effects
            self.env.current_effect_row = ConcreteEffectRow(
                handler_effects, self.env.current_effect_row.row_var)
        else:
            self.env.current_effect_row = ConcreteEffectRow(handler_effects)

        # Track ops used inside handler body separately (they're discharged)
        self._effect_ops_used = set()

        # Bind handler state in handler body scope too
        if state_type and expr.state:
            self.env.push_scope()
            state_tname = self._type_expr_to_slot_name(expr.state.type_expr)
            self.env.bind(state_tname, state_type, "handler")

        body_type = self._synth_expr(expr.body)

        if state_type and expr.state:
            self.env.pop_scope()

        # Restore — the handler discharges its effect
        self.env.current_effect_row = saved_effect
        self._effect_ops_used = saved_ops

        return body_type
