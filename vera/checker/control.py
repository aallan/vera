"""Control-flow, pattern, and handler type-checking mix-in."""

from __future__ import annotations

import dataclasses
from collections.abc import Mapping
from dataclasses import dataclass

from vera import ast, naming
from vera.environment import Binding, FunctionInfo
from vera.skip import STATE_CLAUSE_INLINE_DEPTH_CAP
from vera.slots import (
    bare_call_denotes_user_fn,
    family_fallback_name,
    type_expr_slot_name,
)
from vera.types import (
    BOOL,
    BYTE,
    INT,
    NAT,
    NEVER,
    STRING,
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
    pretty_inferred_type,
    state_cell_decl_equal,
    substitute,
    types_equal,
)


#: The State operations a bare or ``State.``-qualified call can name.
_STATE_OPS = frozenset({"get", "put"})


@dataclass(frozen=True)
class _ClauseCell:
    """The State cell a ``get``/``put`` reaches, as code generation sees it.

    ``family`` is the cell's identity (:func:`vera.naming.family_name`, the
    name code generation's host intrinsics are keyed by); ``clauses`` the
    reaching handler's clauses, empty for a cell of the declared row; and
    ``scope`` the handler's DECLARATION-time scope, which a clause body is
    resolved in when code generation inlines it (#1211).
    """

    family: str
    base: str
    clauses: Mapping[str, ast.HandlerClause]
    scope: _OpScope | None


@dataclass(frozen=True)
class _OpScope:
    """Which cell each State operation reaches here, and from which index of
    the pushed-cell stack the cells are this scope's own (#1233)."""

    cells: Mapping[str, _ClauseCell]
    addressable_from: int


@dataclass
class _ClauseWalk:
    """One E339 walk's results, and the clause inlinings it has walked.

    An inlining is keyed by the clause, the scope it resolves in, the cells
    pushed and the depth: under the same key the clause body reaches the
    same operations, so it is walked once rather than once per path to it
    (a nest whose clauses each perform *k* operations has ``k ** depth``).
    Each key's clause and scope are held here, so no id in a key is reused
    while the walk runs.
    """

    refused: list[tuple[ast.Node, str, _ClauseCell]]
    inlined: dict[
        tuple[int, int, tuple[str, ...], int],
        tuple[ast.HandlerClause, _OpScope],
    ]


# #1315: the built-in ADTs that carry no constructors — the containers
# `_resolve_named_type` builds directly rather than from a `data`
# declaration.  Their absence from `env.data_types` is what let a
# constructor pattern over one through: it reads as "type not registered"
# to a lookup that cannot tell the two apart.  A user `data Array { ... }`
# registers the name, and is then ruled on as the declared ADT it is.
_CONSTRUCTORLESS_BUILTIN_TYPES = frozenset(
    {"Array", "Map", "Set", "Tuple", "Decimal"}
)

# #1320: what each literal pattern form can be compared against — the
# types whose values an integer / string / boolean literal can equal.
# Every integer type is admitted, `Byte` included: the rule refuses what
# can never match, and a `Byte` is an integer 0..255 that an integer
# literal can name.  `Float64` is not an integer type and the grammar has
# no float literal pattern, so a `Float64` scrutinee is matched by a
# wildcard or a binding pattern.
_LITERAL_PATTERN_TYPES: dict[type, tuple[str, tuple[Type, ...]]] = {
    ast.IntPattern: ("Int", (INT, NAT, BYTE)),
    ast.StringPattern: ("String", (STRING,)),
    ast.BoolPattern: ("Bool", (BOOL,)),
}


def _render_literal_pattern(pat: ast.Pattern) -> str:
    """The literal as written, for the E314 instruction."""
    if isinstance(pat, ast.StringPattern):
        return f'"{pat.value}"'
    if isinstance(pat, ast.BoolPattern):
        return "true" if pat.value else "false"
    if isinstance(pat, ast.IntPattern):
        return str(pat.value)
    return "<literal>"  # pragma: no cover — only literal forms reach here


class ControlFlowMixin:

    # -----------------------------------------------------------------
    # Control flow
    # -----------------------------------------------------------------

    def _check_if(self, expr: ast.IfExpr, *,
                  expected: Type | None = None) -> Type | None:
        """Type-check if-then-else."""
        cond_ty = self._synth_expr(expr.condition)
        if cond_ty and not isinstance(cond_ty, UnknownType):
            if not is_subtype(base_type(cond_ty), BOOL):
                self._error(
                    expr.condition,
                    f"If condition must be Bool, found "
                    f"{pretty_inferred_type(cond_ty)}.",
                    rationale="The condition of an if-expression must have "
                              "type Bool.",
                    fix="Replace the condition with a Bool-typed expression, "
                        "e.g. a comparison: if @Int.0 > 0 { ... } else { ... }.",
                    spec_ref='Chapter 4, Section 4.8 "Conditional Expressions"',
                    error_code="E300",
                )

        then_ty = self._synth_expr(expr.then_branch, expected=expected)
        else_ty = self._synth_expr(expr.else_branch, expected=expected)

        if then_ty is None or else_ty is None:  # pragma: no cover — defensive: _synth_expr returns UnknownType, not None
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
        if is_subtype(else_ty, then_ty):  # pragma: no cover — subtyping is symmetric for current rules
            return then_ty

        # Re-synthesis fallback: if one branch has unresolved TypeVars,
        # re-synth it with the concrete branch as expected.
        if contains_typevar(then_ty) and not contains_typevar(else_ty):  # pragma: no cover — requires unresolved TypeVar in branch
            then_ty = self._synth_expr(
                expr.then_branch, expected=else_ty)
            if then_ty and is_subtype(then_ty, else_ty):
                return else_ty
        elif contains_typevar(else_ty) and not contains_typevar(then_ty):  # pragma: no cover
            else_ty = self._synth_expr(
                expr.else_branch, expected=then_ty)
            if else_ty and is_subtype(else_ty, then_ty):
                return then_ty
        elif contains_typevar(then_ty) and contains_typevar(else_ty):  # pragma: no cover
            # Both have TypeVars — pick either (both unresolved)
            return then_ty

        self._error(
            expr,
            f"If branches have incompatible types: then-branch is "
            f"{pretty_inferred_type(then_ty)}, else-branch is "
            f"{pretty_inferred_type(else_ty)}.",
            rationale="Both branches of an if-expression must have "
                      "the same type.",
            fix=f"Make both branches produce the same type: convert one "
                f"branch to {pretty_inferred_type(else_ty)} (or both to a "
                f"common type), so then and else agree.",
            spec_ref='Chapter 4, Section 4.8 "Conditional Expressions"',
            error_code="E301",
        )
        return then_ty  # use then-branch type as best guess

    def _check_match(self, expr: ast.MatchExpr, *,
                     expected: Type | None = None) -> Type | None:
        """Type-check a match expression."""
        for arm in expr.arms:
            self._register_arm_pattern_reads(expr.scrutinee, arm.pattern)
        scrutinee_ty = self._synth_expr(expr.scrutinee)
        if scrutinee_ty is None:  # pragma: no cover — defensive: _synth_expr returns UnknownType, not None
            return None

        result_type: Type | None = None
        for arm in expr.arms:
            # Check pattern and collect bindings
            bindings = self._check_pattern(arm.pattern, scrutinee_ty)

            # Push scope with pattern bindings
            self.env.push_scope()
            for b in bindings:
                self.env.bind(b.type_name, b.resolved_type, "match")

            # Synth arm body type (pass expected for bidirectional)
            arm_ty = self._synth_expr(arm.body, expected=expected)
            self.env.pop_scope()

            if arm_ty is None or isinstance(arm_ty, UnknownType):
                continue

            if result_type is None or isinstance(result_type, UnknownType):
                result_type = arm_ty
            elif types_equal(result_type, NEVER):
                result_type = arm_ty
            elif not types_equal(arm_ty, NEVER):
                # Re-synthesis fallback for unresolved TypeVars
                if contains_typevar(arm_ty) and not contains_typevar(result_type):  # pragma: no cover — requires unresolved TypeVar in arm
                    arm_ty = self._synth_expr(
                        arm.body, expected=result_type)
                    if arm_ty is None or isinstance(arm_ty, UnknownType):
                        continue
                elif contains_typevar(result_type) and not contains_typevar(arm_ty):  # pragma: no cover
                    result_type = arm_ty
                    continue

                if not (is_subtype(arm_ty, result_type)
                        or is_subtype(result_type, arm_ty)):
                    self._error(
                        arm.body if hasattr(arm, 'body') else expr,
                        f"Match arm type {pretty_type(arm_ty)} is "
                        f"incompatible with previous arm type "
                        f"{pretty_type(result_type)}.",
                        rationale="All match arms must have the same type.",
                        fix=f"Make this arm produce {pretty_type(result_type)} "
                            f"to match the other arms (or change every arm to "
                            f"a common type).",
                        spec_ref='Chapter 4, Section 4.9 "Match Expressions"',
                        error_code="E302",
                    )

        # #1497: a match naming a refused declaration's constructor was
        # written against that declaration, so its coverage is not judged.
        if not (self._refused_ctor_names and any(
                self._names_refused_ctor(arm.pattern) for arm in expr.arms)):
            self._check_exhaustiveness(expr, scrutinee_ty)
        return result_type or UnknownType()

    def _names_refused_ctor(self, pat: ast.Pattern) -> bool:
        """Whether *pat* names a constructor of a refused declaration.

        Only a name nothing registered answers: a refused `data Int
        { Some(Bool) }` leaves the prelude's `Some` resolvable, and a match
        on it must still be judged for coverage — the guard the pattern and
        call sites apply too.
        """
        if isinstance(pat, (ast.NullaryPattern, ast.ConstructorPattern)) and (
                pat.name in self._refused_ctor_names
                and self.env.lookup_constructor(pat.name) is None):
            return True
        if isinstance(pat, ast.ConstructorPattern):
            return any(
                self._names_refused_ctor(sub) for sub in pat.sub_patterns)
        return False

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
                    spec_ref='Chapter 4, Section 4.9.3 "Redundancy"',
                    error_code="E310",
                )
            return  # catch-all guarantees exhaustiveness

        # --- ADT exhaustiveness ---
        if isinstance(raw_ty, AdtType):
            # #1513: a type this file does not import is judged by its own
            # declaration, as its constructors are resolved by it.
            adt_info = (self.env.data_types.get(raw_ty.name)
                        or self._stranger_data_type(raw_ty.name))
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
                    spec_ref='Chapter 4, Section 4.9.2 "Exhaustiveness"',
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
                    spec_ref='Chapter 4, Section 4.9.2 "Exhaustiveness"',
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
            spec_ref='Chapter 4, Section 4.9.2 "Exhaustiveness"',
            error_code="E313",
        )

    # -----------------------------------------------------------------
    # Patterns
    # -----------------------------------------------------------------

    def _check_pattern(self, pat: ast.Pattern,
                       expected: Type | None) -> list[Binding]:
        """Check a pattern against an expected type, return bindings."""
        # #1315/#1320: every form is first asked whether it can match the
        # scrutinee at all.  A binding pattern is the exception only in
        # WHERE the same rule runs: its type has to be resolved before it
        # can be compared, resolution reports its own diagnostics (E133,
        # …), and resolving twice would duplicate them — so
        # `_check_binding_pattern` applies the rule with the type it has
        # already resolved.
        if isinstance(pat, ast.BindingPattern):
            return self._check_binding_pattern(pat, expected)
        if self._check_pattern_scrutinee(pat, expected):
            # The head cannot match, so the scrutinee's type arguments say
            # nothing about this constructor's fields: check sub-patterns
            # without them rather than reporting a second mismatch derived
            # from a type this pattern never sees.
            expected = None
        if isinstance(pat, ast.ConstructorPattern):
            return self._check_ctor_pattern(pat, expected)
        if isinstance(pat, ast.NullaryPattern):
            return self._check_nullary_pattern(pat, expected)
        if isinstance(pat, ast.WildcardPattern):
            return []
        if isinstance(pat, ast.IntPattern):
            return []
        if isinstance(pat, ast.StringPattern):
            return []
        if isinstance(pat, ast.BoolPattern):
            return []
        return []  # pragma: no cover — exhaustive isinstance chain above

    # -----------------------------------------------------------------
    # Pattern / scrutinee agreement (#1315, #1320)
    # -----------------------------------------------------------------

    def _scrutinee_for_pattern(self, expected: Type | None) -> Type | None:
        """The type a pattern must be able to match, or None to skip.

        Skipped wherever the question is not decidable from what this
        checker knows:

        * no expected type — a sub-pattern of a `Tuple` whose arity the
          expected type does not supply;
        * an unresolved scrutinee (`UnknownType`), or a `Never` one;
        * a type variable — the deliberate boundary.  A `forall<T>` body
          cannot decide `Some(@Int)` over `@T.0`, because `T` may be
          instantiated at `Option<Int>`.  Only the HEAD has to be known:
          `Map<T, U>` from `map_new()` still decides every pattern whose
          answer depends on the head alone;
        * a named type the checker does not know — #1315's own
          distinction between "not registered" (an unresolved import's
          type: stay quiet, as the exhaustiveness pass does) and
          "registered as a constructor-less built-in" (`Array`, `Map`,
          `Set`, `Tuple`, `Decimal`: rule on it).

        A refinement wrapper is stripped: `{ @Int | ... }` is matched by
        exactly the patterns `Int` is.
        """
        if expected is None:
            return None
        scrut = base_type(expected)  # refinements do not change matchability
        if isinstance(scrut, UnknownType) or types_equal(scrut, NEVER):
            return None
        if isinstance(scrut, PrimitiveType):
            return scrut
        if isinstance(scrut, AdtType) and (
                scrut.name in self.env.data_types
                or scrut.name in _CONSTRUCTORLESS_BUILTIN_TYPES
                # #1513: a type this file does not import, whose own
                # declaration types the constructors a pattern names.
                or self._stranger_data_type(scrut.name) is not None):
            return scrut
        return None

    def _check_pattern_scrutinee(
        self, pat: ast.Pattern, expected: Type | None,
        *, bound: Type | None = None,
    ) -> bool:
        """Report E314 when *pat* cannot match a value of *expected*.

        One rule over every pattern form (#1320), of which the
        constructor-over-a-container case (#1315) is the instance the
        containers make visible: `Array`, `Map` and `Set` are `AdtType`s
        with no entry in the constructor registry, so `Some(...)` over one
        cleared exhaustiveness ("unknown ADT, can't check") with nothing
        else to object.  A literal pattern had no comparison at all.

        Returns True when a mismatch was reported.  *bound* carries a
        binding pattern's already-resolved type (see `_check_pattern`).
        """
        scrut = self._scrutinee_for_pattern(expected)
        if scrut is None:
            return False

        if isinstance(pat, ast.BindingPattern):
            # A binder's relatedness reads the type ARGUMENTS, not just the
            # head, so an unresolved variable anywhere in either type makes
            # the comparison undecidable here.
            if (bound is None or isinstance(bound, UnknownType)
                    or contains_typevar(bound) or contains_typevar(scrut)):
                return False
            # Relatedness in EITHER direction, not equality: `@Int` over a
            # `Nat` scrutinee widens, and `@Nat` over an `Int` scrutinee is
            # the verifier's narrowing obligation (E503), not a type error.
            base_bound = base_type(bound)
            if (is_subtype(scrut, base_bound)
                    or is_subtype(base_bound, scrut)):
                return False
            return self._pattern_mismatch(
                pat, f"Binding pattern '@{pretty_type(bound)}'",
                f"binds a value of type {pretty_type(bound)}", scrut,
            )

        if isinstance(pat, ast.ConstructorPattern) and pat.name == "Tuple":
            if isinstance(scrut, AdtType) and scrut.name == "Tuple":
                # The variadic Tuple carrier has no registry entry, so the
                # E321 field-count rule never sees it: a pattern with the
                # wrong number of sub-patterns bound the components it did
                # name POSITIONALLY, whatever their types.
                width = len(scrut.type_args)
                got = len(pat.sub_patterns)
                if not width or width == got:
                    return False
                return self._pattern_mismatch(
                    pat, f"Pattern 'Tuple' with {got} sub-pattern(s)",
                    f"matches a tuple of {got} component(s)", scrut,
                    fix=f"Give the pattern one sub-pattern per component "
                        f"of {pretty_type(scrut)} ({width}), or match the "
                        f"scrutinee with a wildcard '_'.",
                )
            return self._pattern_mismatch(
                pat, "Pattern 'Tuple(...)'", "matches a tuple", scrut,
            )

        if isinstance(pat, (ast.ConstructorPattern, ast.NullaryPattern)):
            ci = self.env.lookup_constructor(pat.name)
            if ci is None and pat.name not in self._refused_ctor_names:
                # #1513: a constructor of a type this file does not import
                # is typed by its own declaration, so one of another type
                # cannot match this scrutinee here either.
                _candidates, ci = self._stranger_constructor(pat.name)
            if ci is None:
                return False  # E320/E322 own an unknown constructor name
            if isinstance(scrut, AdtType) and scrut.name == ci.parent_type:
                return False
            owner = ci.parent_type
            if ci.parent_type_params:
                owner += f"<{', '.join(ci.parent_type_params)}>"
            return self._pattern_mismatch(
                pat, f"Pattern '{pat.name}'",
                f"is a constructor of {owner}", scrut,
            )

        literal = _LITERAL_PATTERN_TYPES.get(type(pat))
        if literal is None:
            return False  # wildcard — matches every type
        lit_name, accepts = literal
        if any(types_equal(scrut, ok) for ok in accepts):
            return False
        return self._pattern_mismatch(
            pat, f"Pattern literal {_render_literal_pattern(pat)}",
            f"has type {lit_name}", scrut,
        )

    def _pattern_mismatch(
        self, pat: ast.Pattern, subject: str, matches: str, scrut: Type,
        *, fix: str | None = None,
    ) -> bool:
        """Emit E314 for *pat* against the scrutinee type *scrut*."""
        scrut_name = pretty_type(scrut)
        alternatives = [f"a binding pattern '@{scrut_name}'", "a wildcard '_'"]
        if isinstance(scrut, AdtType):
            info = (self.env.data_types.get(scrut.name)
                    or self._stranger_data_type(scrut.name))
            if info is not None and info.constructors:
                ctors = ", ".join(sorted(info.constructors))
                alternatives.insert(0, f"a constructor of {scrut_name} "
                                       f"({ctors})")
        self._error(
            pat,
            f"{subject} {matches}, but the scrutinee has type "
            f"{scrut_name}.",
            rationale="Every value reaching a match arm has the "
                      "scrutinee's type, so a pattern of any other type "
                      "can never be taken — the arm is dead code the "
                      "backend has no way to lower.",
            fix=fix or (
                f"Match a {scrut_name} scrutinee with "
                f"{' or '.join(alternatives)}, or match a scrutinee this "
                f"pattern can take."
            ),
            spec_ref='Chapter 4, Section 4.9.1 "Patterns"',
            error_code="E314",
        )
        return True

    def _check_ctor_pattern(self, pat: ast.ConstructorPattern,
                            expected: Type | None) -> list[Binding]:
        """Check a constructor pattern."""
        # Tuple is variadic — derive field types from sub-pattern bindings
        if pat.name == "Tuple":
            return self._check_tuple_pattern(pat, expected)

        ci = self.env.lookup_constructor(pat.name)
        if ci is None and pat.name in self._refused_ctor_names:
            # #1497: a constructor of a declaration refused as E158.  Its
            # E158 is the one error the program owes, so the sub-patterns
            # bind quietly and nothing more is reported here.
            refused: list[Binding] = []
            for sub_pat in pat.sub_patterns:
                refused.extend(self._check_pattern(sub_pat, UnknownType()))
            return refused
        if ci is None:
            # #1513: a constructor of a type this file does not import is
            # resolved as a construction of it is — a warning naming the
            # import where the name denotes one declaration, which then
            # types the pattern's fields below.
            candidates, ci = self._stranger_constructor(pat.name)
            if ci is not None:
                message, fix = self._stranger_ctor_message(
                    pat.name, ci, candidates)
                self._error(
                    pat, message,
                    rationale=self._STRANGER_CTOR_RATIONALE,
                    fix=fix,
                    severity="warning",
                    spec_ref='Chapter 8, Section 8.5.4 '
                             '"Constructor Resolution"',
                    error_code="E320",
                )
        if ci is None:
            # An error (#1513): the arm names no constructor, so it has no
            # tag to test and cannot be compiled.
            self._error(
                pat,
                f"Unknown constructor '{pat.name}' in pattern.",
                rationale="A constructor pattern must name a constructor "
                          "declared by a data type in scope; no such "
                          "constructor is defined or imported, so the arm "
                          "cannot be compiled.",
                fix=self._unknown_ctor_fix(pat.name, candidates),
                spec_ref='Chapter 2, Section 2.4 '
                         '"Algebraic Data Types (ADTs)"',
                error_code="E320",
            )
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
                rationale="A constructor pattern must supply exactly one "
                          "sub-pattern per field of the constructor.",
                fix=f"Give '{pat.name}' exactly {len(field_types)} "
                    f"sub-pattern(s), one per field, e.g. "
                    f"{pat.name}({', '.join('@T' for _ in field_types)}).",
                spec_ref='Chapter 4, Section 4.9.1 "Patterns"',
                error_code="E321",
            )
            return []

        bindings: list[Binding] = []
        for sub_pat, field_ty in zip(pat.sub_patterns, field_types):
            bindings.extend(self._check_pattern(sub_pat, field_ty))
        return bindings

    def _check_tuple_pattern(
        self, pat: ast.ConstructorPattern, expected: Type | None,
    ) -> list[Binding]:
        """Check a variadic Tuple constructor pattern."""
        if not pat.sub_patterns:  # pragma: no cover — parser rejects empty Tuple()
            self._error(
                pat,
                "Tuple pattern requires at least one field.",
                rationale="A tuple type has at least one component, so a "
                          "Tuple pattern must contain at least one "
                          "sub-pattern.",
                fix="Add one sub-pattern per tuple component, e.g. "
                    "Tuple(@Int, @Bool) for a two-element tuple.",
                spec_ref='Chapter 2, Section 2.3.1 "Tuple Types"',
                error_code="E323",
            )
            return []
        # Derive field types from expected Tuple type if available
        field_types: tuple[Type | None, ...] = (None,) * len(pat.sub_patterns)
        if (isinstance(expected, AdtType) and expected.name == "Tuple"
                and len(expected.type_args) == len(pat.sub_patterns)):
            field_types = expected.type_args
        bindings: list[Binding] = []
        for sub_pat, field_ty in zip(pat.sub_patterns, field_types):
            bindings.extend(self._check_pattern(sub_pat, field_ty))
        return bindings

    def _check_nullary_pattern(self, pat: ast.NullaryPattern,
                               expected: Type | None) -> list[Binding]:
        """Check a nullary constructor pattern."""
        ci = self.env.lookup_constructor(pat.name)
        if ci is None and pat.name in self._refused_ctor_names:
            return []  # #1497: see `_check_ctor_pattern`
        if ci is None:
            # #1513: see `_check_ctor_pattern`.
            candidates, ci = self._stranger_constructor(pat.name)
            if ci is not None:
                message, fix = self._stranger_ctor_message(
                    pat.name, ci, candidates)
                self._error(
                    pat, message,
                    rationale=self._STRANGER_CTOR_RATIONALE,
                    fix=fix,
                    severity="warning",
                    spec_ref='Chapter 8, Section 8.5.4 '
                             '"Constructor Resolution"',
                    error_code="E322",
                )
        if ci is None:
            # An error (#1513); see `_check_ctor_pattern`.
            self._error(
                pat,
                f"Unknown constructor '{pat.name}' in pattern.",
                rationale="A nullary pattern must name a no-field "
                          "constructor declared by a data type in scope; no "
                          "such constructor is defined or imported, so the "
                          "arm cannot be compiled.",
                fix=self._unknown_ctor_fix(pat.name, candidates),
                spec_ref='Chapter 2, Section 2.4 '
                         '"Algebraic Data Types (ADTs)"',
                error_code="E322",
            )
        return []

    def _check_binding_pattern(self, pat: ast.BindingPattern,
                               expected: Type | None) -> list[Binding]:
        """Check a binding pattern (@Type)."""
        self._check_refinement_predicates(pat.type_expr)  # #861
        resolved = self._resolve_type(pat.type_expr)
        # #1320: the pattern/scrutinee rule, applied here because the
        # binder's type is resolved exactly once (see `_check_pattern`).
        self._check_pattern_scrutinee(pat, expected, bound=resolved)
        tname = self._type_expr_to_slot_name(pat.type_expr)
        return [Binding(tname, resolved, "match")]

    # -----------------------------------------------------------------
    # Handlers
    # -----------------------------------------------------------------

    def _check_handle(self, expr: ast.HandleExpr) -> Type | None:
        """Type-check a handler expression."""
        # Resolve the handled effect
        effect_inst = self._resolve_effect_ref(expr.effect)
        if effect_inst is None:  # pragma: no cover — parser always produces EffectRef
            return UnknownType()

        eff_info = self.env.lookup_effect(effect_inst.name)
        if eff_info is None:
            self._error(
                expr.effect,
                f"Unknown effect '{effect_inst.name}' in handler.",
                rationale="A handler must name an effect that has been "
                          "declared with an 'effect' declaration.",
                fix=f"Declare '{effect_inst.name}' with an effect "
                    f"declaration (effect {effect_inst.name} {{ op ...; }}) "
                    f"or handle an effect that is in scope.",
                spec_ref='Chapter 7, Section 7.5 "Effect Handlers"',
                error_code="E330",
            )
            return UnknownType()

        # #1202 adversarial round (F4): the parameterized BUILTIN effects
        # take exactly one type argument — `handle[State<Int, Nat>]` and
        # bare `handle[State]` previously sailed through check (the zip
        # below truncates; a missing arg leaked an unresolved TypeVar into
        # downstream diagnostics) and died at codegen with E602/E121.
        # Check-green ⇒ compilable: reject the arity here.  User-declared
        # effects are untouched (their arity is their declaration's).
        if (effect_inst.name in ("State", "Exn")
                and isinstance(expr.effect, ast.EffectRef)
                and len(expr.effect.type_args or []) != 1):
            got = len(expr.effect.type_args or [])
            self._error(
                expr.effect,
                f"handle[{effect_inst.name}] requires exactly one type "
                f"argument (got {got}).",
                rationale=f"The builtin {effect_inst.name} effect is "
                          f"parameterized by exactly one type — "
                          f"{effect_inst.name}<T> — which types its "
                          f"operations and, for State, the handler's "
                          f"state cell.",
                fix=f"Write handle[{effect_inst.name}<T>](...) with a "
                    f"single concrete type argument, e.g. "
                    f"handle[State<Int>](@Int = 0) {{ ... }}.",
                spec_ref='Chapter 7, Section 7.5.1 "Handler Syntax"',
                error_code="E337",
            )
            return UnknownType()

        # Build type mapping for effect type params
        mapping: dict[str, Type] = {}
        if eff_info.type_params and effect_inst.type_args:
            mapping = dict(zip(eff_info.type_params, effect_inst.type_args))

        # Check handler state
        state_type: Type | None = None
        if expr.state:
            self._check_refinement_predicates(expr.state.type_expr)  # #861
            state_type = self._resolve_type(expr.state.type_expr)
            # #993: synth WITH the declared state type as expected — a bare
            # nullary constructor init (`@Option<Int> = None`) mints a fresh
            # ctor var without it, and the #971 bidirectional fill needs the
            # expected type to adopt the declared type arguments.
            init_type = self._synth_expr(
                expr.state.init_expr, expected=state_type)
            if init_type and not isinstance(init_type, UnknownType):
                if not is_subtype(init_type, state_type):
                    self._error(
                        expr.state.init_expr,
                        f"Handler state initial value has type "
                        f"{pretty_inferred_type(init_type)}, expected "
                        f"{pretty_type(state_type)}.",
                        rationale="A handler's initial state value must have "
                                  "the declared handler state type.",
                        fix=f"Provide an initial value of type "
                            f"{pretty_type(state_type)}, e.g. "
                            f"handle[Eff](@{pretty_type(state_type)} = "
                            f"<value>) {{ ... }}.",
                        spec_ref='Chapter 7, Section 7.5.1 "Handler Syntax"',
                        error_code="E331",
                    )

            # #1206: for the builtin State effect the declared state IS the
            # State<T> cell — obligations and codegen guards key off T
            # (#1203), so a divergent declared type is documentation that
            # lies about what the cell holds.  Structural equality of the
            # RESOLVED types is the test (`is_subtype` is deliberately
            # blind here: Int <: Nat both ways by rule 3b, and refinements
            # erase to their bases by rules 5–7): aliases of T are equal
            # after resolution and stay accepted; Int-for-Nat and
            # refinement-decorated declarations are rejected.  TypeVar
            # anywhere on either side defers to instantiation (the E128
            # lesson: a generic shape whose instantiations are fine must
            # not die at the generic site).
            if (effect_inst.name == "State"
                    and isinstance(expr.effect, ast.EffectRef)
                    and expr.effect.type_args
                    and len(expr.effect.type_args) == 1
                    and state_type is not None
                    and not isinstance(state_type, UnknownType)):
                cell_type = self._resolve_type(expr.effect.type_args[0])
                if (not isinstance(cell_type, UnknownType)
                        and not contains_typevar(cell_type)
                        and not contains_typevar(state_type)
                        and not state_cell_decl_equal(
                            cell_type, state_type)):
                    self._error(
                        expr.state.type_expr,
                        f"Handler state is declared "
                        f"@{pretty_type(state_type)} but the handled "
                        f"effect's cell type is "
                        f"State<{pretty_type(cell_type)}>.",
                        rationale="For the builtin State effect the "
                                  "handler state declaration IS the "
                                  "State<T> cell: verification "
                                  "obligations and runtime guards key "
                                  "off T, so a divergent declared type "
                                  "is documentation that lies about "
                                  "what the cell holds.",
                        fix=f"Declare the state as "
                            f"@{pretty_type(cell_type)} (an alias that "
                            f"resolves to it is fine), and express any "
                            f"refinement in the effect's State<T> "
                            f"argument itself via a NAMED refinement "
                            f"alias — type Small = {{ @Nat | ... }}; "
                            f"handle[State<Small>](@Small = ...) — an "
                            f"inline refinement literal in the State<T> "
                            f"argument is not compilable.",
                        spec_ref='Chapter 7, Section 7.5.1 '
                                 '"Handler Syntax"',
                        error_code="E336",
                    )

        # Compute handler state canonical type name (for with-clause checks)
        state_tname_outer: str | None = None
        if state_type and expr.state:
            state_tname_outer = self._type_expr_to_slot_name(
                expr.state.type_expr)

        # #973 hint hygiene: while checking CLAUSES, no enclosing handled
        # body's state-type hint may apply — clauses legitimately bind state
        # as a slot, so a failed resolution there is an ordinary E130 (bad
        # index), not a "use get(())" case.  A nested handle expression is
        # checked mid-body-walk, so the outer body's hint is masked here and
        # restored before this handler's own body check below.
        saved_body_hints = self._handler_body_state_tnames
        self._handler_body_state_tnames = []

        # Check handler clauses
        first_clauses: dict[str, ast.HandlerClause] = {}
        for clause in expr.clauses:
            # #1433: a handler is a namespace of clauses, one per operation.
            # Two clauses for one operation compiled to a handler that ran
            # the LATER one whenever the body performed it — a choice made by
            # clause order, which the program does not state.  The surplus
            # is refused, and its body not checked.
            first_clause = first_clauses.setdefault(clause.op_name, clause)
            if first_clause is not clause:
                self._report_duplicate_name(
                    clause, noun="handler clause", name=clause.op_name,
                    scope="this handler", first=first_clause,
                    fix=(
                        f"Delete this clause, or merge the two into the one "
                        f"clause for '{clause.op_name}': each operation has "
                        f"exactly one clause in a handler."
                    ),
                )
                # Refused like a surplus declaration, so the call graph
                # reads none of its calls either (#1492).
                self._refused_decl_ids.add(id(clause))
                continue
            op_info = eff_info.operations.get(clause.op_name)
            if op_info is None:
                self._error(
                    clause if hasattr(clause, 'span') else expr,
                    f"Effect '{eff_info.name}' has no operation "
                    f"'{clause.op_name}'.",
                    rationale="Each handler clause must implement an "
                              "operation declared by the handled effect.",
                    fix=f"Rename the clause to one of '{eff_info.name}'s "
                        f"declared operations "
                        f"({', '.join(sorted(eff_info.operations)) or 'none'})"
                        f", or add 'op {clause.op_name}(...)' to the effect "
                        f"declaration.",
                    spec_ref='Chapter 7, Section 7.5.1 "Handler Syntax"',
                    error_code="E332",
                )
                continue

            self.env.push_scope()
            # Bind operation parameters
            op_param_types = tuple(
                substitute(p, mapping) for p in op_info.param_types)
            for param_te, param_ty in zip(clause.params, op_param_types):
                self._check_refinement_predicates(param_te)  # #861
                # #1489: the declared type is otherwise only RENDERED here,
                # for the slot it binds, so a name in it that nothing
                # declares was never reported.  Resolved for its
                # diagnostics; the binding takes the operation's type.
                self._resolve_type(param_te)
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
                self._check_refinement_predicates(upd_te)  # #861
                if state_type is None:
                    self._error(
                        clause,
                        "Handler clause has 'with' state update but "
                        "handler has no state declaration.",
                        rationale="A 'with' state update may only appear in a "
                                  "handler that declares state to update.",
                        fix="Declare handler state, e.g. "
                            "handle[Eff](@Int = 0) { ... }, or remove the "
                            "'with' clause from this operation.",
                        spec_ref='Chapter 7, Section 7.5.2 '
                                 '"Handler Semantics"',
                        error_code="E333",
                    )
                else:
                    # #1489: resolved for its diagnostics, as the clause
                    # parameters above are — only rendered, an unknown name
                    # drew nothing but the E334 mismatch below.
                    self._resolve_type(upd_te)
                    upd_slot = self._type_expr_to_slot_name(upd_te)
                    if upd_slot != state_tname_outer:
                        self._error(
                            clause,
                            f"State update type '{upd_slot}' does not "
                            f"match handler state type "
                            f"'{state_tname_outer}'.",
                            rationale="A 'with' state update must target the "
                                      "handler's declared state type.",
                            fix=f"Update the declared state type instead: "
                                f"with @{state_tname_outer} = <expr>.",
                            spec_ref='Chapter 7, Section 7.5.2 '
                                     '"Handler Semantics"',
                            error_code="E334",
                        )
                    # Synth WITH the declared state type as expected —
                    # the same #993 bidirectional threading the state
                    # INIT got: without it a byte-width literal
                    # (`with @Byte = 77`) synthesized as Nat and E335'd
                    # while the identical literal was accepted at init,
                    # put arguments, and resume values (round-3 review:
                    # the coercion inconsistency made codegen's
                    # with-update Byte arm unreachable from check-green
                    # source).
                    upd_type = self._synth_expr(
                        upd_expr, expected=state_type)
                    if (upd_type and state_type
                            and not isinstance(upd_type, UnknownType)
                            and not is_subtype(upd_type, state_type)):
                        self._error(
                            upd_expr,
                            f"State update expression has type "
                            f"{pretty_inferred_type(upd_type)}, expected "
                            f"{pretty_type(state_type)}.",
                            rationale="The value assigned by a 'with' state "
                                      "update must have the handler's declared "
                                      "state type.",
                            fix=f"Make the update expression evaluate to "
                                f"{pretty_type(state_type)} (convert it or use "
                                f"a {pretty_type(state_type)}-typed value).",
                            spec_ref='Chapter 7, Section 7.5.2 '
                                     '"Handler Semantics"',
                            error_code="E335",
                        )

            # Restore previous resume binding (if any)
            if saved_resume is not None:
                self.env.functions["resume"] = saved_resume
            else:
                del self.env.functions["resume"]

            self.env.pop_scope()

        self._handler_body_state_tnames = saved_body_hints

        # Check handler body — temporarily add handled effect to context
        # so effect operations resolve correctly inside the body
        saved_effect = self.env.current_effect_row
        saved_effect_order = self.env.current_effect_order
        saved_ops = self._effect_ops_used

        # Add the handled effect to the current effect row
        handler_effects = frozenset({effect_inst})
        if isinstance(self.env.current_effect_row, ConcreteEffectRow):
            handler_effects = handler_effects | self.env.current_effect_row.effects
            self.env.current_effect_row = ConcreteEffectRow(
                handler_effects, self.env.current_effect_row.row_var)
        else:
            self.env.current_effect_row = ConcreteEffectRow(handler_effects)
        # #1215: this handler goes to the FRONT of the resolution order, so a
        # bare op name declared both by this effect and by something already
        # in the row binds THIS one inside the body — the innermost handler
        # governs, exactly as `_effect_type_mapping` resolves an op's type
        # arguments against the innermost enclosing handler (§7.5.2).  The
        # rest of the order is preserved, so the enclosing handlers and then
        # the function's declared row follow in their own order.  Note the
        # CLAUSE bodies are checked above, outside this scope: a bare op in a
        # clause body resolves against the ENCLOSING context, not this
        # handler (§7.5.2, the rule codegen mirrors for #1211).
        self.env.current_effect_order = (
            effect_inst,
            *(e for e in saved_effect_order if e != effect_inst),
        )

        # Track ops used inside handler body separately (they're discharged)
        self._effect_ops_used = set()

        # #973: the handled body does NOT get a state slot.  State is reached
        # only through the typed get(())/put(...) operations — spec §7.5 scopes
        # state to handler CLAUSES, and both backends agree (codegen routes
        # state through host-side cells and gives the body no local; the
        # verifier consumes no body-scope state ref).  Binding state here
        # implied a scope the backends never provide, so a body @T.n slot read
        # passed check + verify then crashed compile with a dangling-slot E699.
        # Instead of binding, record the state's type name so a failed slot
        # resolution of that type inside the body carries a get(()) hint.
        pushed_state_hint = False
        if state_type and expr.state and state_tname_outer is not None:
            self._handler_body_state_tnames.append(state_tname_outer)
            pushed_state_hint = True

        # #1148: mark this effect handled while the body is checked, so a bare
        # op call to it in the body is accepted (codegen rewrites it to the
        # handler clause).  A bare op call to a non-State/Exn effect NOT in this
        # stack is E217 (the bare-call path in calls.py), because codegen cannot
        # route it to the host.
        self._handled_effects.append(effect_inst.name)
        self._handled_effect_insts.append(effect_inst)
        body_type = self._synth_expr(expr.body)
        self._handled_effect_insts.pop()
        self._handled_effects.pop()

        if pushed_state_hint:
            self._handler_body_state_tnames.pop()

        # Restore — the handler discharges its effect
        self.env.current_effect_row = saved_effect
        self.env.current_effect_order = saved_effect_order
        self._effect_ops_used = saved_ops

        return body_type

    # -----------------------------------------------------------------
    # #1233: a clause-body State operation code generation cannot lower
    # -----------------------------------------------------------------

    def _check_clause_op_addressing(self, decl: ast.FnDecl) -> None:
        """Refuse a handler-clause State operation codegen cannot lower (E339).

        A bare ``get``/``put`` — or ``State.get``/``State.put`` — written in
        a handler clause body is an operation of the ENCLOSING context
        (spec §7.5.2), and code generation lowers it by inlining the
        clause at each operation that reaches it.  Two shapes cannot be
        lowered, and each used to pass check and verify and then skip the
        function at compile (E602, and its callers after it, E620):

        * **The cell is shadowed** (#1233).  The host intrinsics address only
          the INNERMOST pushed cell of a State family, so when a cell of the
          operation's own family was pushed between its cell and the point
          where the clause is inlined — ``handle[State<Int>]`` nested in
          ``handle[State<Int>]``, a ``handle[State<Int>]`` in a function
          declaring ``effects(<State<Int>>)``, or deeper, through another
          clause's inlining — the operation would read or write the wrong
          cell.
        * **The re-entry is too deep.**  Each outward re-entry inlines one
          more clause, so the emitted code is exponential in the depth;
          code generation stops at ``STATE_CLAUSE_INLINE_DEPTH_CAP``.

        The walk here decides EXACTLY what code generation's gate decides
        (``_reject_unaddressable_clause_op`` and the depth check in
        ``_translate_state_clause_op``, vera/wasm/calls_handlers.py), over
        the same state: the families of the cells pushed so far, the index
        from which they shadow the scope an operation resolves in, and the
        declaration-time scope a clause is inlined under.  It walks what
        code generation walks — a clause body only where an operation
        inlines it, a lambda body with no cells (a lifted closure has
        none).  The gate stays in code generation as the backstop, and the
        two are held together by a differential
        (``tests/test_check_implies_compile.py``).

        A generic template's cells are named by their type parameters, so a
        ``State<T>`` shadowed only at one instantiation is not seen here;
        code generation still refuses that clone.
        """
        if not any(isinstance(node, ast.HandleExpr)
                   for node in _descendants(decl.body)):
            return
        walk = _ClauseWalk([], {})
        root = self._row_op_scope(decl.effect)
        self._clause_op_walk(decl.body, root, (), 0, walk)
        seen: set[int] = set()
        for node, why, cell in walk.refused:
            if id(node) in seen:
                continue
            seen.add(id(node))
            name = getattr(node, "name", "get")
            if why == "shadowed":
                self._error(
                    node,
                    f"This '{name}' in a handler clause body cannot reach "
                    f"its State<{cell.base}> cell: an enclosing "
                    f"State<{cell.base}> handler shadows it.",
                    rationale=(
                        "An operation written in a handler clause body is "
                        "the ENCLOSING context's (spec §7.5.2), so it reaches "
                        "a State<" + cell.base + "> cell outside this "
                        "handler.  Code generation lowers it where the "
                        "clause is inlined, and its State intrinsics address "
                        "only the innermost cell of one State type — here a "
                        "State<" + cell.base + "> cell nested inside the "
                        "one the operation means.  Outward cell addressing "
                        "is not implemented yet (#1233)."
                    ),
                    fix=(
                        "Nest handlers over different State types, move "
                        "the operation into the handled body, or override "
                        "this handler's own state with 'with @T = ...' on "
                        "the clause instead of performing the operation."
                    ),
                    spec_ref='Chapter 7, Section 7.5.2 "Handler Semantics"',
                    error_code="E339",
                )
            else:
                self._error(
                    node,
                    f"This '{name}' re-enters enclosing handler clauses "
                    f"more than {STATE_CLAUSE_INLINE_DEPTH_CAP} levels "
                    f"deep.",
                    rationale=(
                        "A State operation in a clause body is the "
                        "enclosing handler's (spec §7.5.2), so lowering it "
                        "inlines that handler's clause, whose own "
                        "operations inline the next one out.  The emitted "
                        "code grows exponentially with that depth, and "
                        "code generation stops at "
                        f"{STATE_CLAUSE_INLINE_DEPTH_CAP} levels."
                    ),
                    fix=(
                        "Reduce the handler nesting, or move the clause-body "
                        "operations into the handled bodies."
                    ),
                    spec_ref='Chapter 7, Section 7.5.2 "Handler Semantics"',
                    error_code="E339",
                )

    def _clause_cell(
        self, te: ast.TypeExpr,
        clauses: Mapping[str, ast.HandlerClause], scope: _OpScope | None,
    ) -> _ClauseCell:
        """The cell ``State<te>`` names, as code generation keys it."""
        env = self._naming_env()
        fallback = family_fallback_name(te)
        return _ClauseCell(
            family=naming.family_name(te, env, fallback),
            base=naming.family_base_name(te, env, fallback),
            clauses=clauses,
            scope=scope,
        )

    def _row_op_scope(self, row: ast.EffectRow) -> _OpScope:
        """The cells a declared row gives ``get``/``put``: its first
        ``State<T>`` in SOURCE order (spec §7.4), which is how code
        generation seeds its registries (vera/codegen/functions.py)."""
        cells: dict[str, _ClauseCell] = {}
        if isinstance(row, ast.EffectSet):
            for eff in row.effects:
                if (isinstance(eff, ast.EffectRef) and eff.name == "State"
                        and eff.type_args and len(eff.type_args) == 1
                        and type_expr_slot_name(eff.type_args[0])):
                    cell = self._clause_cell(eff.type_args[0], {}, None)
                    for op in _STATE_OPS:
                        cells.setdefault(op, cell)
        return _OpScope(cells, 0)

    def _clause_op_walk(
        self, node: object, scope: _OpScope, pushed: tuple[str, ...],
        depth: int, walk: _ClauseWalk,
    ) -> None:
        """Walk *node* as code generation emits it (see
        :meth:`_check_clause_op_addressing`)."""
        if isinstance(node, (ast.TypeExpr, ast.AssumeExpr)):
            # A type is not emitted, and neither is an `assume`: it is the
            # verifier's axiom and a no-op at run time, so an operation
            # inside one is never lowered.
            return
        if isinstance(node, ast.AnonFn):
            # A lifted closure is compiled with no State cells at all.
            self._clause_op_walk(node.body, _OpScope({}, 0), (), 0, walk)
            return
        if isinstance(node, ast.HandleExpr):
            self._clause_op_walk_handle(node, scope, pushed, depth, walk)
            return
        op = (self._state_op_name(node)
              if isinstance(node, (ast.FnCall, ast.QualifiedCall)) else None)
        if op is not None and isinstance(node, (ast.FnCall,
                                                 ast.QualifiedCall)):
            for arg in node.args:
                self._clause_op_walk(arg, scope, pushed, depth, walk)
            cell = scope.cells.get(op)
            if cell is None:
                return
            if cell.family in pushed[scope.addressable_from:]:
                walk.refused.append((node, "shadowed", cell))
                return
            clause = cell.clauses.get(op)
            if clause is None or cell.scope is None:
                return
            if depth >= STATE_CLAUSE_INLINE_DEPTH_CAP:
                walk.refused.append((node, "depth", cell))
                return
            key = (id(clause), id(cell.scope), pushed, depth + 1)
            if key in walk.inlined:
                return
            walk.inlined[key] = (clause, cell.scope)
            # The clause is inlined HERE: its body resolves in the handler's
            # declaration scope, under the cells pushed at this point.
            self._clause_op_walk(clause.body, cell.scope, pushed, depth + 1,
                                 walk)
            if clause.state_update is not None:
                self._clause_op_walk(clause.state_update[1], cell.scope,
                                     pushed, depth + 1, walk)
            return
        if isinstance(node, ast.Node):
            for f in dataclasses.fields(node):
                self._clause_op_walk(getattr(node, f.name), scope, pushed,
                                     depth, walk)
        elif isinstance(node, (tuple, list)):
            for item in node:
                self._clause_op_walk(item, scope, pushed, depth, walk)

    def _clause_op_walk_handle(
        self, node: ast.HandleExpr, scope: _OpScope, pushed: tuple[str, ...],
        depth: int, walk: _ClauseWalk,
    ) -> None:
        """A ``handle`` expression, as code generation lowers it."""
        eff = node.effect
        if node.state is not None:
            # The init belongs to the ENCLOSING scope: evaluated before the
            # cell is pushed.
            self._clause_op_walk(node.state.init_expr, scope, pushed, depth,
                                 walk)
        if (isinstance(eff, ast.EffectRef) and eff.name == "State"
                and eff.type_args and len(eff.type_args) == 1):
            te = eff.type_args[0]
            if not isinstance(te, ast.NamedType):
                # Code generation refuses this handle outright (an inline
                # refinement as the cell type, spec §7.5.1).
                return
            cell = self._clause_cell(
                te, {c.op_name: c for c in node.clauses}, scope)
            body_scope = _OpScope(
                {**scope.cells, **{op: cell for op in _STATE_OPS}},
                len(pushed) + 1,
            )
            # Clause bodies are NOT walked here: code generation emits one
            # only where an operation inlines it.
            self._clause_op_walk(node.body, body_scope, (*pushed, cell.family),
                                 depth, walk)
            return
        if isinstance(eff, ast.EffectRef) and eff.name == "Exn":
            # An Exn clause is compiled once, at the handle, in the scope the
            # handle is written in; `throw` reaches no State cell.
            for clause in node.clauses:
                self._clause_op_walk(clause.body, scope, pushed, depth, walk)
            self._clause_op_walk(node.body, scope, pushed, depth, walk)
        # Any other handler is refused by code generation outright.

    def _state_op_name(
        self, node: ast.FnCall | ast.QualifiedCall,
    ) -> str | None:
        """``get``/``put`` when *node* performs that State operation."""
        if (isinstance(node, ast.QualifiedCall) and node.qualifier == "State"
                and node.name in _STATE_OPS):
            return node.name
        if (isinstance(node, ast.FnCall) and node.name in _STATE_OPS
                and not bare_call_denotes_user_fn(
                    node.name, self._user_fn_names)):
            return node.name
        return None


def _descendants(node: object) -> list[object]:
    """Every AST node under *node* (iterative, types excluded)."""
    out: list[object] = []
    stack: list[object] = [node]
    while stack:
        cur = stack.pop()
        if isinstance(cur, ast.TypeExpr):
            continue
        if isinstance(cur, ast.Node):
            out.append(cur)
            stack.extend(getattr(cur, f.name)
                         for f in dataclasses.fields(cur))
        elif isinstance(cur, (tuple, list)):
            stack.extend(cur)
    return out
