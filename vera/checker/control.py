"""Control-flow, pattern, and handler type-checking mix-in."""

from __future__ import annotations

import dataclasses
from collections.abc import Collection, Mapping, Sequence
from dataclasses import dataclass

from vera import ast, naming, narrowing, patterns
from vera.checker.registration import builtin_effect_names
from vera.environment import AdtInfo, Binding, ConstructorInfo, FunctionInfo
from vera.formatter import format_type_canonical
from vera.lowering import (
    CLAUSE_RESUME_IN_WITH,
    STATE_CLAUSE_INLINE_DEPTH_CAP,
    Cell,
    cell_type_spelling_lowerable,
    contract_exprs,
    exn_payload_type_lowerable,
    handler_lowerable,
    shadowing_cell,
    state_cell_type_lowerable,
    state_clause_refusal,
)
from vera.slots import (
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
    EffectInstance,
    FunctionType,
    PrimitiveType,
    PureEffectRow,
    RefinedType,
    Type,
    TypeVar,
    UnknownType,
    base_type,
    contains_typevar,
    is_pair_represented,
    is_subtype,
    pretty_type,
    pretty_inferred_type,
    state_cell_decl_equal,
    substitute,
    types_equal,
)


#: The State operations a bare or ``State.``-qualified call can name.
_STATE_OPS = frozenset({"get", "put"})

#: The largest value an integer literal pattern can name: i64's, which an
#: `@Int` is and a `@Nat` is the non-negative half of, and `@Byte`'s.
_I64_MAX = 2**63 - 1
_BYTE_MAX = 255


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
    #: The checker's semantic type of the cell, which E339 unifies when a
    #: type parameter is in it (#1522).
    type: Type | None = None
    #: The cell type as its handler or row writes it, alias-opaque, which
    #: E339's type-parameter fix names the cell's handler by.
    written: str = ""

    @property
    def identity(self) -> Cell:
        """The cell as `vera.lowering`'s shadowing rule compares it."""
        return Cell(self.family, self.type)


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

    #: Each refused operation: the call, why ("shadowed" or "depth"), the
    #: cell it means, and for "shadowed" the pushed cell that shadows it.
    refused: list[tuple[ast.Node, str, _ClauseCell, Cell | None]]
    inlined: dict[
        tuple[int, int, tuple[Cell, ...], int],
        tuple[ast.HandlerClause, _OpScope],
    ]


@dataclass(frozen=True)
class _HeadMisfit:
    """Why a constructor head cannot take a value of a type
    (`ControlFlowMixin._head_misfit`): it is a constructor of *owner*,
    another type; `Tuple` over a tuple of *components* components, another
    number; or `Tuple` over a value that is no tuple (neither is set)."""

    owner: str | None = None
    components: int | None = None


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


def _display_only(ty: Type, declared: Collection[str]) -> bool:
    """Whether `pretty_type` renders a part of *ty* that no program can be
    written with: a refinement, whose predicate it elides (`{@Int | ...}`),
    `Unknown` (`?`), and a type variable or an effect-row variable outside
    *declared*, the enclosing function's own (an inference variable,
    `T$1`, another function's, a built-in's).  The walk is the one
    `pretty_type` and `pretty_effect` make."""
    if isinstance(ty, (RefinedType, UnknownType)):
        return True
    if isinstance(ty, TypeVar):
        return ty.name not in declared
    if isinstance(ty, AdtType):
        return any(_display_only(a, declared) for a in ty.type_args)
    if isinstance(ty, FunctionType):
        row = ty.effect
        return (any(_display_only(p, declared) for p in ty.params)
                or _display_only(ty.return_type, declared)
                or (isinstance(row, ConcreteEffectRow)
                    and (any(_display_only(a, declared)
                             for e in row.effects for a in e.type_args)
                         or (row.row_var is not None
                             and row.row_var not in declared))))
    return False


def _no_call(_call: ast.Expr) -> str | None:
    """A call-type oracle that reads no call: a call's result is never a
    constant, and the checker's types for one are a table only artifact
    collection fills."""
    return None


def _signed_join(
    joined: Type | None, branches: Sequence[tuple[ast.Expr, Type]],
) -> Type | None:
    """The type of a join whose branches meet as an `@Int` and a `@Nat`
    (#1756).

    `is_subtype` admits an `@Int` where a `@Nat` is expected, leaving the
    narrowing to the verifier, and `_join` gives its first type to its
    second, so an `if` whose then-branch is an `@Int` and whose else-branch is
    a `@Nat`, or a `match` whose later arm is the `@Int`, came out a `@Nat`.
    The verifier reads a join's type to decide whether binding it into a
    `@Nat` position narrows, and saw no narrowing, while code generation's
    static rule read the `@Int` branch and planted the guard.  So a join
    *joined* as a `@Nat`, or as a refinement of `@Nat` (the subtype rule
    hands it the refined type), is an `@Int`, spec §4.4's meet of the two,
    when one of its *branches* is an `@Int` that is not statically
    non-negative: `vera.narrowing.is_static_nat_typed`, the rule code
    generation's guard reads, which takes a literal at its value and never a
    negation.  Binding it into a `@Nat` position is then a narrowing the
    verifier obligates.  A join whose `@Int` branches are all non-negative
    constants keeps its type, as before.
    """
    if joined is None or not types_equal(base_type(joined), NAT):
        return joined
    for expr, ty in branches:
        if (types_equal(base_type(ty), INT)
                and not narrowing.is_static_nat_typed(expr, _no_call)):
            return INT
    return joined


def _bindings_form(name: str, types: tuple[Type, ...]) -> str:
    """A destructure's head binding *types* by constructor *name*, as
    written: `Pair<@Int, @String>`."""
    return f"{name}<{', '.join('@' + pretty_type(t) for t in types)}>"


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

        # Branches must have compatible types.  The `if` has the type the
        # two have together (`_join`, #1668): the type of the branch the
        # other is a subtype of, with each position it leaves open given by
        # the other, so `[]` beside `["abc"]` is an `Array<String>` in
        # either order.
        branches = [(expr.then_branch, then_ty), (expr.else_branch, else_ty)]
        if is_subtype(then_ty, else_ty):
            return _signed_join(
                self._join(then_ty, else_ty) or else_ty, branches)
        if is_subtype(else_ty, then_ty):  # pragma: no cover — subtyping is symmetric for current rules
            return _signed_join(
                self._join(else_ty, then_ty) or then_ty, branches)

        # Re-synthesis: a branch with an unresolved type variable is
        # synthesized again with the other branch's type expected, so a
        # constructor takes from it the type arguments it cannot fix
        # itself, and the two are joined.  The join also fills what
        # re-synthesis does not reach (a `None` inside a `Tuple`), and
        # joins two branches that both leave a position open; branches of
        # two types no position reconciles are refused.
        joined: Type | None
        if contains_typevar(then_ty) and not contains_typevar(else_ty):
            then_ty = self._synth_expr(
                expr.then_branch, expected=else_ty) or then_ty
            joined = self._join(then_ty, else_ty)
        elif contains_typevar(else_ty) and not contains_typevar(then_ty):
            else_ty = self._synth_expr(
                expr.else_branch, expected=then_ty) or else_ty
            joined = self._join(else_ty, then_ty)
        else:
            outcome = self._join_parts(else_ty, then_ty)
            joined = outcome.joined or self._join(then_ty, else_ty)
            if (joined is None and outcome.builtin
                    and self._fits(else_ty, then_ty)):
                # A built-in's type variable the join leaves alone: the
                # then branch, as two open branches always gave.
                joined = then_ty
        if joined is not None:
            return _signed_join(joined, [(expr.then_branch, then_ty),
                                         (expr.else_branch, else_ty)])

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
        # #1671: an expression the check has refused is typed `Unknown`,
        # which gives the arms no type to cover, so a scrutinee typed
        # `Unknown` once an error has been reported is not judged for
        # coverage.  Any error counts, not only one raised while typing the
        # scrutinee: the error behind an `Unknown` can sit at a declaration
        # (E158) or an import (E155).  It is read here, before the arms are
        # checked: an error inside an arm says nothing about the scrutinee.
        # `Unknown` with no error reported (`apply_fn` over a type variable)
        # is judged as before, and its E313 is the error that refuses the
        # program.  A position inside the scrutinee whose type the check did
        # not settle is read by the same rule (`_pattern_domain`, #1697).
        after_error = any(d.severity == "error" for d in self.errors)
        in_error = (isinstance(base_type(scrutinee_ty), UnknownType)
                    and after_error)

        result_type: Type | None = None
        arm_types: list[tuple[ast.Expr, Type]] = []
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
            arm_types.append((arm.body, arm_ty))

            if result_type is None or isinstance(result_type, UnknownType):
                result_type = arm_ty
            elif types_equal(result_type, NEVER):
                result_type = arm_ty
            elif not types_equal(arm_ty, NEVER):
                # Re-synthesis fallback for unresolved TypeVars
                if contains_typevar(arm_ty) and not contains_typevar(result_type):
                    arm_ty = self._synth_expr(
                        arm.body, expected=result_type)
                    if arm_ty is None or isinstance(arm_ty, UnknownType):
                        continue

                # The arms so far and this one have the type they have
                # together (`_join`, #1668).  Where the arms so far leave a
                # position open and this arm leaves none, it is this arm's
                # type, with any part this arm leaves unknown given by
                # them; otherwise it is theirs, with each position they
                # leave open given by this arm.
                joined: Type | None
                if (contains_typevar(result_type)
                        and not contains_typevar(arm_ty)):
                    outcome = self._join_parts(result_type, arm_ty)
                    joined = outcome.joined
                    if (joined is None and outcome.builtin
                            and self._fits(result_type, arm_ty)):
                        # A built-in's type variable the join leaves alone
                        # (one a failed substitution left, #1688): this
                        # arm's type, as an arm after an open arm always
                        # gave.
                        joined = arm_ty
                else:
                    joined = self._join(arm_ty, result_type)
                    if joined is None and is_subtype(result_type, arm_ty):
                        joined = result_type
                if joined is not None:
                    result_type = joined
                else:
                    # Both types are inferred, so an open position shows
                    # as `?` (`pretty_inferred_type`): an arm synthesized
                    # again, as a call argument is, then reports once.
                    self._error(
                        arm.body if hasattr(arm, 'body') else expr,
                        f"Match arm type {pretty_inferred_type(arm_ty)} is "
                        f"incompatible with previous arm type "
                        f"{pretty_inferred_type(result_type)}.",
                        rationale="All match arms must have the same type.",
                        fix=f"Make this arm produce "
                            f"{pretty_inferred_type(result_type)} "
                            f"to match the other arms (or change every arm to "
                            f"a common type).",
                        spec_ref='Chapter 4, Section 4.9 "Match Expressions"',
                        error_code="E302",
                    )

        # #1497: a match naming a refused declaration's constructor was
        # written against that declaration, so its coverage is not judged.
        if not (self._refused_ctor_names and any(
                self._names_refused_ctor(arm.pattern) for arm in expr.arms)):
            self._check_exhaustiveness(expr, scrutinee_ty, in_error=in_error,
                                       after_error=after_error)
        return _signed_join(result_type, arm_types) or UnknownType()

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
        self, expr: ast.MatchExpr, scrutinee_ty: Type, *, in_error: bool,
        after_error: bool,
    ) -> None:
        """Check that match arms cover all possible values of the scrutinee.

        Spec Section 4.9.2: compiler MUST verify match is exhaustive.
        Spec Section 4.9.3: compiler SHOULD warn about unreachable arms.

        A scrutinee *in_error* (#1671) has no type to judge coverage by, so
        only the arms are judged: an arm after a catch-all is unreachable
        whatever the scrutinee's type.  *after_error*: an error had been
        reported when the scrutinee was typed, which decides how a position
        inside it whose type the check did not settle is read
        (`_pattern_domain`).
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
        if in_error:
            return  # #1671: no type for the arms to cover

        # --- ADT exhaustiveness ---
        if isinstance(raw_ty, AdtType):
            # #1513: a type this file does not import is judged by its own
            # declaration, as its constructors are resolved by it.  A tuple
            # type is its one constructor, `Tuple`, over its components.
            if (raw_ty.name != "Tuple"
                    and self._match_data_type(raw_ty.name) is None):
                return  # unknown ADT, can't check
            # #1697: every pattern is read to its full depth, so a case
            # missing inside a constructor's fields is missing as one at
            # the top is, and the message names it (`W(Green)`).
            scrutinee: Type = raw_ty
            missing = patterns.missing_cases(
                [self._coverage_pattern(arm.pattern) for arm in expr.arms],
                scrutinee,
                lambda ty: self._pattern_domain(ty, after_error=after_error))
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

    def _coverage_pattern(self, pat: ast.Pattern) -> ast.Pattern:
        """*pat* as the coverage reading takes it: a sub-pattern the check
        refused (E314, an unknown constructor) takes every value, so its arm
        draws no E311 beside that error, as a scrutinee in error draws none
        (#1671).  The pattern itself is read as written, so what it leaves
        at the scrutinee is named beside its error, as it always was."""
        if not isinstance(pat, ast.ConstructorPattern):
            return pat
        return dataclasses.replace(pat, sub_patterns=tuple(
            ast.WildcardPattern() if id(sub) in self._refused_patterns
            else self._coverage_pattern(sub) for sub in pat.sub_patterns))

    def _match_data_type(self, name: str) -> AdtInfo | None:
        """The data declaration a `match` over type *name* is judged by: the
        one in scope, or (#1513) the one a type this file does not import
        denotes."""
        return (self.env.data_types.get(name)
                or self._stranger_data_type(name))

    def _pattern_domain(
        self, ty: Type, *, after_error: bool,
    ) -> patterns.Domain[Type] | None:
        """What the values at a `match` position of type *ty* are, for the
        coverage reading (`vera.patterns.missing_cases`, #1697).

        A data type's are its declaration's constructors, each field at the
        type the scrutinee's type arguments give it, as a constructor
        pattern binds them; a tuple type's, its one constructor `Tuple` over
        its components; `Bool`'s, `true` and `false`.  Every other type has
        an open domain, which only a catch-all covers, as a scrutinee of it
        needs one (E313): every other primitive, a built-in with no
        constructors, a function type, and a type parameter the function
        declares, which may be `Int`, so `Some(None)` and `Some(Some(_))`
        over `Option<T>` leave `Some(_)`.  A position whose type the check
        did not settle, `Unknown` or a type variable no inference bound
        (`T$1`, which `Some(e)` has where `e` is in error), is open too,
        unless an error has been reported by the time the scrutinee is typed
        (*after_error*).  Then the error is what left it unsettled, and it
        is not judged (``None``), as a scrutinee typed `Unknown` after an
        error is not (#1671), so the arms draw no E311 beside that error.
        Nor is a `Tuple` with no components, or a data type no declaration
        in reach says, as a scrutinee of one is not.
        """
        raw = base_type(ty)
        if isinstance(raw, PrimitiveType):
            return (patterns.Booleans() if raw.name == "Bool"
                    else patterns.Open())
        if isinstance(raw, AdtType):
            info = self._match_data_type(raw.name)
            if info is not None:
                return self._declared_constructors(info, raw)
            if raw.name == "Tuple":
                if raw.type_args:
                    return patterns.Constructors(
                        (patterns.Constructor("Tuple", raw.type_args),))
            elif raw.name in _CONSTRUCTORLESS_BUILTIN_TYPES:
                return patterns.Open()
            return None
        if isinstance(raw, TypeVar) and raw.name in self.env.type_params:
            return patterns.Open()
        if isinstance(raw, (UnknownType, TypeVar)) and after_error:
            return None
        return patterns.Open()

    def _declared_constructors(
        self, info: AdtInfo, ty: Type,
    ) -> patterns.Constructors[Type]:
        """*info*'s constructors in declaration order, each field at the
        type a value of *ty* gives it (`_constructor_fields`)."""
        return patterns.Constructors(tuple(
            patterns.Constructor(ci.name, self._constructor_fields(ci, ty))
            for ci in info.constructors.values()))

    @staticmethod
    def _constructor_fields(
        ci: ConstructorInfo, ty: Type | None,
    ) -> tuple[Type, ...]:
        """The types of *ci*'s fields in a value of type *ty*: the declared
        ones, each type parameter replaced by *ty*'s argument for it, a
        refinement of *ty* read as its base, since a refinement does not
        change which patterns match a value (§4.9.1).  The one reading of a
        constructor's fields, for the types a constructor pattern's
        sub-patterns are checked against and the values the coverage reading
        splits (#1697)."""
        fields = ci.field_types or ()
        ty = base_type(ty) if ty is not None else None
        if (isinstance(ty, AdtType) and ci.parent_type_params
                and ty.type_args):
            mapping = dict(zip(ci.parent_type_params, ty.type_args))
            fields = tuple(substitute(ft, mapping) for ft in fields)
        return fields

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
            self._refused_patterns[id(pat)] = pat
        if isinstance(pat, ast.ConstructorPattern):
            return self._check_ctor_pattern(pat, expected)
        if isinstance(pat, ast.NullaryPattern):
            return self._check_nullary_pattern(pat, expected)
        if isinstance(pat, ast.WildcardPattern):
            return []
        if isinstance(pat, ast.IntPattern):
            self._check_int_pattern_range(pat, expected)
            return []
        if isinstance(pat, ast.StringPattern):
            return []
        if isinstance(pat, ast.BoolPattern):
            return []
        return []  # pragma: no cover — exhaustive isinstance chain above

    def _check_int_pattern_range(
        self, pat: ast.IntPattern, expected: Type | None,
    ) -> None:
        """E149 for an integer literal pattern its scrutinee's type cannot
        hold: the range an integer literal has wherever it is written (spec
        §4.2), `@Byte`'s 0..255 over a `Byte` scrutinee and i64's over any
        other.  A pattern is written without a sign, so only the upper bound
        can be passed.  Past it, code generation compares the scrutinee with
        the literal's bits: `9223372036854775808` would match -2^63."""
        base = base_type(expected) if expected is not None else None
        if base == BYTE:
            if pat.value > _BYTE_MAX:
                self._literal_range_error(
                    pat,
                    f"Integer literal {pat.value} is out of range for "
                    f"@Byte; the range is 0..{_BYTE_MAX}.",
                    rationale=(
                        "A `@Byte` is an unsigned 8-bit integer, so no "
                        "value of the scrutinee equals a literal outside "
                        "0..255, and code generation compares at that "
                        "width."
                    ),
                    fix=("Use a pattern literal in 0..255, or match the "
                         "value at a wider type such as `@Int`."),
                    contextual=True,
                )
            return
        if pat.value > _I64_MAX:
            type_name = "@Nat" if base == NAT else "@Int"
            self._literal_range_error(
                pat,
                f"Integer literal {pat.value} is out of range for "
                f"{type_name} (i64); the maximum is {_I64_MAX}.",
                rationale=(
                    "`@Int` is a signed 64-bit integer and `@Nat` holds its "
                    "non-negative half, so no value of the scrutinee equals "
                    f"a literal above {_I64_MAX}, and code generation would "
                    "compare it with the literal's bits reinterpreted as a "
                    "negative i64."
                ),
                fix=(f"Use a pattern literal no greater than {_I64_MAX}, "
                     "or match the value with a binding pattern and a "
                     "comparison."),
                contextual=True,
            )

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

        if isinstance(pat, (ast.ConstructorPattern, ast.NullaryPattern)):
            got = (len(pat.sub_patterns)
                   if isinstance(pat, ast.ConstructorPattern) else None)
            misfit = self._head_misfit(pat.name, got, scrut)
            if misfit is None:
                return False
            if misfit.owner is not None:
                return self._pattern_mismatch(
                    pat, f"Pattern '{pat.name}'",
                    f"is a constructor of {misfit.owner}", scrut,
                )
            if misfit.components is not None:
                return self._pattern_mismatch(
                    pat, f"Pattern 'Tuple' with {got} sub-pattern(s)",
                    f"matches a tuple of {got} component(s)", scrut,
                    fix=f"Give the pattern one sub-pattern per component "
                        f"of {pretty_type(scrut)} ({misfit.components}), or "
                        f"match the scrutinee with a wildcard '_'.",
                )
            return self._pattern_mismatch(
                pat, "Pattern 'Tuple(...)'", "matches a tuple", scrut,
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

    def _pattern_ctor_info(self, name: str) -> ConstructorInfo | None:
        """The constructor a pattern's head *name* denotes: the one in
        scope, or one of a type this file does not import, typed by its own
        declaration (#1513); None for a name that denotes none, and for a
        constructor of a declaration refused as E158, whose error is the
        one the program owes (#1497)."""
        ci = self.env.lookup_constructor(name)
        if ci is None and name not in self._refused_ctor_names:
            _candidates, ci = self._stranger_constructor(name)
        return ci

    def _head_misfit(
        self, name: str, positions: int | None, scrut: Type,
    ) -> _HeadMisfit | None:
        """Why the constructor head *name*, given *positions* sub-patterns
        (None for a nullary pattern), cannot take a value of *scrut*, a
        type `_scrutinee_for_pattern` decides; None where it can, and where
        the name denotes no constructor, which E320 and E322 report.

        The one rule a `match` arm's constructor pattern (#1315, #1320) and
        a destructuring `let`'s constructor (#1545) are held to.  `Tuple`
        takes a tuple of as many components as it has positions: the
        variadic Tuple carrier has no registry entry, so the E321
        field-count rule never sees it, and a head with another number
        bound the components it did name POSITIONALLY, whatever their
        types.  Any other constructor takes a value of its own data type,
        one of a type this file does not import included, so a constructor
        of another type cannot take this value here either."""
        if positions is not None and name == "Tuple":
            if isinstance(scrut, AdtType) and scrut.name == "Tuple":
                components = len(scrut.type_args)
                if not components or components == positions:
                    return None
                return _HeadMisfit(components=components)
            return _HeadMisfit()
        ci = self._pattern_ctor_info(name)
        if ci is None:
            return None
        if isinstance(scrut, AdtType) and scrut.name == ci.parent_type:
            return None
        owner = ci.parent_type
        if ci.parent_type_params:
            owner += f"<{', '.join(ci.parent_type_params)}>"
        return _HeadMisfit(owner=owner)

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
            self._refused_patterns[id(pat)] = pat
            return []

        # Infer type args from expected type
        field_types = self._constructor_fields(ci, expected)

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
        # Derive field types from expected Tuple type if available, a
        # refinement of it read as its base (`_constructor_fields`).
        field_types: tuple[Type | None, ...] = (None,) * len(pat.sub_patterns)
        tuple_ty = base_type(expected) if expected is not None else None
        if (isinstance(tuple_ty, AdtType) and tuple_ty.name == "Tuple"
                and len(tuple_ty.type_args) == len(pat.sub_patterns)):
            field_types = tuple_ty.type_args
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
            self._refused_patterns[id(pat)] = pat
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
    # A destructuring let, held to its constructor pattern (#1545)
    # -----------------------------------------------------------------

    def _check_destructure(
        self, stmt: ast.LetDestruct, value_ty: Type | None,
        bindings: list[Type], *, after_error: bool,
    ) -> None:
        """Hold `let C<@T1, …, @Tn> = e;` to the rules its one-arm pattern
        `match e { C(@T1, …, @Tn) -> … }` is held to, read by the functions
        that decide them for the arm, and each binding to the rule a `let`
        binding is held to (#1545, spec §4.7.1).

        *value_ty* is the type `e` synthesizes without an expected type,
        and *bindings* the types the destructure writes: what it claims of
        the value, never the type the value is read at, so an `if` whose
        branches build `Tuple(1, 2)` is a `Tuple<Int, Int>` whatever the
        bindings say.

        The head names the value's shape by a constructor (`let MkBox<…>`)
        or by the value's type (`let Wrap<…>` over a `Wrap<Int>`, whose
        constructor is `W`; `let Tuple<…>`), by its name or a type alias of
        it, as the verifier reads it (`_destructure_ctor_name`); a type's
        name is read as the type where it is the value's, even where
        another type has a constructor of that name.  The first rule broken
        is the one reported:

        - the head names a constructor or a data type (E320);
        - where the value's type decides it (`_scrutinee_for_pattern`), the
          head is that type's: `Tuple` a tuple of as many components as
          there are bindings, a constructor one of the type's own
          (`_head_misfit`, E314), a type's name or alias the type itself
          (E314);
        - a data constructor has one binding per field, the fields read at
          the value's type arguments (`_constructor_fields`, E321);
        - the one arm covers the value's type (the coverage reading a
          `match` is given, `vera.patterns.missing_cases` over
          `_pattern_domain`): a type with another constructor is refused,
          a destructure having no arm for it (E311), and so is a type no
          constructor builds, a type parameter's among them (E313);
        - each component fits its binding by the judgement a call argument
          is held to its parameter by (`_fits`), on concrete types the
          plain `let`'s `is_subtype`, so a `@Nat` component widens into an
          `@Int` binding and an `@Int` one narrows into an `@Nat` or a
          refined binding, which the verifier obligates (E170, at the
          binding).

        A value typed `Unknown` once an error has been reported is not
        judged, as a `match` over one is not (#1671)."""
        ty = value_ty if value_ty is not None else UnknownType()
        base = base_type(ty)
        if isinstance(base, UnknownType) and after_error:
            return
        name = stmt.constructor
        count = len(stmt.type_bindings)
        scrut = self._scrutinee_for_pattern(ty)
        # A type alias names the type it stands for (`type P = Pair;` and
        # `let P<…>`), so the rules read that type's name, `Tuple` for an
        # alias of a tuple type.  An alias that fixes type arguments is the
        # value's type only where the value fits it, as a `let @P` value
        # must; a generic alias, whose head supplies none, names its type
        # by the type's name.
        alias = self.env.type_aliases.get(name)
        if alias is not None and isinstance(scrut, AdtType):
            # A constructor of the value's type is read as that
            # constructor though an alias of another type has its name,
            # the mirror of a type's name beside another type's
            # constructor, as a `match` arm and the verifier read it.
            own_ctor = self._pattern_ctor_info(name)
            if own_ctor is not None and own_ctor.parent_type == scrut.name:
                alias = None
        target = (base_type(alias.resolved_type) if alias is not None
                  else None)
        # A data type's name is read as the type it denotes here, which is
        # typed by its identity (#1694); a constructor's name stays a name.
        declared = self.env.lookup_type(name)
        identity = declared.name if declared is not None else name
        head = target.name if isinstance(target, AdtType) else identity
        ci: ConstructorInfo | None = None
        # The data type the head names by its type name, the value's own
        # where `own` (its constructors then decide), another otherwise.
        named: AdtInfo | None = None
        own = False
        if alias is not None and scrut is not None:
            own = ((scrut.name == head
                    if isinstance(target, AdtType)
                    and isinstance(scrut, AdtType)
                    else target is not None and types_equal(target, scrut))
                   and (bool(alias.type_params)
                        or self._fits(ty, alias.resolved_type)))
        if head != "Tuple":
            if alias is None:
                ci = self._pattern_ctor_info(name)
                own = (isinstance(scrut, AdtType) and scrut.name == identity
                       and (ci is None or ci.parent_type != identity))
            if own:
                named = self._match_data_type(head)
            elif ci is None:
                named = self._match_data_type(head)
                if named is None and alias is None:
                    if name in self._refused_ctor_names:
                        return  # #1497: the declaration's E158 is it
                    candidates, _stranger = self._stranger_constructor(name)
                    self._error(
                        stmt,
                        f"Unknown constructor '{name}' in a destructuring "
                        f"let.",
                        rationale=(
                            "A destructuring let takes its value apart by "
                            "the constructor or the data type it names, "
                            "which must be the value's; no constructor or "
                            "data type of that name is defined or "
                            "imported."),
                        fix=(self._destructure_fix(ty)
                             or self._unknown_ctor_fix(name, candidates)),
                        spec_ref='Chapter 4, Section 4.7.1 "Tuple Destructuring"',
                        error_code="E320",
                    )
                    return
            if named is not None:
                ctors = list(named.constructors.values())
                ci = ctors[0] if len(ctors) == 1 else None
        components: tuple[Type, ...] | None = None
        if scrut is not None:
            misfit: _HeadMisfit | None = None
            if not own and (alias is not None
                            or (named is not None and head != "Tuple")):
                misfit = _HeadMisfit(owner=head)
            elif head == "Tuple" or not own:
                misfit = self._head_misfit(head, count, scrut)
            if misfit is not None:
                shown = pretty_type(scrut)
                if alias is not None and not own:
                    message = (f"Destructuring let names the type alias "
                               f"'{name}', which stands for "
                               f"{pretty_type(alias.resolved_type)}, but the "
                               f"value has type {shown}.")
                elif named is not None and not own:
                    message = (f"Destructuring let names the type '{name}', "
                               f"but the value has type {shown}.")
                elif misfit.owner is not None:
                    message = (f"Destructuring let names '{name}', a "
                               f"constructor of {misfit.owner}, but the "
                               f"value has type {shown}.")
                elif misfit.components is not None:
                    message = (f"Destructuring let names a tuple of {count} "
                               f"component(s), but the value has type "
                               f"{shown}, a tuple of {misfit.components}.")
                else:
                    message = (f"Destructuring let names a tuple, but the "
                               f"value has type {shown}.")
                whole = (f"Bind the value whole with `let @{shown} = …;`, "
                         f"or match it." if self._fix_writes(scrut)
                         else "Match the value, or destructure a value of "
                              "the type the head names.")
                self._error(
                    stmt, message,
                    rationale=(
                        "A destructuring let takes its value apart by the "
                        "constructor or the data type it names, so the head "
                        "must be the value's: `Tuple` for a tuple with one "
                        "component per binding, and otherwise the value's "
                        "data type or a constructor of it."),
                    fix=self._destructure_fix(ty) or whole,
                    spec_ref='Chapter 4, Section 4.7.1 "Tuple Destructuring"',
                    error_code="E314",
                )
                return
            if isinstance(scrut, AdtType) and head == "Tuple":
                components = scrut.type_args
        if ci is not None:
            fields = self._constructor_fields(ci, ty)
            if len(fields) != count:
                who = (f"Constructor '{ci.name}'" if ci.name == name
                       else f"Constructor '{ci.name}' of '{name}'")
                self._error(
                    stmt,
                    f"{who} has {len(fields)} field(s), the destructuring "
                    f"let has {count} binding(s).",
                    rationale=(
                        "A destructuring let binds each field of the "
                        "constructor it takes its value apart by, so it "
                        "writes one binding per field."),
                    fix=(f"Write one binding per field of '{ci.name}': "
                         f"`{_bindings_form(name, fields)}`."
                         if fields and self._fix_writes(*fields)
                         else f"Write one binding per field of "
                              f"'{ci.name}', {len(fields)} in all." if fields
                         else f"'{ci.name}' has no field to bind: bind the "
                              f"value whole with `let @{pretty_type(ty)} = "
                              f"…;`." if self._fix_writes(ty)
                         else f"'{ci.name}' has no field to bind: bind the "
                              f"value whole with a plain `let`."),
                    spec_ref='Chapter 4, Section 4.7.1 "Tuple Destructuring"',
                    error_code="E321",
                )
                return
            if scrut is not None:
                components = fields
        missing = patterns.missing_cases(
            [ast.ConstructorPattern(
                name=ci.name if ci is not None else head,
                sub_patterns=(ast.WildcardPattern(),) * count)],
            base, lambda t: self._pattern_domain(t, after_error=after_error))
        if missing:
            shown = pretty_inferred_type(ty)
            if missing == ("_",):
                built = ("a tuple" if head == "Tuple"
                         else f"a value of {ci.parent_type}, the type "
                              f"'{name}' builds" if ci is not None
                         else f"a value of '{name}'")
                # `apply_fn` over a type variable is typed `Unknown`: no type
                # to name.
                value = ("the value's type is not known"
                         if isinstance(base, UnknownType)
                         else f"the value has type {shown}")
                if not self._fix_writes(ty):
                    fix = (f"Bind the value whole with a plain `let`: "
                           f"'{name}' has no constructor to take it apart "
                           f"by." if own else f"Destructure {built}.")
                else:
                    fix = (f"Bind the value whole with `let @{shown} = "
                           f"…;`: '{name}' has no constructor to take it "
                           f"apart by." if own
                           else f"Destructure {built}, or bind this value "
                                f"whole with `let @{shown} = …;`.")
                self._error(
                    stmt,
                    f"Destructuring let names '{name}', but {value}, which "
                    f"no constructor is known to build.",
                    rationale=(
                        "A destructuring let binds the fields of the "
                        "constructor that builds its value, so the value's "
                        "type must be a data type or a tuple type built by "
                        "that constructor: a value of a type parameter may "
                        "be of any type, and a type with no constructors "
                        "has no fields to bind."),
                    fix=fix,
                    spec_ref='Chapter 4, Section 4.7.1 "Tuple Destructuring"',
                    error_code="E313",
                )
                return
            cases = ", ".join(missing)
            arms = [f"{self._uncovered_arm(m, base)} -> …" for m in missing]
            if ci is not None:
                written = ", ".join(
                    "@" + pretty_type(b) if self._fix_writes(b) else "_"
                    for b in bindings)
                arms.insert(0, f"{ci.name}({written}) -> …")
                message = (f"Destructuring let names '{name}', but a value "
                           f"of type {shown} may also be {cases}.")
            else:
                message = (f"Destructuring let names the type '{name}', "
                           f"which has more than one constructor: {cases}.")
            self._error(
                stmt, message,
                rationale=(
                    "A destructuring let has one arm: it binds the fields "
                    "of one constructor and has none for another, so its "
                    "value's type must have that constructor alone.  A "
                    "value of a type with several constructors is taken "
                    "apart by a match, with an arm for each."),
                fix=(f"Match the value instead, with an arm for each "
                     f"constructor: `match … {{ {', '.join(arms)} }}`."),
                spec_ref='Chapter 4, Section 4.7.1 "Tuple Destructuring"',
                error_code="E311",
            )
            return
        if components is None:
            return
        for index, (te, binding, component) in enumerate(
                zip(stmt.type_bindings, bindings, components)):
            if self._fits(component, binding):
                continue
            position = index + 1
            self._error(
                te,
                f"Let binding expects {pretty_type(binding)}, component "
                f"{position} of the destructured value has type "
                f"{pretty_inferred_type(component)}.",
                rationale=(
                    "A destructuring let binds each component of its value "
                    "at the type written for it, so each component must be "
                    "a subtype of its binding's type, as a let binding's "
                    "value must be."),
                fix=(f"Write the binding as "
                     f"`@{pretty_inferred_type(component)}`, the type of "
                     f"component {position}, or give the value a component "
                     f"of type {pretty_type(binding)} there."
                     if self._fix_writes(component)
                     else f"Give the value a component of type "
                          f"{pretty_type(binding)} there, or write the "
                          f"binding at the type of component {position}."),
                spec_ref='Chapter 4, Section 4.7.1 "Tuple Destructuring"',
                error_code="E170",
            )

    def _fix_writes(self, *types: Type) -> bool:
        """Whether a fix may write each of *types* as code: `pretty_type`
        renders none of it for display only (`_display_only`).  An
        inference variable left open (`T$1`, shown as `?`), another
        function's type variable and a refinement, whose predicate the
        rendering elides, are in no program as written, so code that wrote
        one would not apply (PR #1721 review); the fix says it in prose."""
        return not any(_display_only(ty, self.env.type_params)
                       for ty in types)

    def _destructure_fix(self, ty: Type) -> str | None:
        """The fix that destructures a value of *ty* by its own
        constructor: a tuple's `Tuple` over its components, or the one
        constructor of a data type that has one with a field, written out
        where `_fix_writes` can write its types and named otherwise; None
        for any other type."""
        base = base_type(ty)
        if not isinstance(base, AdtType):
            return None
        if base.name == "Tuple":
            if not base.type_args:
                return None
            ctor, fields = "Tuple", base.type_args
        else:
            info = self._match_data_type(base.name)
            if info is None or len(info.constructors) != 1:
                return None
            (ci,) = info.constructors.values()
            ctor, fields = ci.name, self._constructor_fields(ci, ty)
            if not fields:
                return None
        if self._fix_writes(*fields):
            return (f"Destructure the value by its type's constructor: "
                    f"`{_bindings_form(ctor, fields)}`.")
        return (f"Destructure the value by its type's constructor, "
                f"'{ctor}', with one binding per component.")

    def _uncovered_arm(self, case: str, ty: Type) -> str:
        """The pattern an arm for the uncovered constructor *case* of *ty*
        is written with: its name, and a wildcard for each field."""
        info = (self._match_data_type(ty.name)
                if isinstance(ty, AdtType) else None)
        ci = info.constructors.get(case) if info is not None else None
        if ci is None or not ci.field_types:
            return case
        return f"{case}({', '.join('_' for _ in ci.field_types)})"

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

        # `vera.lowering` rules 1 and 2: a handler code generation lowers is
        # for State or Exn (#1597), over a cell or payload it can hold
        # (#1512).  Refused here, where the handler is written; the handler
        # is still checked, so its other diagnostics are reported too.
        if not handler_lowerable(effect_inst.name):
            self._refuse_handler_effect(expr, effect_inst.name)
        elif (isinstance(expr.effect, ast.EffectRef)
              and expr.effect.type_args and effect_inst.type_args):
            # State and Exn take exactly one type argument (E337 above).
            self._check_cell_lowerable(
                expr.effect.type_args[0], effect_inst.name,
                effect_inst.type_args[0], handler=True)

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
            if effect_inst.name == "State":
                self._check_state_clause_lowerable(clause)

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
    # `vera.lowering` rules 1, 2 and 2b at a handler (E340)
    # -----------------------------------------------------------------

    def _refuse_handler_effect(
        self, expr: ast.HandleExpr, effect: str,
    ) -> None:
        """E340: a handler for an effect code generation does not lower
        (rule 1, #1597)."""
        if effect in builtin_effect_names():
            why = (f"{effect}'s operations are implemented by the host, "
                   f"which a handler cannot stand in for")
            fix = (
                f"Remove the handler and perform the {effect} operations "
                f"directly, where the host implements them.  To substitute "
                f"for one, write the substitute as a function and call it "
                f"in place of the operation — for a mock of Http.get, a "
                f"function that returns Ok(\"mock\").  Only "
                f"handle[State<T>] and handle[Exn<E>] are lowered."
            )
        else:
            why = (f"'{effect}' is a user-declared effect, and nothing "
                   f"implements its operations")
            fix = (
                "Keep the state the handler would hold in a "
                "handle[State<T>], or its failure in a handle[Exn<E>], or "
                "pass each operation in as a function value — "
                "type Op = fn(Unit -> Int) effects(pure); then a parameter "
                "@Op, called as apply_fn(@Op.0, ()).  Only "
                "handle[State<T>] and handle[Exn<E>] are lowered."
            )
        self._error(
            expr,
            f"Code generation cannot lower a handler for {effect}: only "
            f"handle[State<T>] and handle[Exn<E>] are lowered.",
            rationale=(
                "A handler resumes the handled body from its clauses, which "
                "needs each operation's continuation.  Code generation builds "
                "that for State<T>, through the host's cell imports, and for "
                "Exn<E>, through WebAssembly exception handling, and for no "
                f"other effect: {why}."
            ),
            fix=fix,
            spec_ref='Chapter 7, Section 7.5 "Effect Handlers"',
            error_code="E340",
        )

    def _check_row_cells(
        self, row: ast.EffectRow, order: tuple[EffectInstance, ...],
    ) -> None:
        """Rule 2 over a declared row: each ``State<T>`` / ``Exn<E>`` entry,
        whose cell code generation registers from the row (E607 / E612
        before #1512).  *order* is the row's resolved instances in source
        order, effect row variables left out, as
        ``_resolve_effect_row_ordered`` builds them."""
        if not isinstance(row, ast.EffectSet):
            return
        instances = iter(order)
        for ref in row.effects:
            if (isinstance(ref, ast.EffectRef)
                    and ref.name in self.env.type_params):
                continue  # an effect row variable resolves to no instance
            inst = next(instances, None)
            if inst is None:
                return
            if (isinstance(ref, ast.EffectRef) and ref.name in ("State", "Exn")
                    and ref.type_args and len(ref.type_args) == 1
                    and len(inst.type_args) == 1):
                self._check_cell_lowerable(
                    ref.type_args[0], ref.name, inst.type_args[0],
                    handler=False)

    def _check_cell_lowerable(
        self, te: ast.TypeExpr, effect: str, cell: Type, *, handler: bool,
    ) -> None:
        """E340: a State cell or Exn payload code generation does not lower
        (rule 2, #1512) — a pair-represented cell, a type with no
        representation, and in a handler an inline refinement — where *te*
        writes it, in a handler or a declared row.

        The type is shown as written, so the fix's wrapper is code to paste:
        a resolved refinement renders with its predicate elided."""
        shown = format_type_canonical(te)
        if handler and not cell_type_spelling_lowerable(te):
            self._error(
                te,
                f"Code generation cannot lower a handler whose {effect} "
                f"type argument is an inline refinement: a handler's cell "
                f"is keyed by a type name.",
                rationale=(
                    "A handle[State<T>] cell, or a handle[Exn<E>] tag, is "
                    "named after the type its argument names, and an inline "
                    "refinement literal names none.  The same refinement "
                    "under a type alias is a name, and is lowered."
                ),
                fix=(
                    f"Name the refinement with an alias and handle that: "
                    f"type Small = {{ @Nat | @Nat.0 < 10 }}; then "
                    f"handle[{effect}<Small>], with the state declared "
                    f"@Small."
                ),
                spec_ref='Chapter 7, Section 7.5.1 "Handler Syntax"',
                error_code="E340",
            )
            return
        if effect == "State" and not state_cell_type_lowerable(cell):
            if is_pair_represented(cell):
                what = ("its value is a (ptr, len) pair, and a cell's host "
                        "imports carry one word")
                box, ctor = (("Text", "T") if shown == "String"
                             else ("Wrapped", "W"))
                fix = (
                    f"Wrap the value in a one-constructor data type and use "
                    f"that as the cell: private data {box} "
                    f"{{ {ctor}({shown}) }} and State<{box}>, writing "
                    f"{ctor}(...) into the cell and matching {ctor}(@{shown}) "
                    f"to read the value back."
                )
            else:
                what = f"{shown} has no runtime representation to store"
                fix = (
                    f"Remove the State<{shown}> cell, or keep a value in it: "
                    f"State<Bool>, or a one-constructor data type such as "
                    f"private data Mark {{ Marked }}."
                )
            self._error(
                te,
                f"Code generation cannot lower a State<{shown}> cell: "
                f"{what}.",
                rationale=(
                    "A State<T> cell's value crosses four host imports whose "
                    "signatures carry one word, so a cell whose value is a "
                    "(ptr, len) pair — String, Array<T> — or has no "
                    "representation — Unit, Never — cannot be stored.  "
                    "Scalar, compound, data and Map cells are lowered."
                ),
                fix=fix,
                spec_ref=('Chapter 7, Section 7.3 "Effect Rows" and '
                          'Chapter 7, Section 7.5.1 "Handler Syntax"'),
                error_code="E340",
            )
        elif effect == "Exn" and not exn_payload_type_lowerable(cell):
            self._error(
                te,
                f"Code generation cannot lower an Exn<{shown}> payload: "
                f"{shown} has no runtime representation to throw.",
                rationale=(
                    "An Exn<E> payload is thrown as a WebAssembly tag's "
                    "parameters, so a payload type with no representation — "
                    "Unit, Never — has nothing to throw."
                ),
                fix=(
                    "Throw a value: Exn<Bool>, or a one-constructor data "
                    "type such as private data Failure { Failed }, thrown "
                    "as throw(Failed)."
                ),
                spec_ref=('Chapter 7, Section 7.3 "Effect Rows" and '
                          'Chapter 7, Section 7.5.1 "Handler Syntax"'),
                error_code="E340",
            )

    def _check_state_clause_lowerable(
        self, clause: ast.HandlerClause,
    ) -> None:
        """E340: a State handler clause code generation cannot inline
        (rule 2b): its body must end in exactly one resume, and its 'with'
        update hold none."""
        refusal = state_clause_refusal(clause)
        if refusal is None:
            return
        if refusal == CLAUSE_RESUME_IN_WITH:
            description = (
                f"Code generation cannot lower this '{clause.op_name}' "
                f"clause: its 'with' update contains resume(...), which has "
                f"no effect there.")
            fix = (
                "Keep the 'with' expression free of resume(...): the clause "
                "body's tail resume(...) is the one continuation.")
        else:
            description = (
                f"Code generation cannot lower this '{clause.op_name}' "
                f"clause: a State clause's body ends in exactly one "
                f"resume(...), and contains no other.")
            fix = (
                "End the body in a single resume(...), and branch inside "
                "its argument rather than around it: "
                "resume(if @Int.0 > 0 then { 1 } else { 2 }).")
        self._error(
            clause,
            description,
            rationale=(
                "Code generation inlines a State clause at each operation "
                "that reaches it, and the clause's resume(v) becomes that "
                "operation's result there, so a clause resumes exactly once, "
                "as its last step.  A resume in each arm of an if or a match "
                "puts a value on a branch typed Unit, and a missing or "
                "repeated one leaves the operation's result wrong."
            ),
            fix=fix,
            spec_ref='Chapter 7, Section 7.5.2 "Handler Semantics"',
            error_code="E340",
        )

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

        A generic template's cells are named by their type parameters, and
        the shadowing judgement is `vera.lowering.shadowing_cell` (rule 5):
        a cell whose type mentions a type parameter may be the family of any
        cell its type unifies with (#1522), so an operation that some
        instantiation would shadow is refused here, conservatively, at the
        template.  The contracts are walked as well as the body: code
        generation lowers a runtime-checked contract like the body.
        """
        roots: list[object] = [decl.body]
        roots.extend(contract_exprs(decl.contracts))
        if not any(isinstance(node, ast.HandleExpr)
                   for root_node in roots
                   for node in _descendants(root_node)):
            return
        walk = _ClauseWalk([], {})
        root = self._row_op_scope(decl.effect)
        for root_node in roots:
            self._clause_op_walk(root_node, root, (), 0, walk)
        seen: set[int] = set()
        for node, why, cell, shadow in walk.refused:
            if id(node) in seen:
                continue
            seen.add(id(node))
            name = getattr(node, "name", "get")
            # About the call, after the checking: a piped operation's is
            # placed at its stage (`_placement`).
            with self._about_the_call(node):
                if why == "shadowed" and shadow is not None and (
                        shadow.family != cell.family):
                    shadow_base = (pretty_type(shadow.type)
                                   if shadow.type is not None
                                   else shadow.family)
                    at = _instantiation_text(cell.type, shadow.type)
                    self._error(
                        node,
                        f"This '{name}' in a handler clause body cannot reach "
                        f"its State<{cell.base}> cell at an instantiation "
                        f"that makes the enclosing State<{shadow_base}> "
                        f"handler's cell the same family: at {at}, that "
                        f"handler shadows it.",
                        rationale=(
                            "An operation written in a handler clause body is "
                            "the ENCLOSING context's (spec §7.5.2), so it "
                            "reaches a State<" + cell.base + "> cell outside "
                            "this handler.  Code generation lowers it where "
                            "the clause is inlined, and its State intrinsics "
                            "address only the innermost cell of one State "
                            "type.  A cell named by a type parameter is that "
                            "family at the instantiations that bind it so — "
                            "here " + at + " — and the checker does not hold "
                            "the instantiations a program makes, so the "
                            "operation is refused for all of them."
                        ),
                        fix=(
                            "Nest handlers whose cells cannot coincide (a "
                            "concrete State type, distinct from every cell "
                            "around it), or move the operation out of this "
                            "clause " + _where_the_cell_is_reached(cell) + "."
                        ),
                        spec_ref='Chapter 7, Section 7.5.2 "Handler Semantics"',
                        error_code="E339",
                    )
                elif why == "shadowed":
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
            # Resolved again for the type: `_check_handle` reported whatever
            # resolving it reports, and an exact repeat collapses (`_error`).
            type=self._resolve_type(te),
            written=type_expr_slot_name(te) or fallback,
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
        self, node: object, scope: _OpScope, pushed: tuple[Cell, ...],
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
            shadow = shadowing_cell(
                cell.identity, pushed[scope.addressable_from:])
            if shadow is not None:
                walk.refused.append((node, "shadowed", cell, shadow))
                return
            clause = cell.clauses.get(op)
            if clause is None or cell.scope is None:
                return
            if depth >= STATE_CLAUSE_INLINE_DEPTH_CAP:
                walk.refused.append((node, "depth", cell, None))
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
        self, node: ast.HandleExpr, scope: _OpScope, pushed: tuple[Cell, ...],
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
            self._clause_op_walk(node.body, body_scope,
                                 (*pushed, cell.identity), depth, walk)
            return
        if isinstance(eff, ast.EffectRef) and eff.name == "Exn":
            # An Exn clause is compiled once, at the handle, in the scope the
            # handle is written in; `throw` reaches no State cell.
            for clause in node.clauses:
                self._clause_op_walk(clause.body, scope, pushed, depth, walk)
            self._clause_op_walk(node.body, scope, pushed, depth, walk)
        # Any other handler is refused at check (E340, `vera.lowering` rule
        # 1), so code generation never lowers it.

    def _state_op_name(
        self, node: ast.FnCall | ast.QualifiedCall,
    ) -> str | None:
        """``get``/``put`` when *node* performs that State operation."""
        if (isinstance(node, ast.QualifiedCall) and node.qualifier == "State"
                and node.name in _STATE_OPS):
            return node.name
        if (isinstance(node, ast.FnCall) and node.name in _STATE_OPS
                and self._bound_function(node) is None):
            return node.name
        return None


def _where_the_cell_is_reached(cell: _ClauseCell) -> str:
    """Where an operation reaches *cell* with no handler between, for E339's
    type-parameter fix: the handled body of the handler that pushes the
    cell, outside the handlers nested in it, or, for a cell the declared row
    gives, the function body outside every handler.  Named, because "the
    handled body" reads as the inner handler's too, where the operation
    reaches the inner cell (PR #1687 review)."""
    if cell.scope is None:
        return (f"into the function body, outside every handler, where it "
                f"reaches the State<{cell.written}> cell the function's "
                f"effects declare")
    return (f"into the handled body of the handle[State<{cell.written}>] "
            f"whose cell it reaches, outside the handlers nested in it")


def _instantiation_text(a: Type | None, b: Type | None) -> str:
    """The binding that makes cells of types *a* and *b* one family, for
    E339's message: ``T = Int`` when one is a bare type parameter."""
    if isinstance(a, TypeVar) and b is not None:
        return f"{a.name} = {pretty_type(b)}"
    if isinstance(b, TypeVar) and a is not None:
        return f"{b.name} = {pretty_type(a)}"
    return "an instantiation that makes the two types one"


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
