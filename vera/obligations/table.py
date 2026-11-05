"""The obligation table (#1695, ROADMAP Stage 27): every obligation site of a
typed program, listed once, which the verifier discharges and code
generation guards.

Built by :func:`build` after :func:`vera.typed.build` and before
:func:`vera.verifier.verify` and :func:`vera.codegen.compile`, with neither
Z3 nor WASM.  A row is one obligation at one node of the typed program:
its kind (today's :data:`vera.obligations.core.ObligationKind`, plus
``effect_bind`` for a binder bound at a narrower effect row), the place
inside the value it is about (``path``), the function it belongs to, the
type it holds the value to, whether a runtime check can be emitted for it
and, where none can, why (``guard``), and where the check is evaluated
(``evaluation``): in the body, at the callee's entry, at the measure's entry
evaluation, at one self tail call's re-evaluation, or inside one guard's
lowering of a refinement predicate.

What lists a row is read from the typed program alone (the Stage 27 design
note, § 2):

* **contracts**: each ``requires``, ``ensures`` and ``decreases`` clause, a
  ``call_pre`` at each call of a user function with a non-trivial
  ``requires`` (one per clause) and at each call of a built-in with a
  declared domain, and an ``assert``;
* **partial operations**: ``/`` and ``%``, a signed ``/`` whose quotient
  can leave the range (``INT_MIN / -1``, #1598), a ``@Nat`` subtraction,
  ``Int`` and ``Nat`` ``+ - *``, ``abs``, an index, the float conversions
  and renderings;
* **narrowings**, from the requirement each node is held to: the component
  an enclosing construction handed it, else the target the checker
  recorded, at the head and at every component path;
* **binders**: a match binder, a sub-pattern binder, a destructure
  component, a handler clause binder, the ``State`` writes, a closure's
  parameters and return, and a binder bound at a narrower effect row
  (#1725, ``effect_bind``);
* **boundaries**: a refined parameter's entry check as a row of the callee,
  the same for a closure's parameters and for a return.

Nothing inside an ``assume`` is a row (#1582).

Whether a row can be guarded is decided here once, from lowering's facts,
and the reason is the row's (design note § 3); code generation emits a
check for every row whose guard is :data:`CHECK` and for no other node
(:meth:`vera.wasm.context.WasmContext._record_check` takes the row).  A
row whose check is another row's — a ``call_pre`` answered by the callee's
``requires`` check, a call argument's narrowing answered by the callee's
entry check, a composite walk's further positions answered by the walk's
first — names that row in ``answered_by`` and emits no check of its own.
"""

from __future__ import annotations

from dataclasses import dataclass, field, replace
from typing import Any, TYPE_CHECKING

from vera import ast, carriers, fold, naming, narrowing
from vera.builtin_domains import BUILTIN_DOMAIN_NAMES
from vera.lowering import quantifier_predicate_refusals, tail_resume_arg
from vera.obligations.core import ObligationKind, expr_text_for
from vera.tail_position import compute_tail_call_sites
from vera.types import (
    FLOAT64,
    INT,
    NAT,
    NEVER,
    AdtType,
    ConcreteEffectRow,
    FunctionType,
    PrimitiveType,
    PureEffectRow,
    RefinedType,
    Type,
    base_type,
    pretty_type,
)

if TYPE_CHECKING:
    from collections.abc import Callable, Iterator

    from vera.typed import TypedProgram


@dataclass(frozen=True)
class Guard:
    """Whether code generation emits a runtime check for a row, and why not
    when it does not."""

    check: bool
    reason: str = ""


CHECK = Guard(True)
TRIVIAL = Guard(False, "the clause is trivially true")


def unguarded(reason: str) -> Guard:
    """A row no check can be emitted for, and why."""
    return Guard(False, reason)


# The reasons, each the fact of lowering it is read from (design note § 3).
REASON_PAIR_ENSURES = (
    "an ensures over a String or Array result is not lowered")
REASON_QUANTIFIER = (
    "a quantified predicate the lowering refuses: only one parameter of "
    "Int or Nat to Bool is lowered")
REASON_EXN_DECREASES = (
    "a decreases on an Exn row has no chain guard: a throw unwinds past "
    "the restore")
REASON_MEASURE_NOT_SLOT = (
    "a measure component that is not a slot of a concrete data type cannot "
    "be ranked")
REASON_MEASURE_NOT_RANKABLE = (
    "a measure component of a parameterised or non-rankable data type "
    "cannot be ranked")
REASON_NESTED_REFINEMENT = "a refinement over a refinement has no guard"
REASON_ERASED_BASE = "a refinement over an erased base has no value to check"
REASON_FUNCTION_BASE = "a refinement over a function type has no binder to check"
REASON_NON_SCALAR_STORE = (
    "a construction store guards only a scalar-based refinement")
REASON_INSIDE_PAYLOAD = (
    "a refinement inside a constructor payload or below a carrier element "
    "is decomposed by no boundary")
REASON_ELEMENT_BELOW_TUPLE = (
    "an element below a tuple component is decomposed by no boundary")
REASON_COMPOSITE_ELEMENT = (
    "a pair-shaped or composite element refinement is not checked by the "
    "element loop")
REASON_EFFECT_ROW = "an effect row has no runtime check"
REASON_NOT_REFINED = "the type is no refinement"
REASON_STRING_SLICE = "string_slice clamps its @Nat argument"
REASON_UNEVALUATED = "inside a clause no check evaluates"
REASON_CLAUSE_NOT_INLINED = (
    "the handler clause is inlined at no operation call, so it never runs")
REASON_HANDLE_VALUE = (
    "code generation emits no store check for a value produced inside a "
    "handle body")

#: The built-ins whose call is a float conversion with a domain (one
#: ``float_to_int_domain`` row at the call).
FLOAT_CONVERSIONS = frozenset(
    {"float_to_int", "floor", "ceil", "round", "float_to_string"})
#: The built-ins whose ``@Nat`` formal takes no guard (#475: `string_slice`
#: clamps).
NAT_ARG_UNGUARDED_BUILTINS = frozenset({"string_slice"})
#: The scalar bases an element loop checks a refinement over.
_ELEMENT_LOOP_BASES = frozenset({"Int", "Nat", "Float64", "Bool", "Byte"})
_RANKABLE_SCALARS = frozenset(
    {"Int", "Nat", "Bool", "Float64", "Byte", "String", "Unit"})
_UNRANKABLE_HEADS = frozenset(
    {"Tuple", "Array", "Map", "Set", "Option", "Result", "Future"})

Evaluation = tuple[object, ...]
#: The row is evaluated in the body, where its node is.
BODY: Evaluation = ("body",)
#: A parameter's entry check, evaluated at the callee's entry.
ENTRY: Evaluation = ("entry",)
#: A return's check, evaluated at the boundary the value leaves through.
RETURN: Evaluation = ("return",)
#: A measure's operations, evaluated at the function's entry.
MEASURE: Evaluation = ("measure",)


@dataclass(frozen=True)
class Source:
    """What a binder row takes apart: the value, and the constructor steps
    ``(constructor, field)`` down to the component the binder binds (the
    verifier's term for the row)."""

    value: ast.Expr
    steps: tuple[tuple[str, int], ...] = ()


@dataclass(frozen=True)
class Row:
    """One obligation site of the typed program."""

    id: int
    node: ast.Node
    kind: ObligationKind
    fn: str
    target: Type | None
    guard: Guard
    path: tuple[str, ...] = ()
    evaluation: Evaluation = BODY
    #: For a binder row: the value the binder takes apart.
    source: Source | None = None
    #: The row whose check answers this one, where this row emits none of
    #: its own (a ``call_pre`` names the callee's ``requires`` row; a call
    #: argument's narrowing names the callee's entry row; a composite
    #: walk's further positions name the walk's first).
    answered_by: int | None = None
    #: For a ``nat_bind`` row at a construction's component: whether the
    #: requirement reached the node from the construction alone, the
    #: checker having recorded no `Nat` target at it (#1542's shape); such
    #: a check is the composite-coercion emitter's, every other narrowing's
    #: the sign guard's.
    handed: bool = False
    #: For the first row of a composite walk (an opaque value, a binder):
    #: the differing tree the walk reads (:func:`vera.narrowing.differing_tree`),
    #: less the tuple positions a boundary's entry rows answer.  The walk's
    #: one check answers this row and, through ``answered_by``, the rows of
    #: the tree's other positions.
    tree: narrowing.Coercion | None = None
    #: The identity fields the warm session keys on
    #: (:meth:`vera.obligations.core.ProofObligation.content_key`): the
    #: function, the kind, the expression text, the span's line and
    #: column.  The file is the function's module, which the session adds.
    content_key: tuple[str, str, str, int, int] = ("", "", "", 0, 0)


#: The ``answered_by`` of a row checked at the entry of the closure the
#: call reaches (a `Tuple` component or a refined formal of a closure
#: passed as a slot), which every closure of the type guards and no row
#: the table lists names.
ANSWERED_AT_CLOSURE_ENTRY = -1


@dataclass
class ObligationTable:
    """Every row of one typed program, in the order they were listed."""

    rows: list[Row] = field(default_factory=list)
    #: The rows each function lists, by the identity of the function's body
    #: (a clone's own body; the verifier verifies a clone renamed to its
    #: generic, which keeps the body): what the verifier discharges when it
    #: has verified that function.
    by_body: dict[int, list[int]] = field(default_factory=dict)
    _at: dict[object, list[Row]] = field(default_factory=dict, repr=False)
    _refinement_guard: Callable[[RefinedType], Guard] | None = field(
        default=None, repr=False)

    def refinement_guard(self, ty: Type | None) -> Guard:
        """Whether a check guards a value held to the refinement *ty* (the
        table's rule, which every narrowing row into *ty* carries): what
        makes a binder's predicate a fact for the rest of its scope."""
        if not isinstance(ty, RefinedType) or self._refinement_guard is None:
            return unguarded(REASON_NOT_REFINED)
        return self._refinement_guard(ty)

    @staticmethod
    def _key(node: ast.Node) -> object:
        return (node.node_id if node.node_id is not None
                else ("object", id(node)))

    def index(self) -> None:
        """Index the rows by node, after the rows are listed."""
        self._at = {}
        for row in self.rows:
            self._at.setdefault(self._key(row.node), []).append(row)

    def rows_at(self, node: ast.Node) -> list[Row]:
        """The rows standing at *node*."""
        return list(self._at.get(self._key(node), ()))

    def rows_of(
        self, node: ast.Node, kind: str, path: tuple[str, ...] | None = (),
        evaluation: Evaluation | None = BODY,
    ) -> list[Row]:
        """The rows of *kind* at *node*, at *path* (any when ``None``) and
        *evaluation* (any when ``None``)."""
        return [row for row in self._at.get(self._key(node), ())
                if row.kind == kind
                and (path is None or row.path == path)
                and (evaluation is None or row.evaluation == evaluation)]

    def row(
        self, node: ast.Node, kind: str, path: tuple[str, ...] | None = (),
        evaluation: Evaluation | None = BODY,
    ) -> Row | None:
        """The first row :meth:`rows_of` lists, or ``None``."""
        rows = self.rows_of(node, kind, path, evaluation)
        return rows[0] if rows else None

    def by_id(self, row_id: int) -> Row:
        return self.rows[row_id]

    def rows_of_function(self, decl: ast.FnDecl) -> list[Row] | None:
        """The rows *decl*'s body lists, or ``None`` for a function the
        table does not list (nothing of *decl* is a row)."""
        if decl.body is None:
            return None
        ids = self.by_body.get(id(decl.body))
        return None if ids is None else [self.rows[i] for i in ids]

    def answered(self, row: Row) -> Row | None:
        """The row whose check answers *row*: *row* itself when it has its
        own, else the end of its ``answered_by`` chain; ``None`` for a row
        answered at a closure's entry (:data:`ANSWERED_AT_CLOSURE_ENTRY`)."""
        seen: set[int] = set()
        while row.answered_by is not None and row.id not in seen:
            if row.answered_by == ANSWERED_AT_CLOSURE_ENTRY:
                return None
            seen.add(row.id)
            row = self.rows[row.answered_by]
        return row


def build(typed: TypedProgram) -> ObligationTable:
    """The obligation table of *typed*."""
    builder = _Builder(typed)
    builder.build()
    table = ObligationTable(builder.finished(), by_body=builder.by_body,
                            _refinement_guard=builder._refinement_guardable)
    table.index()
    return table


# =====================================================================
# Type readers
# =====================================================================


def _is_nat(ty: Type | None) -> bool:
    return ty == NAT or (isinstance(ty, RefinedType) and ty.base == NAT)


def _is_int(ty: Type | None) -> bool:
    return ty == INT or (isinstance(ty, RefinedType) and ty.base == INT)


def _strip(ty: Type | None) -> Type | None:
    while isinstance(ty, RefinedType):
        ty = ty.base
    return ty


def _same_refinement(a: Type | None, b: Type) -> bool:
    """Whether the source type *a* already carries the target refinement
    *b* exactly."""
    if not isinstance(a, RefinedType) or not isinstance(b, RefinedType):
        return False
    return a.predicate == b.predicate and base_type(a) == base_type(b)


def _effect_set(row: object) -> frozenset[tuple[str, tuple[str, ...]]] | None:
    if isinstance(row, PureEffectRow):
        return frozenset()
    if isinstance(row, ConcreteEffectRow) and row.row_var is None:
        return frozenset(
            (e.name, tuple(pretty_type(a) for a in e.type_args))
            for e in row.effects)
    return None


def _pattern_nodes(pat: ast.Pattern) -> Iterator[ast.Pattern]:
    yield pat
    if isinstance(pat, ast.ConstructorPattern):
        for sub in pat.sub_patterns:
            yield from _pattern_nodes(sub)


def _pattern_steps(
    pat: ast.ConstructorPattern, steps: tuple[tuple[str, int], ...] = (),
) -> Iterator[tuple[ast.BindingPattern, tuple[tuple[str, int], ...]]]:
    """Every binding pattern under *pat* with the constructor steps down to
    the field it binds."""
    for i, sub in enumerate(pat.sub_patterns):
        here = steps + ((pat.name, i),)
        if isinstance(sub, ast.BindingPattern):
            yield sub, here
        elif isinstance(sub, ast.ConstructorPattern):
            yield from _pattern_steps(sub, here)


def return_leaves(body: ast.Expr) -> tuple[ast.Expr, ...]:
    """The leaves of *body* code generation lowers a return guard at
    separately: through a block's tail, both branches of an ``if`` (none
    for an ``if`` without ``else``) and every arm of a ``match``; any other
    form, a ``handle`` included, is one leaf.  The table lists a ``@Nat``
    return's narrowing rows one per leaf, and code generation guards each
    leaf by its row."""
    if isinstance(body, ast.Block):
        return () if body.expr is None else return_leaves(body.expr)
    if isinstance(body, ast.IfExpr):
        if body.else_branch is None:
            return ()
        return (return_leaves(body.then_branch)
                + return_leaves(body.else_branch))
    if isinstance(body, ast.MatchExpr):
        out: tuple[ast.Expr, ...] = ()
        for arm in body.arms:
            out += return_leaves(arm.body)
        return out
    return (body,)


def _reads_hand_down(expr: ast.Expr) -> bool:
    """Whether a construction with no recorded target reads the component
    type an enclosing `Tuple` argument, array-literal element or
    ``map_insert`` value handed it (code generation's hand-down, #1606): a
    `Tuple`, an array literal, a ``map_insert``."""
    return ((isinstance(expr, ast.ConstructorCall) and expr.name == "Tuple")
            or isinstance(expr, ast.ArrayLit)
            or (isinstance(expr, ast.FnCall) and expr.name == "map_insert"))


def _expr_text(node: ast.Node) -> str:
    if isinstance(node, (ast.Expr, ast.Contract)):
        return expr_text_for(node)
    if isinstance(node, ast.TypeExpr):
        return ast.format_type_expr(node)
    if isinstance(node, ast.BindingPattern):
        return ast.format_type_expr(node.type_expr)
    return type(node).__name__


# =====================================================================
# The builder
# =====================================================================


class _Builder:
    """Lists the rows of one typed program (:func:`build`)."""

    def __init__(self, typed: TypedProgram) -> None:
        self.typed = typed
        self.rows: list[Row] = []
        self.by_body: dict[int, list[int]] = {}
        self._body: list[int] = []
        self.fn_decls: dict[str, ast.FnDecl] = {}
        self.fn_requires: dict[str, list[ast.Requires]] = {}
        self.prelude: set[str] = set()
        #: Nodes whose narrowing rows are listed, with the evaluation they
        #: are listed in (a join's leaves are reached once through the join
        #: and once as children).
        self.done: set[object] = set()
        #: ``id(arg)`` of a call argument or a return leaf to the boundary
        #: type expression whose entry rows answer its rows.
        self._boundary: dict[int, ast.TypeExpr] = {}
        #: ``id(arg)`` of an argument passed to a closure held in a slot,
        #: whose boundary rows are the entry rows of whichever closure the
        #: call reaches (:data:`ANSWERED_AT_CLOSURE_ENTRY`).
        self._closure_args: set[int] = set()
        #: ``(id(node), path)`` of an answering row to its id: a
        #: ``requires`` clause's row, a boundary's entry rows.
        self._answerers: dict[tuple[int, tuple[str, ...]], int] = {}
        #: ``(row index, answering node, path)`` resolved at the end.
        self._pending: list[tuple[int, ast.Node, tuple[str, ...]]] = []
        #: ``id(expr)`` of a `throw` payload and its value leaves: a refined
        #: payload's predicate guard is its only one (#1268), the sign guard
        #: standing only where the payload is no refinement.
        self._predicate_only: set[int] = set()
        #: ``id(arg)`` of a built-in's argument no guard checks, to why.
        self._arg_reason: dict[int, str] = {}
        #: ``id(expr)`` of a value the walk hands a requirement to from
        #: outside its parent (a `get` clause's tail ``resume`` argument,
        #: held to the cell).
        self._handed_override: dict[int, Type] = {}
        #: The `State` handlers whose bodies the walk is inside, innermost
        #: last: a `get` or `put` written there is the innermost's.
        self._handler_stack: list[ast.HandleExpr] = []
        #: ``id(handle)`` of a `State` handler to the operation calls it
        #: handles, each with the evaluation it was met in: the sites its
        #: clauses are inlined at.
        self._handled: dict[int, list[tuple[ast.Expr, Evaluation]]] = {}
        self._unevaluated: list[str] = []
        #: The reason a requirement handed into a `handle`'s value carries:
        #: code generation hands no requirement there (its coercion walk
        #: stops at the handle), so a row the hand-down alone lists has no
        #: check (one entry per `expr_rows` call; `None` where the
        #: requirement is the node's own).
        self._via: list[str | None] = []
        self._evaluation: list[Evaluation] = [BODY]
        #: ``id`` of a written refinement's predicate to its base type
        #: expression, built on first need (:meth:`_inline_base`).
        self._refinement_bases: dict[int, ast.TypeExpr] | None = None
        #: ``id`` of a quantifier's predicate, a closure lowered inline.
        self._inline_closures: set[int] = set()
        #: The closures whose rows are listed (:meth:`walk`).
        self._closures_listed: set[object] = set()
        #: The refinement predicates whose rows are being listed, innermost
        #: last (:meth:`_predicate_rows`).
        self._predicate_chain: list[object] = []
        self.fn = ""

    # -- type readers ---------------------------------------------------

    def sem(self, node: ast.Node) -> Type | None:
        return self.typed.semantic_type(node)

    def target(self, node: ast.Node) -> Type | None:
        return self.typed.target_type(node)

    def effective(self, e: ast.Expr) -> Type | None:
        t = self.target(e)
        return t if t is not None else self.sem(e)

    def is_nat_expr(self, e: ast.Expr) -> bool:
        """The reading of a ``@Nat`` under the post-fact rule: a slot
        declared ``@Nat`` is one (its binder's row guards it), else the
        checker's type decides."""
        if isinstance(e, ast.SlotRef) and e.type_name == "Nat":
            return True
        return _is_nat(self.sem(e))

    def narrows_nat(self, e: ast.Expr) -> bool:
        return narrowing.nat_narrowing(e, self.is_nat_expr)

    def narrows_nat_join(self, e: ast.Expr) -> bool:
        """A join narrows where any value leaf does: the checker types the
        join at the expected type and masks a narrowing arm.  A leaf the
        checker types `Never` (a `throw`, a join of such leaves) yields no
        value, so it narrows nothing, and a join whose every leaf is
        `Never` narrows nothing either: there is no value to prove a fact
        of or to guard."""
        return any(self.narrows_nat(leaf) for leaf in narrowing.value_leaves(e)
                   if self.sem(leaf) != NEVER)

    def ftypes(self, ctor: str, ty: Type | None) -> tuple[Type, ...] | None:
        return self.typed.field_types_at(ctor, ty)

    def ctors(self, name: str) -> tuple[str, ...]:
        return self.typed.constructors_of(name)

    def chain(self, ty: Type | None) -> narrowing.RefinementChain | None:
        if ty is None:
            return None
        chain = naming.refined_type_chain(ty)
        if chain is None:
            return (pretty_type(ty), frozenset())
        base, predicates = chain
        return (pretty_type(base),
                frozenset(ast.format_expr(p) for p in predicates))

    def _contains_refinement(self, ty: Type | None,
                             seen: frozenset[str] = frozenset()) -> bool:
        if isinstance(ty, RefinedType):
            return True
        if not isinstance(ty, AdtType):
            return False
        key = repr(ty)
        if key in seen:
            return False
        deeper = seen | {key}
        if any(self._contains_refinement(a, deeper) for a in ty.type_args):
            return True
        for ctor in self.ctors(ty.name):
            fs = self.ftypes(ctor, ty)
            if fs and any(self._contains_refinement(f, deeper) for f in fs):
                return True
        return False

    def _holds_float(self, ty: Type) -> bool:
        seen: set[str] = set()
        stack: list[Type] = [ty]
        while stack:
            t = stack.pop()
            if isinstance(t, RefinedType):
                stack.append(t.base)
                continue
            if t == FLOAT64:
                return True
            if not isinstance(t, AdtType):
                continue
            k = pretty_type(t)
            if k in seen:
                continue
            seen.add(k)
            stack.extend(t.type_args)
            for ctor in self.ctors(t.name):
                stack.extend(self.ftypes(ctor, t) or ())
        return False

    # -- rows -----------------------------------------------------------

    def add(
        self, kind: ObligationKind, node: ast.Node, *,
        target: Type | None = None, guard: Guard = CHECK,
        path: tuple[str, ...] = (), evaluation: Evaluation | None = None,
        source: Source | None = None, answer: ast.Node | None = None,
        answer_path: tuple[str, ...] = (),
        answer_row: int | None = None, handed: bool = False,
    ) -> int:
        """List one row; returns its id.  *answer* names the node whose
        row at *answer_path* answers this one (resolved once every row is
        listed); *answer_row* names the row itself."""
        if guard.check and self._unevaluated:
            guard = unguarded(self._unevaluated[-1])
        if (guard.check and kind in ("refine_bind", "nat_bind")
                and self._via and self._via[-1] is not None):
            guard = unguarded(self._via[-1])
        # A piped call's row stands at its stage, where it is written (#1641).
        stage = getattr(node, "stage_span", None)
        span = stage if stage is not None else node.span
        row = Row(
            id=len(self.rows), node=node, kind=kind, fn=self.fn,
            target=target, guard=guard, path=path,
            evaluation=self._evaluation[-1] if evaluation is None else evaluation,
            source=source, answered_by=answer_row, handed=handed,
            content_key=(self.fn, kind, _expr_text(node),
                         span.line if span is not None else 0,
                         span.column if span is not None else 0),
        )
        self.rows.append(row)
        if self._body:
            self.by_body[self._body[-1]].append(row.id)
        if answer is not None:
            self._pending.append((row.id, answer, answer_path))
        if (guard.check and answer is None and answer_row is None
                and isinstance(target, RefinedType)):
            self._predicate_rows(row.id, target)
        return row.id

    def _predicate_rows(self, guard_row: int, target: RefinedType) -> None:
        """The operations of *target*'s predicate, evaluated once by the
        guard of row *guard_row*: a row each, keyed by that evaluation."""
        if isinstance(target.base, RefinedType):
            return
        # A predicate whose closure's signature holds the refinement again
        # (#1234) would list its own rows for ever; code generation refuses
        # the cycle (E602), and its chain lists them once.
        key = ObligationTable._key(target.predicate)
        if key in self._predicate_chain:
            return
        self._predicate_chain.append(key)
        self._evaluation.append(("predicate", guard_row))
        try:
            self.walk(target.predicate, None, in_contract=True)
        finally:
            self._evaluation.pop()
            self._predicate_chain.pop()

    def _quantifier_layer_rows(
        self, expr: ast.ForallExpr | ast.ExistsExpr,
    ) -> None:
        """The operations of each refinement layer of a quantifier's index
        type, which the lowering evaluates at every index to test the range
        (#1506): a row each, keyed by the quantifier's evaluation."""
        ty = self.sem(expr.binding_type)
        self._evaluation.append(("quantifier", expr.node_id))
        try:
            while isinstance(ty, RefinedType):
                self.walk(ty.predicate, None, in_contract=True)
                ty = ty.base
        finally:
            self._evaluation.pop()

    def finished(self) -> list[Row]:
        """The rows with every pending answer resolved."""
        rows = self.rows
        for index, node, path in self._pending:
            answerer = self._answerers.get((id(node), path))
            if answerer is not None and rows[index].answered_by is None:
                rows[index] = replace(rows[index], answered_by=answerer)
        return rows

    def _answers(self, node: ast.Node, path: tuple[str, ...],
                 row_id: int) -> None:
        self._answerers.setdefault((id(node), path), row_id)

    # -- the program ----------------------------------------------------

    def build(self) -> None:
        typed = self.typed
        linked = typed.linked
        decls = [tld.decl for tld in linked.program.declarations
                 if isinstance(tld.decl, ast.FnDecl)]
        for mod in linked.modules:
            decls.extend(tld.decl for tld in mod.program.declarations
                         if isinstance(tld.decl, ast.FnDecl))
        # The prelude's functions compile into the module like the user's,
        # so their checks name rows too; `prelude` tells them apart.
        prelude_decls = [tld.decl for tld in linked.prelude
                         if isinstance(tld.decl, ast.FnDecl)]
        for d in prelude_decls:
            self.prelude.add(d.name)
        for d in (*decls, *prelude_decls):
            self._index_fn(d)
        for inst in typed.instances:
            if inst.clone is not None:
                self._index_fn(inst.clone)
        # A generic's template compiles too (its checks reach the module
        # where its body lowers at the erased types), so it has rows of its
        # own beside each clone's.
        for d in (*decls, *prelude_decls):
            self.function(d)
        for inst in typed.instances:
            if inst.clone is not None:
                self.function(inst.clone, name=inst.name)

    def _index_fn(self, d: ast.FnDecl) -> None:
        self.fn_decls[d.name] = d
        self.fn_requires[d.name] = [
            c for c in d.contracts
            if isinstance(c, ast.Requires) and not self._trivial(c)]
        for h in d.where_fns or ():
            self._index_fn(h)

    # -- one function ---------------------------------------------------

    def function(self, d: ast.FnDecl, name: str | None = None) -> None:
        saved = self.fn
        self.fn = d.name if name is None else name
        if d.body is not None:
            self._body.append(id(d.body))
            self.by_body.setdefault(id(d.body), [])
        try:
            self._function(d)
        finally:
            self.fn = saved
            if d.body is not None:
                self._body.pop()

    def _function(self, d: ast.FnDecl) -> None:
        ret_ty = self.sem(d.return_type)
        measure: tuple[ast.Decreases, Guard] | None = None
        for c in d.contracts:
            if isinstance(c, ast.Requires):
                guard = TRIVIAL if self._trivial(c) else CHECK
                row_id = self.add("requires", c, guard=guard)
                self._answers(c, (), row_id)
                self._walk_clause(c.expr, d, guard)
            elif isinstance(c, ast.Ensures):
                guard = CHECK
                if self._trivial(c):
                    guard = TRIVIAL
                elif self._pair(ret_ty):
                    guard = unguarded(REASON_PAIR_ENSURES)
                elif self._has_quantifier(c.expr) and self._quantifier_refused(c.expr):
                    guard = unguarded(REASON_QUANTIFIER)
                self.add("ensures", c, guard=guard)
                self._walk_clause(c.expr, d, guard)
            elif isinstance(c, ast.Decreases) and c.exprs:
                guard = self._decreases_guard(d, c)
                self.add("decreases", c, guard=guard)
                measure = (c, guard)
        for p in d.params:
            self._entry_rows(p, self.sem(p))
        if d.body is not None:
            self._boundary_rows(d.body, d.return_type)
            self.walk(d.body, d, handed=ret_ty, under_join=True)
            self._return_rows(d.return_type, ret_ty, d.body)
        if measure is not None:
            self._measure_rows(d, *measure, epilogue=self._has_epilogue(d, ret_ty))
        # A generic helper's template compiles too, as a top-level
        # generic's does (its clones are the instances'), so it has rows.
        for h in d.where_fns or ():
            self.function(h)

    def _has_epilogue(self, d: ast.FnDecl, ret_ty: Type | None) -> bool:
        """Whether *d*'s return runs a check after the body (a non-trivial
        ``ensures``, a refined return, a guarded tuple component or carrier
        element of the return): then no self tail call transfers, every
        hop re-enters through the entry check, and the measure is
        re-evaluated at no call."""
        # The function's own return boundary: its head row at the body, its
        # component and element rows at the return type; a closure's
        # return rows inside the body are the closure's epilogue.
        own = {ObligationTable._key(d.return_type)}
        if d.body is not None:
            own.add(ObligationTable._key(d.body))
        boundary = any(
            row.evaluation == RETURN and row.guard.check
            and row.kind == "refine_bind" and ObligationTable._key(row.node) in own
            for row in self.rows)
        if self._pair(ret_ty):
            return boundary
        ensures = any(isinstance(c, ast.Ensures) and not self._trivial(c)
                      for c in d.contracts)
        return ensures or boundary

    def _walk_clause(self, expr: ast.Expr, d: ast.FnDecl, guard: Guard) -> None:
        """The operations inside a clause: rows evaluated where the clause
        is; none evaluated where no check of the clause runs."""
        if guard.check:
            self.walk(expr, d, in_contract=True)
            return
        self._unevaluated.append(
            guard.reason if guard is not TRIVIAL else REASON_UNEVALUATED)
        try:
            self.walk(expr, d, in_contract=True)
        finally:
            self._unevaluated.pop()

    @staticmethod
    def _trivial(c: ast.Contract) -> bool:
        return (isinstance(c, (ast.Requires, ast.Ensures))
                and isinstance(c.expr, ast.BoolLit) and c.expr.value)

    def _measure_rows(
        self, d: ast.FnDecl, c: ast.Decreases, guard: Guard, *, epilogue: bool,
    ) -> None:
        """The measure's operations at the entry evaluation, and the
        clause and its operations again at each self tail call the
        function transfers to (the spliced prefix): none where an epilogue
        runs after the body, since every hop then re-enters through the
        entry check."""
        if not guard.check:
            self._unevaluated.append(guard.reason)
        try:
            self._evaluation.append(MEASURE)
            try:
                for e in c.exprs:
                    self.walk(e, d, in_contract=True)
            finally:
                self._evaluation.pop()
            if d.body is None or epilogue:
                return
            tail_ids = compute_tail_call_sites(d, None)
            for n in fold.walk(d.body):
                if not (isinstance(n, ast.FnCall) and n.name == d.name
                        and id(n) in tail_ids):
                    continue
                self._evaluation.append(("measure_call", n.node_id))
                try:
                    self.add("decreases", c, guard=guard)
                    for e in c.exprs:
                        self.walk(e, d, in_contract=True)
                finally:
                    self._evaluation.pop()
        finally:
            if not guard.check:
                self._unevaluated.pop()

    def _pair(self, ty: Type | None) -> bool:
        b = _strip(ty)
        return (isinstance(b, PrimitiveType) and b.name == "String") or (
            isinstance(b, AdtType) and b.name == "Array")

    def _has_quantifier(self, e: ast.Expr) -> bool:
        return any(isinstance(n, (ast.ForallExpr, ast.ExistsExpr))
                   for n in fold.walk(e))

    def _quantifier_refused(self, e: ast.Expr) -> bool:
        for n in fold.walk(e):
            if isinstance(n, (ast.ForallExpr, ast.ExistsExpr)):
                pred = n.predicate
                if not isinstance(pred, ast.AnonFn):
                    return True
                param = self.sem(pred.params[0]) if pred.params else None
                result = self.sem(pred.return_type)
                if quantifier_predicate_refusals(len(pred.params), param, result):
                    return True
        return False

    def _rankable(self, ty: Type | None, seen: frozenset[str] = frozenset()) -> bool:
        b = _strip(ty)
        if isinstance(b, PrimitiveType):
            return b.name in ("Int", "Nat")
        if not isinstance(b, AdtType) or b.type_args:
            return False
        if b.name in seen:
            return True
        for ctor in self.ctors(b.name):
            for f in self.ftypes(ctor, b) or ():
                fb = _strip(f)
                if isinstance(fb, PrimitiveType) and fb.name in _RANKABLE_SCALARS:
                    continue
                if (isinstance(fb, AdtType) and not fb.type_args
                        and fb.name not in _UNRANKABLE_HEADS):
                    if not self._rankable(fb, seen | {b.name}):
                        return False
                    continue
                return False
        return bool(self.ctors(b.name))

    def _decreases_guard(self, d: ast.FnDecl, c: ast.Decreases) -> Guard:
        if isinstance(d.effect, ast.EffectSet) and any(
                isinstance(e, ast.EffectRef) and e.name == "Exn"
                for e in d.effect.effects):
            return unguarded(REASON_EXN_DECREASES)
        for e in c.exprs:
            ty = self.sem(e)
            b = _strip(ty)
            if isinstance(b, PrimitiveType) and b.name in ("Int", "Nat"):
                continue
            if ty is None:
                continue
            if not isinstance(e, ast.SlotRef):
                return unguarded(REASON_MEASURE_NOT_SLOT)
            if not self._rankable(ty):
                return unguarded(REASON_MEASURE_NOT_RANKABLE)
        return CHECK

    # -- boundaries -----------------------------------------------------

    def _entry_rows(self, te: ast.TypeExpr, ty: Type | None) -> None:
        """A refined parameter's entry check: head, tuple components,
        carrier elements (the boundary decomposition code generation
        makes), rows of the callee."""
        if ty is None:
            return
        if isinstance(ty, RefinedType):
            row_id = self.add("refine_bind", te, target=ty,
                              guard=self._refinement_guardable(ty),
                              evaluation=ENTRY)
            self._answers(te, (), row_id)
        self._component_entry_rows(te, _strip(ty), ())

    def _component_entry_rows(
        self, te: ast.TypeExpr, b: Type | None, path: tuple[str, ...],
        depth: int = 0, evaluation: Evaluation = ENTRY,
    ) -> None:
        if depth > 16:
            return
        if isinstance(b, AdtType) and b.name == "Tuple":
            for i, comp in enumerate(b.type_args):
                p = path + (f"Tuple.{i}",)
                if isinstance(comp, RefinedType):
                    row_id = self.add("refine_bind", te, target=comp, path=p,
                                      guard=self._refinement_guardable(comp),
                                      evaluation=evaluation)
                    self._answers(te, p, row_id)
                elif comp == NAT:
                    row_id = self.add("refine_bind", te, target=NAT, path=p,
                                      evaluation=evaluation)
                    self._answers(te, p, row_id)
                self._component_entry_rows(te, _strip(comp), p, depth + 1,
                                           evaluation)
        elif isinstance(b, AdtType) and b.name in carriers.CARRIER_POSITIONS:
            for carrier in carriers.element_carriers(b):
                el = carrier.element_type
                if not self._contains_refinement(el):
                    continue
                p = path + (carrier.kind,)
                if path:
                    guard = unguarded(REASON_ELEMENT_BELOW_TUPLE)
                elif (isinstance(el, RefinedType)
                        and getattr(_strip(el), "name", None) in _ELEMENT_LOOP_BASES):
                    guard = self._refinement_guardable(el)
                else:
                    guard = unguarded(REASON_COMPOSITE_ELEMENT)
                row_id = self.add("refine_bind", te,
                                  target=el if isinstance(el, RefinedType) else None,
                                  path=p, guard=guard, evaluation=evaluation)
                self._answers(te, p, row_id)

    def _boundary_rows(self, body: ast.Expr, te: ast.TypeExpr) -> None:
        """Mark the body's return leaves as answered by the return
        boundary's entry rows (their tuple components and elements)."""
        for leaf in narrowing.value_leaves(body):
            self._boundary.setdefault(id(leaf), te)

    def _return_rows(self, te: ast.TypeExpr, ret_ty: Type | None,
                     body: ast.Expr) -> None:
        """The return boundary: a refined return's head row at the body,
        its component rows at the return type, and a ``@Nat`` return's
        narrowing rows, one per leaf code generation guards."""
        if ret_ty is None:
            return
        # A leaf of type `Never` (a `throw`) yields no value, so it is no
        # row; a body that yields none has no return row at all.
        if isinstance(ret_ty, RefinedType):
            if self.sem(body) != NEVER:
                self.add("refine_bind", body, target=ret_ty,
                         guard=self._refinement_guardable(ret_ty),
                         evaluation=RETURN)
        elif _is_nat(ret_ty):
            for leaf in return_leaves(body):
                if self.sem(leaf) != NEVER and self.narrows_nat(leaf):
                    self.add("nat_bind", leaf, target=NAT, evaluation=RETURN)
        self._component_entry_rows(te, _strip(ret_ty), (), evaluation=RETURN)

    def _refinement_guardable(
        self, ty: RefinedType, construction: bool = False,
    ) -> Guard:
        if isinstance(ty.base, RefinedType):
            return unguarded(REASON_NESTED_REFINEMENT)
        b = _strip(ty)
        if isinstance(b, PrimitiveType) and b.name == "Unit":
            return unguarded(REASON_ERASED_BASE)
        if isinstance(b, FunctionType) and self._inline_base(ty):
            # `naming.refinement_binder_parts` names no binder for a base
            # written inline (`{ @fn(A -> B) … | P }`), so the guard's
            # lowering has nothing to bind the predicate to; an alias base
            # (`{ @F | P }`) names one, and is guarded.
            return unguarded(REASON_FUNCTION_BASE)
        if (isinstance(b, AdtType) and b.name == "Future" and b.type_args
                and _strip(b.type_args[0]) == PrimitiveType("Unit")):
            return unguarded(REASON_ERASED_BASE)
        if construction and not (
                isinstance(b, PrimitiveType)
                and b.name in narrowing.REFINED_CONSTRUCTION_SCALAR_BASES):
            return unguarded(REASON_NON_SCALAR_STORE)
        return CHECK

    def _inline_base(self, ty: RefinedType) -> bool:
        """Whether *ty*'s refinement is written over a base that is no
        type name, by the written refinement whose predicate it carries."""
        if self._refinement_bases is None:
            bases: dict[int, ast.TypeExpr] = {}
            seen: set[int] = set()

            def visit(node: object) -> None:
                if isinstance(node, ast.RefinementType):
                    bases[id(node.predicate)] = node.base_type
                if isinstance(node, ast.Node):
                    if id(node) in seen:
                        return
                    seen.add(id(node))
                    for name in node.__dataclass_fields__:
                        visit(getattr(node, name))
                elif isinstance(node, (tuple, list)):
                    for item in node:
                        visit(item)

            linked = self.typed.linked
            visit(linked.program)
            for mod in linked.modules:
                visit(mod.program)
            visit(tuple(linked.prelude))
            for inst in self.typed.instances:
                visit(inst.clone)
            self._refinement_bases = bases
        base = self._refinement_bases.get(id(ty.predicate))
        return base is not None and not isinstance(base, ast.NamedType)

    # -- the walk -------------------------------------------------------

    def walk(
        self, expr: object, d: ast.FnDecl | None, handed: Type | None = None,
        in_contract: bool = False, in_closure: bool = False,
        under_join: bool = False, store: bool = False,
        inplace: Type | None = None, fallback: bool = False,
        nat_handed: Type | None = None, via: str | None = None,
    ) -> None:
        """List the rows under *expr*.

        Two requirements reach a node from above.  *handed* is the one a
        refinement row reads: the component an enclosing construction or
        join holds *expr* to, of the construction's recorded target or,
        with *fallback*, of its own type (it recorded no target), which a
        target the checker recorded at *expr* itself overrides.
        *nat_handed* is the one a `Nat` row reads, code generation's
        (:mod:`vera.wasm.coercion`): handed down only along the differing
        tree of the enclosing requirement, so a node below no position of
        it reads its own recorded target.  *store* marks a construction's
        component.  *inplace* is the component type the store of *expr*
        reads for itself: its construction's own target's, or the one a
        `Tuple` argument, an array-literal element or a ``map_insert``
        value hands through the joins to the `Tuple`, literal or
        ``map_insert`` it reaches (code generation's hand-down, #1606); a
        component the requirement makes a `Nat` that its store does not
        read as one is a composite coercion's (`Row.handed`).  *via* is the
        reason a requirement handed into a `handle`'s value carries
        (`REASON_HANDLE_VALUE`): the rows it alone lists are unguarded."""
        if not isinstance(expr, ast.Node):
            return
        if isinstance(expr, (ast.AssumeExpr, ast.TypeExpr, ast.Pattern)):
            return
        if (fallback and isinstance(expr, ast.Expr)
                and self.target(expr) is not None):
            handed, fallback = None, False
        if handed is None:
            via = None
        if isinstance(expr, ast.Expr):
            self._via.append(via)
            try:
                self.expr_rows(expr, handed, nat_handed, in_closure, under_join,
                               store, store and not _is_nat(inplace))
            finally:
                self._via.pop()
        if isinstance(expr, ast.LetStmt):
            let_ty = self.sem(expr.type_expr)
            self.walk(expr.value, d, handed=self.target(expr.value) or let_ty,
                      in_closure=in_closure)
            return
        if isinstance(expr, ast.LetDestruct):
            self.walk(expr.value, d, in_closure=in_closure)
            self.destructure_rows(expr)
            return
        if (isinstance(expr, (ast.MatchExpr, ast.IfExpr, ast.Block, ast.HandleExpr))
                and handed is None):
            handed = self.target(expr)
        # A join hands the requirement, and the store's own component type,
        # to its value leaves; the `Nat` requirement only where a position
        # of its differing tree lies below the join.
        joined = handed is not None
        nat_join: Type | None = None
        if isinstance(expr, ast.Expr):
            nat_req = nat_handed if nat_handed is not None else self.target(expr)
            if nat_req is not None and not self._coerces_nothing(expr, nat_req):
                nat_join = nat_req
        if isinstance(expr, ast.MatchExpr):
            self.walk(expr.scrutinee, d, in_closure=in_closure)
            for arm in expr.arms:
                self.pattern_rows(expr.scrutinee, arm.pattern)
                self.walk(arm.body, d, handed=handed, in_closure=in_closure,
                          under_join=joined, store=store, inplace=inplace,
                          fallback=fallback, nat_handed=nat_join, via=via)
            return
        if isinstance(expr, ast.IfExpr):
            self.walk(expr.condition, d, in_closure=in_closure)
            self.walk(expr.then_branch, d, handed=handed, in_closure=in_closure,
                      under_join=joined, store=store, inplace=inplace,
                      fallback=fallback, nat_handed=nat_join, via=via)
            if expr.else_branch is not None:
                self.walk(expr.else_branch, d, handed=handed,
                          in_closure=in_closure, under_join=joined,
                          store=store, inplace=inplace, fallback=fallback,
                          nat_handed=nat_join, via=via)
            return
        if isinstance(expr, ast.Block):
            for s in expr.statements:
                self.walk(s, d, in_closure=in_closure)
            if expr.expr is not None:
                self.walk(expr.expr, d, handed=handed, in_closure=in_closure,
                          under_join=joined, store=store, inplace=inplace,
                          fallback=fallback, nat_handed=nat_join, via=via)
            return
        if isinstance(expr, ast.HandleExpr):
            # A `handle` yields its body's value, or a non-resuming clause's
            # (`narrowing.handle_value_exprs`), the fourth join: the
            # requirement is handed there as through the other three, and
            # the rows it alone lists are unguarded, since code generation
            # hands no requirement into a handle (the follow-up closes it).
            self.handle_rows(expr, d, in_closure,
                             handed=handed if joined else None,
                             under_join=joined, store=store, inplace=inplace,
                             fallback=fallback)
            return
        if isinstance(expr, ast.AnonFn):
            # A closure is lifted and compiled once, as a function of its
            # own whose body is evaluated as a body is, wherever it is
            # written: inside a measure or a predicate lowered at several
            # sites, its rows are listed once, in the body's evaluation.
            # A quantifier's predicate is the exception: its body is
            # lowered inline, in the quantifier's own evaluation.
            inline = id(expr) in self._inline_closures
            key = ObligationTable._key(expr)
            if not inline:
                if key in self._closures_listed:
                    return
                self._closures_listed.add(key)
            self._evaluation.append(self._evaluation[-1] if inline else BODY)
            try:
                rty = self.sem(expr.return_type)
                for p in expr.params:
                    self._entry_rows(p, self.sem(p))
                self._boundary_rows(expr.body, expr.return_type)
                self.walk(expr.body, d, handed=rty, in_closure=True,
                          under_join=True)
                self._return_rows(expr.return_type, rty, expr.body)
            finally:
                self._evaluation.pop()
            return
        if isinstance(expr, (ast.ForallExpr, ast.ExistsExpr)):
            self._quantifier_layer_rows(expr)
            self._inline_closures.add(id(expr.predicate))
        req_here = handed
        from_own_type = fallback
        if req_here is None and isinstance(expr, ast.Expr):
            req_here = self.target(expr)
            if req_here is None:
                # A construction with no recorded target hands its children
                # its own declared component types; a child's own recorded
                # target overrides that (`fallback`).
                req_here = self.sem(expr)
                from_own_type = True
        comps = (self._construction_components(expr, req_here)
                 if req_here is not None and isinstance(expr, ast.Expr) else None)
        # The `Nat` requirement is handed down along its differing tree
        # alone (code generation's descent): a child below no position of
        # it reads its own recorded target.
        nat_comps: dict[int, Type] | None = None
        if isinstance(expr, ast.Expr):
            nat_req = nat_handed if nat_handed is not None else self.target(expr)
            if nat_req is not None and not self._coerces_nothing(expr, nat_req):
                nat_comps = self._construction_components(expr, nat_req)
        # The component types the construction's own store reads (#1606's
        # hand-down): its recorded target, else what a `Tuple` argument, an
        # array-literal element or a `map_insert` value handed a `Tuple`, a
        # literal or a `map_insert` through the joins; a user constructor
        # reads its own target or declaration alone.
        in_comps: dict[int, Type] | None = None
        if comps is not None and isinstance(expr, ast.Expr):
            own = self.target(expr)
            if own is None:
                if _reads_hand_down(expr):
                    own = inplace
                elif not isinstance(expr, ast.ArrayLit):
                    own = self.sem(expr)
            in_comps = (self._construction_components(expr, own)
                        if own is not None else None)
        for child in fold.children(expr):
            h = comps.get(id(child)) if comps is not None else None
            child_via = via if h is not None and handed is not None else None
            if h is None:
                h = self._handed_override.get(id(child))
            child_store = (comps is not None and h is not None
                           and not (isinstance(expr, ast.FnCall)
                                    and child is expr.args[0]))
            self.walk(
                child, d, handed=h, in_contract=in_contract,
                in_closure=in_closure, under_join=False, store=child_store,
                inplace=(in_comps.get(id(child)) if in_comps is not None
                         and child_store else None),
                fallback=from_own_type and h is not None
                and id(child) not in self._handed_override,
                nat_handed=(nat_comps.get(id(child)) if nat_comps is not None
                            else self._handed_override.get(id(child))),
                via=child_via)

    def _coerces_nothing(self, expr: ast.Expr, req: Type) -> bool:
        """Whether holding *expr* to *req* coerces no component below it: the
        requirement is its own type, or no position of the differing tree
        lies below the node (a refinement holds no position)."""
        sem = self.sem(expr)
        if sem is None or req == sem:
            return True
        required = _strip(req)
        if required is None:  # pragma: no cover — a type strips to a type
            return True
        tree = narrowing.differing_tree(base_type(sem), required,
                                        self.ftypes, self.ctors)
        return tree is None or tree.kind == "nat"

    def _construction_components(
        self, expr: ast.Expr, req: Type,
    ) -> dict[int, Type] | None:
        """The component of *req* each child of a construction is stored
        at; ``None`` for a node that is no construction."""
        b = _strip(req)
        out: dict[int, Type] = {}
        if isinstance(expr, ast.ConstructorCall):
            fs = self.ftypes(expr.name, b)
            if fs is None:
                return None
            for arg, f in zip(expr.args, fs):
                out[id(arg)] = f
            return out
        if isinstance(expr, ast.ArrayLit):
            if isinstance(b, AdtType) and b.name == "Array" and b.type_args:
                for e in expr.elements:
                    out[id(e)] = b.type_args[0]
                return out
            return None
        if isinstance(expr, ast.FnCall) and expr.name == "map_insert" and len(expr.args) == 3:
            if isinstance(b, AdtType) and b.name == "Map" and len(b.type_args) == 2:
                out[id(expr.args[0])] = req
                out[id(expr.args[1])] = b.type_args[0]
                out[id(expr.args[2])] = b.type_args[1]
                return out
        if isinstance(expr, ast.FnCall) and expr.name == "set_add" and len(expr.args) == 2:
            if isinstance(b, AdtType) and b.name == "Set" and b.type_args:
                out[id(expr.args[0])] = req
                out[id(expr.args[1])] = b.type_args[0]
                return out
        return None

    # -- rows at one expression -----------------------------------------

    def expr_rows(
        self, e: ast.Expr, handed: Type | None, nat_handed: Type | None,
        in_closure: bool, under_join: bool, store: bool,
        handed_only: bool = False,
    ) -> None:
        if isinstance(e, ast.BinaryExpr):
            self._binary_rows(e)
        elif isinstance(e, ast.IndexExpr):
            self.add("index_bounds", e)
        elif isinstance(e, ast.AssertExpr):
            self.add("assert", e)
        elif isinstance(e, ast.InterpolatedString):
            for part in e.parts:
                if isinstance(part, ast.Expr):
                    ty = self.sem(part)
                    if ty is not None and (_strip(ty) == FLOAT64 or self._holds_float(ty)):
                        self.add("float_to_int_domain", part)
        elif isinstance(e, (ast.FnCall, ast.ModuleCall)):
            self.call_rows(e)
        elif (isinstance(e, ast.QualifiedCall) and e.qualifier == "State"
                and e.name in ("get", "put")):
            self._register_op_call(e)
        # narrowings: the requirement is the handed component, else the
        # target; the `Nat` requirement its own channel's, else the target,
        # else the handed component
        req = handed if handed is not None else self.target(e)
        req_nat = nat_handed
        if req_nat is None:
            req_nat = self.target(e)
            if req_nat is None:
                req_nat = req
        sem = self.sem(e)
        # Once per evaluation: a measure re-evaluated at each tail call and
        # a predicate lowered by each guard hold the node's rows again.
        key = (ObligationTable._key(e), self._evaluation[-1])
        if req is None or sem is None or key in self.done:
            return
        self.done.add(key)
        if sem == NEVER:
            # A `throw` (or a join of them) yields no value: nothing to
            # prove a fact of, nothing to guard.
            return
        if narrowing.flow_arms(e) is not None:
            # The head row stands at the join when some leaf differs; the
            # component rows stand at the leaves (the walk hands req down).
            if under_join:
                return
            leaves = [leaf for leaf in narrowing.value_leaves(e)
                      if self.sem(leaf) != NEVER]
            if isinstance(req, RefinedType):
                if any(not _same_refinement(self.sem(leaf), req)
                       and self._construction_components(leaf, req) is None
                       and not narrowing.holds_no_component(leaf)
                       for leaf in leaves):
                    self.add("refine_bind", e, target=req,
                             guard=self._refinement_guardable(req),
                             answer=self._boundary.get(id(e)))
            # A refinement over `Nat` takes the sign row beside its
            # predicate's, as a bare `Nat` does.
            # The sign is checked where the value narrows, a refined
            # formal's entry checking its predicate alone.
            if (_is_nat(req_nat) and self.narrows_nat_join(e)
                    and not (isinstance(req, RefinedType)
                             and id(e) in self._predicate_only)):
                # A join passed where no check is planted (`string_slice`
                # clamps, #475) is unguarded as a single value there is.
                reason = self._arg_reason.get(id(e))
                self.add("nat_bind", e, target=NAT, handed=handed_only,
                         guard=CHECK if reason is None else unguarded(reason))
            return
        if self._construction_components(e, req) is not None:
            # a construction: its components carry the requirement; the
            # head may still be refined over the construction's type
            if isinstance(req, RefinedType) and not _same_refinement(sem, req):
                self.add("refine_bind", e, target=req,
                         guard=self._refinement_guardable(req, construction=store),
                         answer=self._boundary.get(id(e)))
            return
        if narrowing.holds_no_component(e):
            return
        assert req_nat is not None  # noqa: S101 — `req` stands in above
        self.narrowing_rows(e, sem, req, req_nat, head=not under_join,
                            store=store, handed_only=handed_only)

    def _binary_rows(self, e: ast.BinaryExpr) -> None:
        lt, rt = self.sem(e.left), self.sem(e.right)
        if e.op in (ast.BinOp.DIV, ast.BinOp.MOD):
            if (rt is not None and _strip(rt) == FLOAT64) or (
                    lt is not None and _strip(lt) == FLOAT64):
                return
            self.add("div_zero", e)
            if e.op == ast.BinOp.DIV and self._quotient_can_overflow(e, lt, rt):
                self.add("int_overflow", e)
        elif e.op in (ast.BinOp.ADD, ast.BinOp.SUB, ast.BinOp.MUL):
            if e.op == ast.BinOp.SUB and narrowing.is_guarded_nat_subtraction(
                    e, self.is_nat_expr):
                self.add("nat_sub", e)
                return
            kinds: list[str | None] = []
            for s in (lt, rt):
                if s is None:
                    kinds.append("Int")
                elif _is_nat(s):
                    kinds.append("Nat")
                elif _is_int(s):
                    kinds.append("Int")
                else:
                    kinds.append(None)
            if None not in kinds and not (
                    e.op == ast.BinOp.SUB and kinds == ["Nat", "Nat"]):
                self.add("int_overflow", e)

    def _quotient_can_overflow(
        self, e: ast.BinaryExpr, lt: Type | None, rt: Type | None,
    ) -> bool:
        if _is_nat(lt) or _is_nat(rt):
            return False
        if isinstance(e.right, ast.IntLit):
            return False
        if (isinstance(e.right, ast.UnaryExpr) and e.right.op == ast.UnaryOp.NEG
                and isinstance(e.right.operand, ast.IntLit)
                and e.right.operand.value != 1):
            return False
        return True

    def _boundary_formal(self, pty: Type | None) -> bool:
        """Whether a formal of type *pty* has entry rows an argument's rows
        are answered by: a refinement at its head or inside it, or a
        `Tuple` (whose `Nat` components the entry decomposes)."""
        if isinstance(pty, RefinedType) or self._contains_refinement(pty):
            return True
        base = _strip(pty)
        return isinstance(base, AdtType) and base.name == "Tuple"

    def _register_op_call(self, e: ast.Expr) -> None:
        """A `get` or `put` written in a `State` handler's body is the
        innermost such handler's operation, and the site its clause for
        the operation is inlined at."""
        if self._handler_stack:
            self._handled.setdefault(id(self._handler_stack[-1]), []).append(
                (e, self._evaluation[-1]))

    def call_rows(self, e: ast.FnCall | ast.ModuleCall) -> None:
        name = e.name
        is_builtin = name not in self.fn_decls
        if isinstance(e, ast.FnCall) and is_builtin and name in ("get", "put"):
            self._register_op_call(e)
        if isinstance(e, ast.FnCall) and is_builtin and name == "throw":
            for arg in e.args:
                self._predicate_only.add(id(arg))
                for leaf in narrowing.value_leaves(arg):
                    self._predicate_only.add(id(leaf))
        if isinstance(e, ast.FnCall) and is_builtin and len(e.args) == 1:
            if name in FLOAT_CONVERSIONS:
                self.add("float_to_int_domain", e)
            elif name == "show":
                ty = self.sem(e.args[0])
                if ty is not None and (_strip(ty) == FLOAT64 or self._holds_float(ty)):
                    self.add("float_to_int_domain", e)
            elif name == "abs":
                self.add("int_overflow", e)
        decl = self.fn_decls.get(name)
        callee: ast.FnDecl | None = decl
        inst = self.typed.call_target(e)
        if inst is not None and inst.clone is not None:
            callee = inst.clone
        if callee is not None:
            # a refined formal's check is the callee's entry guard
            for arg, p in zip(e.args, callee.params):
                if self._boundary_formal(self.sem(p)):
                    self._boundary.setdefault(id(arg), p)
                    for leaf in narrowing.value_leaves(arg):
                        self._boundary.setdefault(id(leaf), p)
            for c in callee.contracts:
                if isinstance(c, ast.Requires) and not self._trivial(c):
                    self.add("call_pre", e, answer=c)
            return
        if isinstance(e, ast.FnCall) and name == "apply_fn" and e.args:
            closure = e.args[0]
            if isinstance(closure, ast.AnonFn):
                for arg, p in zip(e.args[1:], closure.params):
                    if self._boundary_formal(self.sem(p)):
                        self._boundary.setdefault(id(arg), p)
                        for leaf in narrowing.value_leaves(arg):
                            self._boundary.setdefault(id(leaf), p)
            elif isinstance(closure, ast.SlotRef):
                # Every closure of the slot's type guards its own entry.
                for arg in e.args[1:]:
                    self._closure_args.add(id(arg))
                    for leaf in narrowing.value_leaves(arg):
                        self._closure_args.add(id(leaf))
        if isinstance(e, ast.FnCall) and name in NAT_ARG_UNGUARDED_BUILTINS:
            for arg in e.args:
                self._arg_reason.setdefault(id(arg), REASON_STRING_SLICE)
        if isinstance(e, ast.FnCall) and name in BUILTIN_DOMAIN_NAMES:
            self.add("call_pre", e)

    def narrowing_rows(
        self, e: ast.Expr, sem: Type, req: Type, req_nat: Type, head: bool,
        store: bool, handed_only: bool = False,
    ) -> None:
        """The rows of a value held to *req* (its refinement rows) and to
        *req_nat* (its `Nat` rows: the head's sign, the positions of the
        differing tree below it)."""
        boundary = self._boundary.get(id(e))
        closure = id(e) in self._closure_args
        at_entry = ANSWERED_AT_CLOSURE_ENTRY if closure else None
        if head:
            if isinstance(req, RefinedType):
                if not _same_refinement(sem, req):
                    self.add("refine_bind", e, target=req,
                             guard=self._refinement_guardable(req, construction=store),
                             answer=boundary, answer_row=at_entry)
            # A refinement over `Nat` takes the sign row beside its
            # predicate's, as a bare `Nat` does.
            if (_is_nat(req_nat) and self.narrows_nat(e)
                    and not (isinstance(req, RefinedType)
                             and id(e) in self._predicate_only)):
                reason = self._arg_reason.get(id(e))
                # The sign is checked where the value narrows, a refined
                # formal's entry checking its predicate alone.
                self.add("nat_bind", e, target=NAT,
                         guard=CHECK if reason is None else unguarded(reason),
                         handed=handed_only)
        # components
        required = _strip(req_nat)
        tree = (narrowing.differing_tree(base_type(sem), required,
                                         self.ftypes, self.ctors)
                if required is not None else None)
        if tree is not None and tree.kind != "nat":
            self._tree_rows(tree, e, boundary=boundary, closure=closure)
        for p, rty in self._refined_paths(_strip(req), _strip(sem), ()):
            tuple_path = all(s.startswith("Tuple.") for s in p)
            guard = (self._refinement_guardable(rty) if tuple_path
                     else unguarded(REASON_INSIDE_PAYLOAD))
            self.add("refine_bind", e, target=rty, path=p, guard=guard,
                     answer=boundary, answer_path=p,
                     answer_row=at_entry if tuple_path else None)

    def _tree_rows(
        self, tree: narrowing.Coercion, node: ast.Node, *,
        boundary: ast.TypeExpr | None = None, source: Source | None = None,
        closure: bool = False,
    ) -> None:
        """The ``Nat`` positions of one differing tree, as rows at *node*:
        the first is the walk's own check and carries the tree the walk
        reads, the rest are answered by it, bar a tuple position a
        boundary's entry row answers (or, for an argument to a closure held
        in a slot, the closure's own entry guard)."""
        walk_row: int | None = None
        covered: set[tuple[int, ...]] = set()
        for p in self._nat_paths(tree, ()):
            tuple_path = all(step.startswith("Tuple.") for step in p)
            if tuple_path and (boundary is not None or closure):
                covered.add(tuple(int(step.split(".")[1]) for step in p))
                self.add("nat_bind", node, target=NAT, path=p, source=source,
                         answer=boundary, answer_path=p,
                         answer_row=ANSWERED_AT_CLOSURE_ENTRY if closure else None)
                continue
            row_id = self.add("nat_bind", node, target=NAT, path=p,
                              source=source, answer_row=walk_row)
            if walk_row is None:
                walk_row = row_id
        if walk_row is not None:
            walked = narrowing.without_paths(tree, frozenset(covered))
            if walked is None:  # pragma: no cover — a walk row has a position
                raise AssertionError("a walk row with no tree")
            self.rows[walk_row] = replace(self.rows[walk_row], tree=walked)

    def _nat_paths(
        self, tree: narrowing.Coercion, prefix: tuple[str, ...],
    ) -> Iterator[tuple[str, ...]]:
        if tree.kind == "nat":
            yield prefix
            return
        if tree.kind == "again":
            return
        for ctor, i, child in tree.parts:
            if ctor in ("key", "value"):
                step = f"{tree.kind} {ctor}"
            elif ctor == "":
                step = f"{tree.kind} element"
            else:
                step = f"{ctor}.{i}"
            yield from self._nat_paths(child, prefix + (step,))

    def _refined_paths(
        self, req: Type | None, sem: Type | None, prefix: tuple[str, ...],
        seen: frozenset[str] = frozenset(),
    ) -> Iterator[tuple[tuple[str, ...], RefinedType]]:
        """Positions below the head where *req* holds a refinement *sem*
        does not."""
        if not isinstance(req, AdtType):
            return
        key = repr(req)
        if key in seen:
            return
        deeper = seen | {key}
        sb = _strip(sem) if sem is not None else None
        if req.name == "Tuple":
            for i, comp in enumerate(req.type_args):
                scomp = (sb.type_args[i]
                         if isinstance(sb, AdtType) and len(sb.type_args) > i
                         else None)
                step = (f"Tuple.{i}",)
                if isinstance(comp, RefinedType) and not _same_refinement(scomp, comp):
                    yield prefix + step, comp
                yield from self._refined_paths(_strip(comp), scomp, prefix + step, deeper)
            return
        if req.name in carriers.CARRIER_POSITIONS:
            for carrier in carriers.element_carriers(req):
                scar = {c.kind: c for c in carriers.element_carriers(sb)}.get(carrier.kind)
                sel = scar.element_type if scar else None
                step = (carrier.kind,)
                if (isinstance(carrier.element_type, RefinedType)
                        and not _same_refinement(sel, carrier.element_type)):
                    yield prefix + step, carrier.element_type
                yield from self._refined_paths(
                    _strip(carrier.element_type), sel, prefix + step, deeper)
            return
        for ctor in self.ctors(req.name):
            fr = self.ftypes(ctor, req)
            fs = self.ftypes(ctor, sb) if isinstance(sb, AdtType) else None
            if fr is None:
                continue
            for i, f in enumerate(fr):
                sf = fs[i] if fs is not None and i < len(fs) else None
                step = (f"{ctor}.{i}",)
                if isinstance(f, RefinedType) and not _same_refinement(sf, f):
                    yield prefix + step, f
                yield from self._refined_paths(_strip(f), sf, prefix + step, deeper)

    # -- binders --------------------------------------------------------

    def pattern_rows(self, scrutinee: ast.Expr, pattern: ast.Pattern) -> None:
        if isinstance(pattern, ast.BindingPattern):
            declared = self.sem(pattern.type_expr)
            matched = self.sem(pattern)
            if declared is None or matched is None:
                return
            source = Source(scrutinee)
            if isinstance(declared, RefinedType):
                # A refined bind is guarded ungated, as code generation
                # always has (#765): the field's refinement is no fact
                # unless its producer was checked, which a payload's
                # entry is not.
                self.add("refine_bind", pattern, target=declared,
                         guard=self._refinement_guardable(declared),
                         source=source)
            elif _is_nat(declared) and self.narrows_nat(scrutinee):
                self.add("nat_bind", pattern, target=NAT, source=source)
            for tree in narrowing.value_coercion(
                    scrutinee, declared, self.effective, self.ftypes,
                    self.ctors, self.narrows_nat):
                self._tree_rows(tree, pattern, source=source)
            self._effect_row_rows(pattern, declared, matched, source)
            return
        if not isinstance(pattern, ast.ConstructorPattern):
            return
        steps = {id(sub): here for sub, here in _pattern_steps(pattern)}
        for te, sources, i, ctor_name in narrowing.pattern_binding_sources(
                scrutinee, pattern, self.typed.field_is_generic):
            sub = self._binder_of(pattern, te)
            if sub is None:
                continue
            declared = self.sem(te)
            matched = self.sem(sub)
            if declared is None:
                continue
            source = Source(scrutinee, steps.get(id(sub), ()))
            if isinstance(declared, RefinedType):
                # A refined bind is guarded ungated, as code generation
                # always has (#765): the field's refinement is no fact
                # unless its producer was checked, which a payload's
                # entry is not.
                self.add("refine_bind", sub, target=declared,
                         guard=self._refinement_guardable(declared),
                         source=source)
            elif _is_nat(declared):
                def leaf_is_nat(leaf: narrowing.ComponentSource, idx: int,
                                _c: str = ctor_name) -> bool | None:
                    return narrowing.declared_component_is_nat(
                        leaf, idx, _c, self.sem, self.ftypes, _is_nat)
                if narrowing.component_narrows(sources, i, self.narrows_nat, leaf_is_nat):
                    self.add("nat_bind", sub, target=NAT, source=source)
            for tree in narrowing.component_coercion(
                    sources, i, ctor_name, declared, self.effective, self.sem,
                    self.ftypes, self.ctors, self.narrows_nat):
                self._tree_rows(tree, sub, source=source)
            self._effect_row_rows(sub, declared, matched, source)

    def _effect_row_rows(
        self, binder: ast.Node, declared: Type | None, matched: Type | None,
        source: Source,
    ) -> None:
        """#1725: a binder bound at a function type whose effect row is
        narrower than the matched value's: a row no check can evaluate."""
        d, m = _strip(declared), _strip(matched)
        if isinstance(d, FunctionType) and isinstance(m, FunctionType):
            de = _effect_set(d.effect)
            me = _effect_set(m.effect)
            if de is not None and me is not None and de < me:
                self.add("effect_bind", binder, target=declared,
                         guard=unguarded(REASON_EFFECT_ROW), source=source)

    @staticmethod
    def _binder_of(
        pattern: ast.ConstructorPattern, te: ast.TypeExpr,
    ) -> ast.BindingPattern | None:
        for n in _pattern_nodes(pattern):
            if isinstance(n, ast.BindingPattern) and n.type_expr is te:
                return n
        return None

    def destructure_rows(self, stmt: ast.LetDestruct) -> None:
        src_ty = _strip(self.sem(stmt.value))
        ctor_name = self._destructure_ctor(stmt, src_ty)
        tuple_shape = stmt.constructor == "Tuple"

        def ctor_matches(n: str) -> bool:
            if ctor_name is None:
                return (n == "Tuple") == tuple_shape
            return n == ctor_name or ((n == "Tuple") == tuple_shape)

        for i, te in enumerate(stmt.type_bindings):
            declared = self.sem(te)
            if declared is None:
                continue
            sources = narrowing.component_sources(
                stmt.value, i, ctor_matches, self.typed.field_is_generic)
            source = Source(stmt.value, ((ctor_name or stmt.constructor, i),))
            if isinstance(declared, RefinedType):
                # A refined bind is guarded ungated, as code generation
                # always has (#765): the field's refinement is no fact
                # unless its producer was checked, which a payload's
                # entry is not.
                self.add("refine_bind", te, target=declared,
                         guard=self._refinement_guardable(declared),
                         source=source)
            elif _is_nat(declared) and ctor_name is not None:
                def leaf_is_nat(leaf: narrowing.ComponentSource, idx: int,
                                _c: str = ctor_name) -> bool | None:
                    return narrowing.declared_component_is_nat(
                        leaf, idx, _c, self.sem, self.ftypes, _is_nat)
                if narrowing.component_narrows(sources, i, self.narrows_nat, leaf_is_nat):
                    self.add("nat_bind", te, target=NAT, source=source)
            if ctor_name is not None:
                for tree in narrowing.component_coercion(
                        sources, i, ctor_name, declared, self.effective,
                        self.sem, self.ftypes, self.ctors, self.narrows_nat):
                    self._tree_rows(tree, te, source=source)

    def _destructure_ctor(self, stmt: ast.LetDestruct, src_ty: Type | None) -> str | None:
        if stmt.constructor == "Tuple":
            return "Tuple"
        if isinstance(src_ty, AdtType):
            names = self.ctors(src_ty.name)
            if names:
                if stmt.constructor in names:
                    return stmt.constructor
                if len(names) == 1:
                    return names[0]
                return None
        return stmt.constructor

    def handle_rows(self, expr: ast.HandleExpr, d: ast.FnDecl | None,
                    in_closure: bool, *, handed: Type | None = None,
                    under_join: bool = False, store: bool = False,
                    inplace: Type | None = None, fallback: bool = False,
                    ) -> None:
        eff = expr.effect
        cell: Type | None = None
        if isinstance(eff, ast.EffectRef) and eff.type_args:
            cell = self.sem(eff.type_args[0])
        is_state = isinstance(eff, ast.EffectRef) and eff.name == "State"
        if expr.state is not None:
            self.walk(expr.state.init_expr, d,
                      handed=(cell or self.target(expr.state.init_expr)
                              or self.sem(expr.state.type_expr)),
                      in_closure=in_closure)
        if is_state:
            self._handler_stack.append(expr)
        via = REASON_HANDLE_VALUE if handed is not None else None
        value: dict[str, Any] = dict(
            handed=handed, under_join=under_join, store=store,
            inplace=inplace, fallback=fallback, via=via)
        try:
            self.walk(expr.body, d, in_closure=in_closure, **value)
        finally:
            if is_state:
                self._handler_stack.pop()
        handled = self._handled.pop(id(expr), []) if is_state else []
        for clause in expr.clauses:
            if not is_state:
                # An `Exn` clause compiles once, where the handler stands.
                # One that resumes nowhere yields the handle's value, and is
                # handed its requirement as the body is.
                yields = handed is not None and not any(
                    narrowing.is_resume(n) for n in fold.walk(clause.body)
                    if isinstance(n, ast.Expr))
                self._clause_rows(clause, cell, eff, d, in_closure,
                                  value=value if yields else None)
                continue
            # A `State` clause is inlined at each operation call of its
            # handler's body (`vera.wasm.calls_handlers`): its rows are
            # listed once per site, under that site's evaluation (a chain,
            # since a clause body inlined inside another's copy is a copy
            # per copy of the outer one).  A clause no call inlines runs
            # nowhere: its rows are listed once and no check evaluates them.
            sites = [(call, ev) for call, ev in handled
                     if getattr(call, "name", None) == clause.op_name]
            if not sites:
                self._evaluation.append(("clause",))
                self._unevaluated.append(REASON_CLAUSE_NOT_INLINED)
                try:
                    self._clause_rows(clause, cell, eff, d, in_closure)
                finally:
                    self._unevaluated.pop()
                    self._evaluation.pop()
                continue
            for call, ev in sites:
                chain = ev[1:] if ev and ev[0] == "clause" else ()
                self._evaluation.append(("clause", *chain, call.node_id))
                try:
                    self._clause_rows(clause, cell, eff, d, in_closure)
                finally:
                    self._evaluation.pop()

    def _clause_rows(
        self, clause: ast.HandlerClause, cell: Type | None,
        eff: ast.EffectRefNode, d: ast.FnDecl | None, in_closure: bool,
        value: dict[str, Any] | None = None,
    ) -> None:
        """One copy of a handler clause: its binder's rows, its body's, and
        its `with` update's; *value* is the handle's requirement where the
        clause's body is the handle's value."""
        if (clause.params and isinstance(eff, ast.EffectRef) and eff.type_args
                and (eff.name, clause.op_name) in (("Exn", "throw"), ("State", "put"))):
            self._clause_binder_rows(clause, cell)
        if (clause.op_name == "get" and isinstance(eff, ast.EffectRef)
                and eff.name == "State" and cell is not None):
            # The tail `resume(x)` of a `get` clause writes `x` back into
            # the cell: `x` is held to the cell's type.
            r = tail_resume_arg(clause.body)
            if r is not None:
                self._handed_override.setdefault(id(r), cell)
        self.walk(clause.body, d, in_closure=in_closure,
                  **(value or {}))
        if clause.state_update is not None:
            self.walk(clause.state_update[1], d,
                      handed=cell or self.sem(clause.state_update[0]),
                      in_closure=in_closure)

    def _clause_binder_rows(self, clause: ast.HandlerClause, payload: Type | None) -> None:
        te = clause.params[0]
        binder = self.sem(te)
        if payload is None or binder is None:
            return
        if isinstance(binder, RefinedType):
            if narrowing.narrows_into_refinement(self.chain(payload), self.chain(binder)):
                self.add("refine_bind", te, target=binder,
                         guard=self._refinement_guardable(binder))
        elif _is_nat(binder) and not _is_nat(payload):
            self.add("nat_bind", te, target=NAT)
        declared = _strip(binder)
        tree = (narrowing.differing_tree(base_type(payload), declared,
                                         self.ftypes, self.ctors)
                if declared is not None else None)
        if tree is not None and tree.kind != "nat":
            self._tree_rows(tree, te)
        for p, rty in self._refined_paths(_strip(binder), _strip(payload), ()):
            self.add("refine_bind", te, target=rty, path=p,
                     guard=unguarded(REASON_INSIDE_PAYLOAD))
