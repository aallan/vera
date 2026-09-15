"""The one enumeration of the positions Vera's grammar binds a slot in.

Vera has no variable names, so every value a body can refer to arrives through
a *binder position*: a place the grammar declares a slot at a type.  There are
a dozen of them — a function's parameters and its return, a closure's, a `let`,
a destructuring `let`, a match arm's pattern and its sub-patterns, a handler
clause's payload binder and its state writes, a constructor's fields, an effect
operation's formals, a quantifier's variable.  Two components have to answer a
question about each: the verifier asks "is there a narrowing to obligate here?"
and code generation asks "do I plant a guard here?", and #1412 made their answer
to the second one shared (:data:`GUARD_SITES` below, read through
``vera.narrowing``) so a status cannot promise a check the backend does not
emit.

What was never shared is the LIST.  Each position was added to the guard table
and to the two emitters as review DISCOVERED it, so the set of positions existed
only as the union of what several walks happened to visit — and a position no
walk visited was silent rather than wrong, which is the failure mode nothing
notices.  Seven of the ten issues before this module was written were that:
a construction component (#1426), a `State` write (#1439), the sign direction at
two stores (#1440), a handler clause binder over `Exn` (#1445) and over a
refinement (#1448), a `where` helper's parameter at the call boundary (#1455).

So the list lives here, keyed by AST node class, and
``test_binder_positions.py`` holds it to the AST: every field of every node
class that carries a ``TypeExpr`` or a ``Pattern`` is either a registered binder
position or an entry in :data:`NON_BINDER_FIELDS` with the reason it binds
nothing.  A node class added later with a binder field fails that test rather
than being quietly unvisited.

The module deliberately holds no analysis.  It says WHICH positions exist, what
each is called in a diagnostic, and which guard key each asks the table with;
whether a particular value narrows, and whether a particular refinement's base
can be lowered, stay with the components that can answer them.
"""

from __future__ import annotations

from collections.abc import Iterator
from dataclasses import dataclass

from vera import ast

# =====================================================================
# Guard sites: what code generation plants, per key
# =====================================================================


@dataclass(frozen=True)
class SiteGuards:
    """Which runtime guards code generation emits at one guard key.

    A guard key is what the two components ASK the table with, which is not
    always the diagnostic site name: the three `State` writes each keep their
    own name in the message — "handler state init" tells a reader which of the
    three to go and look at — while asking one key, because what must not
    differ between them is the answer about codegen (#1439).
    """

    #: The §2.6.5 refinement predicate is lowered here (#765, #1426).
    refinement_predicate: bool = False
    #: The `@Nat >= 0` sign check is planted at this CONSTRUCTION position
    #: (#747/#757 for the constructor field, #1416 for the tuple component,
    #: #1440 for the array element and the `Map` value).  Boundary and
    #: pattern-bind sites take their sign guard from the boundary/bind
    #: emitters instead and are not construction positions, so they are False
    #: here and the verifier never asks them this question.
    nat_sign_at_construction: bool = False
    #: The `@Nat` -> `@Int` widening check at the same construction position
    #: (#820's enabler threads a target type to these two shapes only).
    int_widen_at_construction: bool = False
    #: Why the answers above are what they are — measured, not remembered.
    note: str = ""


#: THE table both components read, keyed by guard key.
#:
#: Membership is necessary and not sufficient: the TYPE half — whether a guard
#: can be emitted for this particular refinement's BASE — is
#: ``ContractVerifier._refined_boundary_codegen_guardable`` and
#: ``_emit_bind_refine_guard``'s own bail, intersected wherever a type is in
#: hand (``vera.narrowing.REFINED_CONSTRUCTION_SCALAR_BASES`` is the
#: construction-position half of that).
#:
#: A key absent from this table is a position whose guard answer is not a
#: property of the position: an effect operation's argument is guarded for a
#: built-in effect and not for a user-declared one, so the verifier computes it
#: from the operation's parent effect and there is nothing here to read.
GUARD_SITES: dict[str, SiteGuards] = {
    "return type": SiteGuards(
        refinement_predicate=True,
        note="the function boundary guards its return predicate (#746), "
             "and the `@Nat` return position since #758",
    ),
    "call argument": SiteGuards(
        refinement_predicate=True,
        note="the callee's boundary guards each parameter; a generic formal "
             "is guarded on the monomorphised callee (#746, CR #756)",
    ),
    "closure argument": SiteGuards(
        refinement_predicate=True,
        note="`_compile_lifted_closure` guards the lifted body's parameters",
    ),
    "closure return": SiteGuards(
        refinement_predicate=True,
        note="the same lifted body guards its per-narrowing-leaf return "
             "(#984, #1032)",
    ),
    "let binding": SiteGuards(
        refinement_predicate=True,
        note="`_emit_bind_refine_guard` at the narrowing bind (#765)",
    ),
    "match binding": SiteGuards(
        refinement_predicate=True,
        note="as `let binding` — the arm's top-level pattern binder (#765)",
    ),
    "tuple destructure": SiteGuards(
        refinement_predicate=True,
        note="as `let binding`, once per component the destructure names "
             "(#765)",
    ),
    "ADT sub-pattern bind": SiteGuards(
        refinement_predicate=True,
        note="as `let binding`, at the projected field (#765)",
    ),
    "constructor field": SiteGuards(
        refinement_predicate=True,
        nat_sign_at_construction=True,
        note="the store is guarded in both directions: the sign since "
             "#747/#757, the predicate since #1426",
    ),
    "tuple component": SiteGuards(
        refinement_predicate=True,
        nat_sign_at_construction=True,
        int_widen_at_construction=True,
        note="the built-in `Tuple` carrier reads its target from the "
             "threaded table (#1416); predicate since #1426",
    ),
    "array element": SiteGuards(
        refinement_predicate=True,
        nat_sign_at_construction=True,
        int_widen_at_construction=True,
        note="predicate since #1426, sign since #1440",
    ),
    "map value": SiteGuards(
        refinement_predicate=True,
        nat_sign_at_construction=True,
        note="predicate since #1426, sign since #1440.  No widening entry: "
             "#820's enabler threads a target type to the array and tuple "
             "shapes only",
    ),
    "State write boundary": SiteGuards(
        refinement_predicate=True,
        note="the ONE key the three `State` writes ask with — the `handle` "
             "init, `put`'s argument and a clause's `with @T = …` override.  "
             "Their sign direction has been guarded since #1203 by the write "
             "emitters rather than by a construction store, so the "
             "construction flags above do not apply; the predicate is the "
             "other half (#1439)",
    ),
    "handler clause binder": SiteGuards(
        refinement_predicate=True,
        note="a clause binder declared narrower than the payload it receives "
             "— `throw(@Nat)` on an `Exn<Int>` handler, `put(@Pos)` on a "
             "`State<Int>` one.  A pattern-bind site like the others, and the "
             "last one with no guard (#1445, #1448)",
    ),
}


# =====================================================================
# Binder positions: where the grammar declares a slot
# =====================================================================


@dataclass(frozen=True)
class BinderField:
    """One field of one AST node class that declares a slot binding."""

    #: The attribute on the node.
    field: str
    #: What the position is called when the instrument enumerates it.
    kind: str
    #: The name a diagnostic uses for this position.  ``None`` means the
    #: position inherits it from whatever declares the pattern it sits in —
    #: a `BindingPattern` is a `match binding` under an arm and an
    #: `ADT sub-pattern bind` under a constructor pattern.
    site: str | None
    #: The key :data:`GUARD_SITES` is asked with, when it differs from
    #: *site*: the three `State` writes share one answer under three names.
    guard_key: str | None = None
    #: The field holds a tuple rather than a single node.
    sequence: bool = False
    #: Why this position exists, and what it binds.
    note: str = ""

    def key(self) -> str | None:
        """The guard key to ask :data:`GUARD_SITES` with."""
        return self.guard_key if self.guard_key is not None else self.site


#: Every AST node class that declares a slot binding, and the field it
#: declares it in.  The completeness test holds this against ``vera.ast``.
BINDER_FIELDS: dict[type[ast.Node], tuple[BinderField, ...]] = {
    ast.FnDecl: (
        BinderField(
            "params", "function parameter", "call argument", sequence=True,
            note="the caller discharges it AT THE CALL, against the formals "
                 "of whatever declaration the name reaches from there — a "
                 "`where` helper's included, which is what #1455 lost",
        ),
        BinderField(
            "return_type", "function return", "return type",
            note="the body's value binds into the declared return (#746)",
        ),
    ),
    ast.AnonFn: (
        BinderField(
            "params", "closure parameter", "closure argument", sequence=True,
            note="`apply_fn`'s arguments bind here (#820)",
        ),
        BinderField(
            "return_type", "closure return", "closure return",
            note="the lifted body's value (#984, #1032)",
        ),
    ),
    ast.LetStmt: (
        BinderField(
            "type_expr", "let", "let binding",
            note="`let @T = e;` binds `e` at `@T` (#765)",
        ),
    ),
    ast.LetDestruct: (
        BinderField(
            "type_bindings", "destructure", "tuple destructure",
            sequence=True,
            note="each component the destructure names is its own bind, "
                 "projected when the source is a literal constructor and "
                 "opaque otherwise (#1426)",
        ),
    ),
    ast.MatchArm: (
        BinderField(
            "pattern", "match arm", "match binding",
            note="the arm's top-level pattern; a `BindingPattern` here is "
                 "the scrutinee bound at the arm's type",
        ),
    ),
    ast.ConstructorPattern: (
        BinderField(
            "sub_patterns", "ADT sub-pattern", "ADT sub-pattern bind",
            sequence=True,
            note="a projected field, whose accessor term carries only the "
                 "field's own declared invariants (#746)",
        ),
    ),
    ast.BindingPattern: (
        BinderField(
            "type_expr", "pattern binder", None,
            note="the declared type OF a binder.  The POSITION is whichever "
                 "pattern field declares it, so the site is inherited rather "
                 "than restated — a `@T` under an arm and the same `@T` under "
                 "a constructor pattern are different positions with "
                 "different guards",
        ),
    ),
    ast.HandlerClause: (
        BinderField(
            "params", "handler clause", "handler clause binder",
            sequence=True,
            note="the payload the operation delivers, bound at the clause's "
                 "own declared type — `throw(@Nat)` over `Exn<Int>` (#1445), "
                 "`throw(@Pos)` over the same (#1448)",
        ),
        BinderField(
            "state_update", "handler state override", "handler state update",
            guard_key="State write boundary",
            note="a clause's `with @T = …` writes the cell (#1203, #1439)",
        ),
    ),
    ast.HandlerState: (
        BinderField(
            "type_expr", "handler state init", "handler state init",
            guard_key="State write boundary",
            note="`handle[State<T>] (@T = e)` writes the cell (#1203, #1439)",
        ),
    ),
    ast.Constructor: (
        BinderField(
            "fields", "constructor field", "constructor field", sequence=True,
            note="a construction store: the DECLARED field type is the slot "
                 "a `Ctor(...)` argument goes into (#1426)",
        ),
    ),
    ast.OpDecl: (
        BinderField(
            "param_types", "effect-operation formal",
            "effect-operation argument", sequence=True,
            note="an op call's arguments bind here.  Absent from GUARD_SITES "
                 "on purpose: a built-in effect's argument is guarded at its "
                 "op-call site and a user-declared one's is not, so the "
                 "answer is a property of the EFFECT (#754, #1268)",
        ),
        BinderField(
            "return_type", "effect-operation result", "State-op resume",
            note="a `get` clause's tail `resume(v)` delivers the cell-typed "
                 "result (#1203).  Not in GUARD_SITES for the same reason as "
                 "the formals",
        ),
    ),
    ast.ForallExpr: (
        BinderField(
            "binding_type", "quantifier binder", None,
            note="`forall(@T, domain, pred)` binds `@T` over the domain.  A "
                 "contract-only position: it is translated to a Z3 bound "
                 "variable and never reaches a run, so there is nothing for "
                 "a runtime guard to check and no GUARD_SITES entry",
        ),
    ),
    ast.ExistsExpr: (
        BinderField(
            "binding_type", "quantifier binder", None,
            note="as `forall` — contract-only",
        ),
    ),
}


#: Fields that carry a ``TypeExpr`` or a ``Pattern`` and bind NO slot, with
#: the reason.  The completeness test requires every such field to be in
#: exactly one of these two tables, so a new one forces a decision rather than
#: defaulting to silence.
#: Keyed by ``type`` rather than ``type[ast.Node]``: three of the entries
#: are the transformer's own sentinels, which are dataclasses but not
#: `Node` subclasses, and the completeness test reflects over every
#: dataclass in `vera.ast` — so a key type that excluded them would put
#: three fields permanently out of reach of the check.
NON_BINDER_FIELDS: dict[type, dict[str, str]] = {
    ast.NamedType: {
        "type_args": "type ARGUMENTS of a type expression; the slot, if any, "
                     "is bound by whatever declares a value at this type",
    },
    ast.FnType: {
        "params": "a function TYPE. Nothing is bound until a value of it "
                  "exists, and `AnonFn` is where one is written",
        "return_type": "as `params`",
    },
    ast.RefinementType: {
        "base_type": "the base a refinement is written over; the binder is "
                     "whichever position declares the refinement",
    },
    ast.SlotRef: {
        "type_args": "a REFERENCE to an already-bound slot, not a binding",
    },
    ast.ResultRef: {
        "type_args": "as `SlotRef` — `@T.result` names the return value",
    },
    ast.TypeAliasDecl: {
        "type_expr": "names a type; binds no value",
    },
    ast.EffectRef: {
        "type_args": "the effect's own type arguments. They SAY what a "
                     "payload or cell type is — `_handler_op_payload_type` "
                     "reads them — but the slot is declared by the handler "
                     "clause's params or the state's type_expr",
    },
    ast.QualifiedEffectRef: {
        "type_args": "as `EffectRef`",
    },
    ast._Signature: {
        "params": "transformer sentinel, folded into `FnDecl` before any "
                  "walk sees a program",
        "return_type": "as `params`",
    },
    ast._TupleDestruct: {
        "type_bindings": "transformer sentinel, folded into `LetDestruct`",
    },
    ast._WithClause: {
        "type_expr": "transformer sentinel, folded into "
                     "`HandlerClause.state_update`",
    },
}


# =====================================================================
# Construction positions: a store into a slot declared elsewhere
# =====================================================================

#: The positions where a value is stored into a slot whose type is declared by
#: a CONTAINER rather than by a binder field of its own (#1426).  Keyed by the
#: node whose evaluation performs the store, so the construction descent reads
#: which sites it is responsible for from here rather than from a list written
#: out beside it.
#:
#: `constructor field` is in :data:`BINDER_FIELDS` as well, under
#: ``ast.Constructor``: the DECLARATION is a binder field and the STORE is a
#: construction position, and both are true of it.
CONSTRUCTION_SITES: dict[type[ast.Node], tuple[str, ...]] = {
    ast.ConstructorCall: ("constructor field", "tuple component"),
    ast.ArrayLit: ("array element",),
    # `map_insert(m, k, v)` — a call rather than a literal, so the descent
    # keys on the builtin's name and the site is read from here.
    ast.FnCall: ("map value",),
}


# =====================================================================
# Derived rosters
# =====================================================================

def site_of(node_class: type[ast.Node], field_name: str) -> str:
    """The diagnostic site name of one registered binder position.

    The accessor for a position whose two halves have been converged onto
    it: today that is the `handler clause binder` alone, read by the
    verifier's obligation and by the emitter's guard, so the string that
    links a status to the guard behind it is written once for that position.
    The other thirteen site names are still string literals at their own
    call sites — around eighty of them across `vera/` — and converging them
    is what this accessor exists to make possible, not something it has
    already done.  Saying otherwise would claim a coupling that is not there
    yet (R-1465 review).

    Raises rather than returning a default — a caller asking about a field
    that is not a binder position, or one whose site its owner supplies, has
    a question this module cannot answer, and a fallback would turn that into
    a guard answer nobody chose.
    """
    for binder in BINDER_FIELDS.get(node_class, ()):
        if binder.field == field_name:
            if binder.site is None:
                raise KeyError(
                    f"{node_class.__name__}.{field_name} inherits its site "
                    f"from the position that declares it"
                )
            return binder.site
    raise KeyError(
        f"{node_class.__name__}.{field_name} is not a registered binder "
        f"position"
    )


def guarded_sites(guard: str) -> frozenset[str]:
    """The guard keys at which code generation plants *guard*.

    The three rosters the verifier and code generation read are derived from
    :data:`GUARD_SITES` through this, so a position added to the table with
    its guard answers reaches every consumer at once — which is the coupling
    the table exists for.  *guard* names a field of :class:`SiteGuards`.
    """
    return frozenset(
        key for key, guards in GUARD_SITES.items()
        if getattr(guards, guard)
    )


# =====================================================================
# The enumerator
# =====================================================================


@dataclass(frozen=True)
class BinderPosition:
    """One occurrence of a binder position in a program."""

    #: The node that declares the binding.
    owner: ast.Node
    #: The registration it came from.
    binder: BinderField
    #: The declared type of the bound slot, when the field holds one
    #: directly.  A pattern field holds a `Pattern`, so the type is on the
    #: `BindingPattern` position yielded beneath it rather than here.
    type_expr: ast.TypeExpr | None
    #: Index within a sequence field, or 0.
    index: int
    #: The diagnostic site, with a pattern binder's inherited from its
    #: owner, and ``None`` for a contract-only occurrence — a site NAME is
    #: as much a claim about a guard as the key is, so a consumer reading
    #: one and not the other must not see `closure argument` for a closure
    #: that never reaches a run (R-1465 review).  The registration's own
    #: ``binder.site`` still says what the position is called in general.
    site: str | None
    #: Whether this occurrence is inside a contract-only construct.
    #:
    #: A quantifier's predicate is an `AnonFn`, and an `AnonFn`'s parameters
    #: are a registered position with a guarded site — so `forall(@T, dom,
    #: fn(@T -> @Bool) …)` yielded `closure argument` for a closure that is
    #: translated to a Z3 bound variable and never lifted, applied or run
    #: (R-1465 review).  The KIND is still reported, because the position is
    #: really there; what it may not do is name a guard key.
    contract_only: bool = False

    def key(self) -> str | None:
        """The guard key for this occurrence, or None when it has none."""
        if self.site is None:
            return None
        return self.binder.guard_key or self.site


def binder_positions(node: object) -> Iterator[BinderPosition]:
    """Every binder position *node* and everything under it declares.

    A structural walk over :data:`BINDER_FIELDS`, in source order.  It answers
    "what does this subtree bind, and at which position" — the question both
    the obligation emission and the guard emission start from; neither decides
    anything here.

    Its consumers today are the tests: the completeness matrix in
    `test_binder_positions.py`, which holds the registry to `vera/ast.py`, and
    the class instrument in `test_binder_position_generator.py`, which
    enumerates the positions to build its cells.  No compiler pass walks it
    yet — each still finds its own positions on its own descent — so this is
    the shape a pass would consume rather than one that has replaced them.

    A pattern field yields its own position and descends, so `Some(@Pos)`
    under a match arm yields the arm's `match binding`, the sub-pattern's
    `ADT sub-pattern bind`, and the `@Pos` binder under it carrying the
    sub-pattern's site.
    """
    yield from _walk(node, inherited=None, contract_only=False)


def _positions_in_field(
    node: ast.Node, binder: BinderField, value: object, site: str | None,
    contract_only: bool,
) -> Iterator[BinderPosition]:
    """The positions *binder*'s field declares on *node*."""
    if binder.field == "state_update":
        # `(TypeExpr, Expr)`: the type half is what the write binds at.
        value = (value[0],) if isinstance(value, tuple) else None
    if value is None:
        return
    items = value if isinstance(value, tuple) else (value,)
    for index, item in enumerate(items):
        if isinstance(item, (ast.TypeExpr, ast.Pattern)):
            yield BinderPosition(
                owner=node, binder=binder,
                type_expr=item if isinstance(item, ast.TypeExpr) else None,
                index=index, site=None if contract_only else site,
                contract_only=contract_only,
            )


def _pattern_valued(child: object) -> bool:
    """Whether *child* is a pattern, or a sequence holding one."""
    if isinstance(child, ast.Pattern):
        return True
    if isinstance(child, tuple):
        return any(isinstance(item, ast.Pattern) for item in child)
    return False


def _walk(
    node: object, inherited: str | None, contract_only: bool,
) -> Iterator[BinderPosition]:
    if isinstance(node, tuple):
        for item in node:
            yield from _walk(item, inherited, contract_only)
        return
    if not isinstance(node, ast.Node):
        return
    # A quantifier's whole subtree is contract-only: its binder, and the
    # `AnonFn` predicate's parameters and return with it.
    contract_only = contract_only or isinstance(
        node, (ast.ForallExpr, ast.ExistsExpr))

    by_field = {b.field: b for b in BINDER_FIELDS.get(type(node), ())}
    for fld in getattr(node, "__dataclass_fields__", {}):
        child = getattr(node, fld, None)
        binder = by_field.get(fld)
        site = inherited
        if binder is not None:
            site = binder.site if binder.site is not None else inherited
            yield from _positions_in_field(
                node, binder, child, site, contract_only)
        # Descend exactly once per field.  The site travels only through a
        # PATTERN, which is the one place a position is declared by one node
        # and spelled by another: a `BindingPattern` under a `MatchArm` is a
        # `match binding` and the same node under a `ConstructorPattern` is
        # an `ADT sub-pattern bind`.  Everything else clears it.  Carrying it
        # further gave a quantifier written inside a parameter's refinement
        # predicate the enclosing position's site, so `key()` answered
        # `call argument` for a contract-only binder that never reaches a run
        # and can have no guard (CodeRabbit on PR #1465).
        yield from _walk(
            child, site if _pattern_valued(child) else None,
            contract_only)
