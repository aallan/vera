"""The one derivation of whether binding a value into a `@Nat` slot needs a
runtime guard (#1205 parity, re-keyed in #1362).

Codegen and the verifier both have to answer "does a guard get planted here?",
and they answered it with two parallel implementations — ``_is_static_nat_typed``
/ ``_is_nat_typed``, and ``_has_underflow_leaf`` written twice.  Two copies of a
rule are two things that can drift, and a drift here is invisible from inside
either component: the verifier reports a status about codegen's behaviour, so if
they disagree the status is simply wrong and nothing local notices.

The RULE lives here once (:func:`nat_narrowing`), and both callers read it over
the checker's types: code generation the typed program's type of each node, the
verifier its semantic table (#1525).  What still differs is a pattern-bound or
destructured component: the verifier traces it to its source
(:func:`component_narrows`), where code generation reads the type its field is
instantiated at, so a component the verifier sees built from a non-negative
value can still be guarded (#1695).  The CLASSIFICATION asks "will codegen plant
a guard?" and must be answered with codegen's reading, or the status describes a
component other than the one it is about.  So the oracle is a parameter and the
rule is not.
"""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass

from vera import ast, binders

#: The effects whose operations code generation can lower at all (#754).
#:
#: A guard is a claim about a RUN, so an operation of an effect codegen
#: refuses cannot be "guarded" in any useful sense: a row naming the effect is
#: refused at check (E340), and there is no run to guard.  The verifier's
#: op-argument classification therefore has to intersect its guard question
#: with this set, or it repeats the #1268 mistake one boundary over —
#: recording a Tier-3 runtime check for a program that never reaches a
#: runtime.
#:
#: Here rather than in the backend because both sides read it: codegen's
#: `_is_compilable` decides membership FROM this set, and the verifier's
#: `_effect_op_formal_guarded` asks about it.  Two copies of the roster is
#: exactly the drift this module exists to prevent.
#:
#: ``Diverge`` is here since #1492.  It is a marker with no operations, so
#: there is nothing to lower: a function that declares it compiles like any
#: other, with no termination guard unless it also declares ``decreases``.
#: It was refused before, which made the spec's only opt-out from the
#: termination rule (§7.7.3) unusable, because E125 then carried the refusal
#: up every caller to ``main``.
COMPILABLE_EFFECTS = frozenset({
    "IO", "State", "Exn", "Http", "Async", "HttpServer",
    "Inference", "DB", "Random", "Diverge",
})

#: The subset of :data:`COMPILABLE_EFFECTS` whose lowering touches linear
#: memory, so a function carrying one needs the memory section emitted.
MEMORY_EFFECTS = frozenset({"IO", "Http", "HttpServer", "Inference", "DB"})



#: The SITE half of "does codegen plant a §2.6.5 refinement guard here?" —
#: THE table, read by the verifier's `refine_bind` legs to classify AND by
#: codegen to decide whether to emit (#765, extended to construction in
#: #1426).
#:
#: It lives in this module for the reason the rest of this module does: the
#: two components answer one question, and a copy each is a drift nobody can
#: see from inside either.  Before #1426 the table was the verifier's alone
#: and codegen emitted at a hard-coded set of sites that happened to match;
#: "happened to match" is not a property anything checks.  Now a site is
#: added HERE once and both halves move together — the classification cannot
#: promise a guard the backend does not plant, and the backend cannot plant
#: one the stream does not count.
#:
#: The TYPE half is `ContractVerifier._refined_boundary_codegen_guardable` /
#: `_emit_bind_refine_guard`'s own bail: whether a guard can be emitted for
#: this particular refinement's BASE (an erased `@Unit`, a base that is
#: itself a refinement).  Site and type are intersected wherever a type is in
#: hand, so membership here is necessary and not sufficient.
#: The refinement BASES a construction-position guard can be lowered for.
#:
#: A construction store tees the value into one scalar local and compares it
#: there, so the base has to have a scalar WASM representation.  A boundary
#: guard over a value that is BOUND has no such limit — it binds the value's
#: whole representation (`vera.wasm.helpers.bind_slot_value_from_field` and
#: its operand-stack twin: one local for a scalar or a handle, two
#: consecutive i32s for a `(ptr, len)` pair), so a `{ @String | … }` is
#: guarded at a parameter, a return, a closure boundary and as a tuple
#: COMPONENT alike.  That is why this is a CONSTRUCTION-position rule and not
#: a property of the refinement.
#:
#: The component was the exception until #1466: the tuple decomposition bound
#: one local for a pair, so the predicate read the pointer and a value that
#: SATISFIES the refinement trapped, on a program proved at Tier 1.  The
#: repair was the binding, not this roster — which stays about construction,
#: where the store's own shape (a tee, a stride write, a host import) is what
#: the limit is about.
#:
#: Read by codegen's `_refined_component_wasm_type` and by the verifier's
#: construction arm, so a base the emitter cannot lower is not classified
#: guarded.  Without the second reader a `{ @String | … }` constructor field
#: recorded `tier3` while the store emitted nothing — measured, 0 guards in
#: the emitted body — which is the false-guarantee class this release exists
#: to remove.
REFINED_CONSTRUCTION_SCALAR_BASES = frozenset({
    "Int", "Nat", "Float64", "Bool", "Byte",
})


#: Since #1455/#1445 the membership is DERIVED from
#: :data:`vera.binders.GUARD_SITES`, where each binder position's guard
#: answers are declared beside the position itself.  Keeping the roster
#: as a literal here made it possible to register a position and forget
#: its guard answer, which is one level up from the drift this module
#: exists to prevent — a position nothing answered for was SILENT.
#: The name stays, because every consumer reads it through this module
#: and a test may monkeypatch it to prove the coupling is load-bearing.
REFINED_BIND_GUARDED_SITES = binders.guarded_sites("refinement_predicate")

#: A declared type's refinement chain, comparable across the two components:
#: the name the chain bottoms out in, and the set of predicates conjoined on
#: the way down, keyed by rendered text.  A type carrying no refinement
#: answers ``(its own name, frozenset())`` — "no predicates" is an answer.
RefinementChain = tuple[str, frozenset[str]]


def narrows_into_refinement(
    source: RefinementChain | None, declared: RefinementChain | None,
) -> bool:
    """Does binding a *source*-typed value at a *declared* type NARROW?

    THE derivation of that question, the way :func:`narrows_into_nat` is the
    derivation of the sign one.  It exists because two components were asking
    it two different ways and disagreeing on every program where both types
    are refined: the verifier asked "is the declared type refined and the
    source's not?", which exempted a refined payload bound at a STRICTER
    refinement, and the emitter compared refinement-preserving family NAMES,
    which does not.  So `handle[Exn<Pos>] { throw(@Neg) -> … }` was guarded
    and recorded nowhere, and `Big = { @Pos | @Pos.0 > 100 }` over an
    `Exn<Pos>` payload was neither — silent and unguarded, which is #1448
    again at the chain spelling (R-1465 review).

    Membership in a chain is the CONJUNCTION over its whole length, so the
    comparison is over conjoined predicate SETS rather than over one level or
    over a name: *declared* narrows *source* when it bottoms out in a
    different base, or when it adds a predicate the source does not already
    carry.  A source carrying MORE than the declared type asks for does not
    narrow — that is a widening, and the value already satisfies what it is
    being bound at.

    Predicate identity is TEXTUAL, so "the same chain under two names" holds
    only while the two spell their predicates the same way.  An alias that
    names the whole type does: `type P2 = Pos;` renders `@Int.0 > 0` either
    way, and `Exn<Pos>` bound at `@P2` narrows nothing.  An alias inside the
    refinement's BASE does not, because the predicate embeds the base's
    spelling — `Big = { @Pos | @Pos.0 > 100 }` and
    `SBig = { @P2 | @P2.0 > 100 }` are the same type and render
    `{'@Int.0 > 0', '@Pos.0 > 100'}` against
    `{'@Int.0 > 0', '@P2.0 > 100'}`, so `Exn<Big>` bound at `@SBig` reads as
    a narrowing and is obligated.  Measured, and in the safe direction: it
    over-obligates rather than under-obligating, the record is
    `tier3_unguarded` rather than a claimed guard, and both oracles agree on
    it, so the two components stay in step (R-1465 review).  Comparing
    normalised predicates instead is #1450's seam, not this one's.

    Its consumers today are the handler-clause binder's two halves.  The
    other pattern-bind positions — `let`, `match`, a destructuring `let` —
    answer the same question through `_narrows_into_refined` /
    `_refined_field_narrows`, which compare ONE level rather than the
    conjoined chain, and a differential over twelve (source, declared) pairs
    puts them at the same answer on every pair but one:
    `test_refinement_chain_convergence.py`.  The exception is a source
    carrying a STRONGER refinement than the slot asks for — `Big`'s
    `> 0 AND > 100` into `Pos`'s `> 0`.  This rule exempts it, because the
    value satisfies what it is bound at; those positions obligate it and
    DISCHARGE it from the source's assumed predicate, which is a free Tier 1
    where a value term exists to discharge against.  At a clause binder no
    term exists — the bound value is whatever reaches the operation, and no
    throw or put site pins it — so the same obligation would be a `tier3`
    that can never become anything else.  The difference is deliberate on
    both sides and measured rather than assumed; converging them is a
    decision about that pair, not a tidy-up.

    The chains are the caller's to produce, because the two components hold
    different things: the verifier has the checker's semantic types
    (:func:`vera.naming.refined_type_chain`), code generation has the
    source's type expressions and the alias table
    (:func:`vera.naming.refined_type_expr_chain`).  A chain the caller cannot
    see at all is ``None``: an unknown DECLARED type narrows nothing, because
    there is no predicate to check, and an unknown SOURCE narrows everything,
    because it establishes nothing.
    """
    if declared is None:
        return False
    if source is None:
        return True
    declared_base, declared_predicates = declared
    source_base, source_predicates = source
    if declared_base != source_base:
        return True
    return not declared_predicates <= source_predicates


#: Answers "what Vera type name does this call return?", or None when unknown.
FnCallTypeOracle = Callable[[ast.Expr], "str | None"]

#: Answers "is this a `@Nat` subtraction, the one the verifier obligates
#: `lhs >= rhs` for and code generation guards?" (:func:`is_guarded_nat_subtraction`
#: over each side's reading of the checker's types).
GuardedSubtractionOracle = Callable[[ast.Expr], bool]


#: Answers "is this slot reference a `@Nat`?".  Code generation reads the
#: slot's declared type; the verifier reads the checker's type of the read,
#: which for a clause binder declared `@Nat` over a thrown `@Int` is the
#: `@Int` the binder narrows (spec §11.2.1).
SlotIsNatOracle = Callable[[ast.SlotRef], bool]


def _declared_nat_slot(slot: ast.SlotRef) -> bool:
    return slot.type_name == "Nat"


def is_static_nat_typed(
    expr: ast.Expr, fncall_ret: FnCallTypeOracle,
    slot_is_nat: SlotIsNatOracle = _declared_nat_slot,
) -> bool:
    """True iff *expr* is statically non-negative under the caller's oracles.

    Returns True for a slot reference *slot_is_nat* calls ``@Nat`` (by
    default its declared type), a non-negative ``IntLit``, arithmetic whose
    operands both are (the subtraction among them is
    :func:`has_underflow_leaf`'s question), an ``IfExpr`` / ``MatchExpr``
    whose every branch is, and a call whose oracle answers ``Nat``.
    Conservative False elsewhere — a ``UnaryExpr`` negation is an ``@Int``.

    A literal is an ``Int`` to the checker (spec §4.2) and a ``Nat`` here:
    this is a question about the VALUE, and a non-negative literal's value
    is non-negative, so binding it into a ``@Nat`` slot needs no guard and
    no obligation.
    """
    def nonneg(e: ast.Expr) -> bool:
        return is_static_nat_typed(e, fncall_ret, slot_is_nat)

    if isinstance(expr, ast.SlotRef):
        return slot_is_nat(expr)
    if isinstance(expr, ast.IntLit):
        return expr.value >= 0
    if isinstance(expr, ast.BinaryExpr):
        if expr.op in (ast.BinOp.ADD, ast.BinOp.SUB, ast.BinOp.MUL,
                       ast.BinOp.DIV, ast.BinOp.MOD):
            return nonneg(expr.left) and nonneg(expr.right)
        return False
    if isinstance(expr, ast.IfExpr):
        if expr.else_branch is None:
            return False
        return nonneg(expr.then_branch) and nonneg(expr.else_branch)
    if isinstance(expr, ast.Block):
        return nonneg(expr.expr)
    if isinstance(expr, ast.MatchExpr):
        if not expr.arms:
            return False
        return all(nonneg(arm.body) for arm in expr.arms)
    if isinstance(expr, (ast.FnCall, ast.ModuleCall)):
        return fncall_ret(expr) == "Nat"
    return False


def has_underflow_leaf(
    expr: ast.Expr, guarded: GuardedSubtractionOracle,
) -> bool:
    """True iff a statically non-negative *expr* holds a subtraction that
    can go below zero: any subtraction but a guarded `@Nat` one (*guarded*),
    whose own check traps first.

    Every literal is an `Int` (spec §4.2), so `@Nat.0 - 1` and `0 - 1` are
    `@Int` subtractions, which no underflow check covers: each is a leaf,
    and binding the value into a `@Nat` slot is the narrowing that checks
    it.  `@Nat.0 - @Nat.1` is the `@Nat` subtraction, never negative.
    """
    if isinstance(expr, ast.BinaryExpr):
        if expr.op == ast.BinOp.SUB and not guarded(expr):
            return True
        return (has_underflow_leaf(expr.left, guarded)
                or has_underflow_leaf(expr.right, guarded))
    if isinstance(expr, ast.Block):
        return has_underflow_leaf(expr.expr, guarded)
    if isinstance(expr, ast.IfExpr):
        if expr.else_branch is None:
            return False
        return (has_underflow_leaf(expr.then_branch, guarded)
                or has_underflow_leaf(expr.else_branch, guarded))
    if isinstance(expr, ast.MatchExpr):
        return any(has_underflow_leaf(arm.body, guarded)
                   for arm in expr.arms)
    return False


def is_guarded_nat_subtraction(
    expr: ast.Expr, is_nat: Callable[[ast.Expr], bool],
) -> bool:
    """Whether *expr* is a `@Nat` subtraction the verifier obligates
    `lhs >= rhs` for and code generation guards (#520): both operands `@Nat`
    by *is_nat*, each side's reading of the checker's type.  One rule, read
    by both sides.  A literal operand is an `Int`, so `@Nat.0 - 1` is an
    `@Int` subtraction and no `@Nat` one (spec §4.4)."""
    return (isinstance(expr, ast.BinaryExpr) and expr.op == ast.BinOp.SUB
            and is_nat(expr.left) and is_nat(expr.right))


# =====================================================================
# The value a join produces
# =====================================================================


def is_resume(expr: ast.Expr) -> bool:
    """True iff *expr* is a handler clause's `resume(...)` — whose value is
    the rest of the handled body's, so it supplies no value of its own to
    the `handle` expression the clause belongs to."""
    return isinstance(expr, ast.FnCall) and expr.name == "resume"


def handle_value_exprs(expr: ast.HandleExpr) -> tuple[ast.Expr, ...]:
    """The expressions whose value a `handle` expression takes: its body's,
    and each clause's where the clause does not resume — `throw(@Int) ->
    Tuple(0, 0)` makes `Tuple(0, 0)` the whole expression's value.  A
    clause's value is read through its own blocks, `if`s and `match`es, and
    a `resume(...)` there supplies nothing new (:func:`is_resume`)."""
    out: list[ast.Expr] = [expr.body]
    for clause in expr.clauses:
        out.extend(_clause_value_exprs(clause.body))
    return tuple(out)


def _clause_value_exprs(expr: ast.Expr) -> tuple[ast.Expr, ...]:
    if is_resume(expr):
        return ()
    if isinstance(expr, ast.Block):
        return () if expr.expr is None else _clause_value_exprs(expr.expr)
    if isinstance(expr, ast.IfExpr):
        if expr.else_branch is None:
            return ()
        return (_clause_value_exprs(expr.then_branch)
                + _clause_value_exprs(expr.else_branch))
    if isinstance(expr, ast.MatchExpr):
        out: tuple[ast.Expr, ...] = ()
        for arm in expr.arms:
            out += _clause_value_exprs(arm.body)
        return out
    return (expr,)


def flow_arms(expr: ast.Expr) -> tuple[ast.Expr, ...] | None:
    """The arms a join's value is one of — a block's tail, an `if`'s
    branches, a `match`'s arms, a `handle`'s body and non-resuming clauses
    (:func:`handle_value_exprs`) — or ``None`` for any other form.  An `if`
    without an `else`, and a block with no tail, have no value to join and
    give ``()``."""
    if isinstance(expr, ast.Block):
        return () if expr.expr is None else (expr.expr,)
    if isinstance(expr, ast.IfExpr):
        if expr.else_branch is None:
            return ()
        return (expr.then_branch, expr.else_branch)
    if isinstance(expr, ast.MatchExpr):
        return tuple(arm.body for arm in expr.arms)
    if isinstance(expr, ast.HandleExpr):
        return handle_value_exprs(expr)
    return None


def value_leaves(expr: ast.Expr) -> tuple[ast.Expr, ...]:
    """The expressions *expr*'s value is one of, read through the joins
    (:func:`flow_arms`); *expr* itself for any other form."""
    arms = flow_arms(expr)
    if arms is None:
        return (expr,)
    out: tuple[ast.Expr, ...] = ()
    for arm in arms:
        out += value_leaves(arm)
    return out


def element_sources(collection: ast.Expr) -> tuple["ComponentSource", ...]:
    """The expressions that can supply an element of *collection*'s value:
    read the way the value flows (:func:`flow_arms`) down to the array
    literals built here, whose elements ARE the values, and through an
    index into such an array.  Anything else is an opaque collection whose
    element type its declaration states (``is_argument`` False)."""
    arms = flow_arms(collection)
    if arms is not None:
        out: tuple[ComponentSource, ...] = ()
        for arm in arms:
            out += element_sources(arm)
        return out
    if isinstance(collection, ast.ArrayLit):
        return tuple(ComponentSource(e, is_argument=True)
                     for e in collection.elements)
    if isinstance(collection, ast.IndexExpr):
        inner = element_sources(collection.collection)
        if inner and all(s.is_argument for s in inner):
            out = ()
            for s in inner:
                out += element_sources(s.expr)
            return out
    return (ComponentSource(collection, is_argument=False),)


# ---------------------------------------------------------------------
# Components: what a destructure or a constructor sub-pattern binds
# ---------------------------------------------------------------------

@dataclass(frozen=True)
class ComponentSource:
    """One expression that can supply the component a pattern binds.

    ``is_argument`` says which question the expression answers.  True: it is
    the argument a constructor was applied to, so the component IS its value
    and the scalar narrowing rule (:func:`narrows_into_nat`) applies to it.
    False: it is an opaque
    composite — a slot, a call, anything whose component type is the one
    its declaration gives it — so the component's type comes from that
    declaration and not from the expression's shape.

    ``path`` places an opaque source under enclosing constructor patterns:
    the ``(constructor, field)`` steps from the expression's declared type
    down to the composite whose component is asked.  Empty at a pattern's
    top level, where the expression's value IS that composite
    (:func:`subcomponent_sources` extends it).
    """

    expr: ast.Expr
    is_argument: bool
    path: tuple[tuple[str, int], ...] = ()


def component_sources(
    expr: ast.Expr,
    index: int,
    ctor_matches: Callable[[str], bool],
    field_is_generic: Callable[[str, int], bool] | None = None,
) -> tuple[ComponentSource, ...]:
    """The expressions that can supply component *index* of *expr*'s value.

    Reads the value the way it flows: through the joins (:func:`flow_arms`
    — a block's tail, both branches of an `if`, every arm of a `match`, a
    `handle`'s body and non-resuming clauses) and an index
    into an array built here (:func:`element_sources`).  A constructor
    application accepted by *ctor_matches* contributes its *index*-th
    argument; one it rejects — a different constructor of the same type,
    which the pattern does not match — contributes nothing, and so does a
    nullary constructor.  Anything else is an opaque source whose component
    type its declaration states.

    *field_is_generic* narrows the argument case to the fields whose type
    the construction takes FROM the argument — a type-parameter field, whose
    instantiation the checker inferred from it.  A field it answers False for
    has a declared type the construction enforces, so the constructor
    application stands as an opaque source typed by that declaration.
    Omitted, every field is read from its argument.

    This is what separates a component's VALUE from the checker's type for
    the whole: `if b then { Tuple(1, @Int.0) } else { Tuple(1, @Nat.0) }`
    supplies `@Int.0` and `@Nat.0`, each read where it is built, where the
    checker gives the join one component type for both.
    """
    arms = flow_arms(expr)
    if arms is not None:
        out: tuple[ComponentSource, ...] = ()
        for arm in arms:
            out += component_sources(arm, index, ctor_matches, field_is_generic)
        return out
    if isinstance(expr, ast.IndexExpr):
        elements = element_sources(expr.collection)
        if any(s.is_argument for s in elements):
            out = ()
            for element in elements:
                if element.is_argument:
                    out += component_sources(
                        element.expr, index, ctor_matches, field_is_generic)
                else:
                    out += (ComponentSource(expr, is_argument=False),)
            return out
        return (ComponentSource(expr, is_argument=False),)
    if isinstance(expr, ast.ConstructorCall):
        if not ctor_matches(expr.name):
            return ()
        if index >= len(expr.args):
            return ()
        if field_is_generic is not None and not field_is_generic(
                expr.name, index):
            return (ComponentSource(expr, is_argument=False),)
        return (ComponentSource(expr.args[index], is_argument=True),)
    if isinstance(expr, ast.NullaryConstructor):
        return ()
    return (ComponentSource(expr, is_argument=False),)


def subcomponent_sources(
    sources: tuple[ComponentSource, ...],
    step: tuple[str, int],
    index: int,
    ctor_matches: Callable[[str], bool],
    field_is_generic: Callable[[str, int], bool] | None = None,
) -> tuple[ComponentSource, ...]:
    """The step into a NESTED constructor pattern: *sources* supply the
    component ``step`` = ``(constructor, field)`` of an outer pattern, which
    the nested pattern matches; this is the sources of that nested value's
    component *index*.

    An argument source is the nested composite's own expression, read the
    way :func:`component_sources` reads a top-level one.  An opaque source
    stays opaque one level deeper: its ``path`` gains *step*, so its leaf
    oracle answers from the declared type reached through it —
    `match W(Tuple(1, 0 - 3)) { W(Tuple(@Int, @Int)) -> … }` supplies
    `0 - 3`, while `match @Wrap<Tuple<Int, Nat>>.0 { … }` supplies the slot's
    `Tuple<Int, Nat>` field."""
    out: tuple[ComponentSource, ...] = ()
    for source in sources:
        if source.is_argument:
            out += component_sources(
                source.expr, index, ctor_matches, field_is_generic)
        else:
            out += (ComponentSource(source.expr, is_argument=False,
                                    path=source.path + (step,)),)
    return out


#: Answers "is component *index* of this opaque source a `@Nat`?" from the
#: composite's DECLARED type — a slot's, a call's return, followed down the
#: source's ``path`` — never from its shape.  ``None`` when the declaration
#: does not say (no such field), which is neither answer: such a component
#: is claimed no narrowing.
LeafComponentIsNat = Callable[[ComponentSource, int], "bool | None"]


def pattern_binding_sources(
    scrutinee: ast.Expr,
    pattern: ast.ConstructorPattern,
    field_is_generic: Callable[[str, int], bool] | None = None,
) -> tuple[tuple[ast.TypeExpr, tuple[ComponentSource, ...], int, str], ...]:
    """Every binding a constructor *pattern* over *scrutinee* makes, at any
    depth: ``(type, sources, field, constructor)`` — the binding's declared
    type, the sources of the component it binds (:func:`component_sources`,
    and one level deeper per nested pattern, :func:`subcomponent_sources`),
    and the constructor field it reads.  The walk both code generation's
    field extraction and the verifier's sub-pattern legs take."""
    out: list[tuple[ast.TypeExpr, tuple[ComponentSource, ...], int, str]] = []

    def walk(pat: ast.ConstructorPattern,
             field_sources: Callable[[int], tuple[ComponentSource, ...]],
             ) -> None:
        for i, sub in enumerate(pat.sub_patterns):
            sources = field_sources(i)
            if isinstance(sub, ast.BindingPattern):
                out.append((sub.type_expr, sources, i, pat.name))
            elif isinstance(sub, ast.ConstructorPattern):
                step = (pat.name, i)

                def inner(j: int, *, _outer: tuple[ComponentSource, ...]
                          = sources, _step: tuple[str, int] = step,
                          _name: str = sub.name,
                          ) -> tuple[ComponentSource, ...]:
                    return subcomponent_sources(
                        _outer, _step, j, lambda n: n == _name,
                        field_is_generic)
                walk(sub, inner)

    walk(pattern, lambda i: component_sources(
        scrutinee, i, lambda n: n == pattern.name, field_is_generic))
    return tuple(out)


def component_narrows(
    sources: tuple[ComponentSource, ...],
    index: int,
    narrows: Callable[[ast.Expr], bool],
    leaf_component_is_nat: LeafComponentIsNat,
) -> bool:
    """True iff binding the component *sources* supply into a `@Nat` slot is
    a narrowing — any source can be negative.  *narrows* is the caller's
    scalar narrowing test (:func:`narrows_into_nat` under its oracle); an
    opaque source narrows when its declaration types the component as
    something other than a `@Nat`, and not when it does not say."""
    return any(
        narrows(source.expr) if source.is_argument
        else leaf_component_is_nat(source, index) is False
        for source in sources
    )


def all_sources_opaque(sources: tuple[ComponentSource, ...]) -> bool:
    """True iff every source of a component is opaque — the only case in
    which the component's DECLARED type is a fact about its value, and so
    one a refined binding may assume (PR #1537 review).  A component built
    here has the type its construction's context gives it and the value of
    its argument, which the binding's own narrowing reads."""
    return bool(sources) and all(not s.is_argument for s in sources)


def nat_narrowing(value: ast.Expr, is_nat: Callable[[ast.Expr], bool]) -> bool:
    """Whether binding *value* into a `@Nat` slot is a narrowing: THE rule
    the verifier records a `nat_bind` obligation by and code generation
    guards by (#552, #1525), each side reading the checker's type of a node
    through *is_nat* (the verifier's ``_narrows_into_nat`` composes these
    same three functions over its reader of the same table).

    A value the checker types `@Nat` narrows only where it holds a
    subtraction no `@Nat`-subtraction check covers (:func:`has_underflow_leaf`).
    Any other value narrows unless it is statically non-negative
    (:func:`narrows_into_nat`), each node read at the checker's type of it:
    a non-negative literal, `@Nat.0 + 1`, `if c then { @Nat.0 } else { 0 }`
    are no narrowing, while `@Int.0`, `-1`, `0 - 1` and `@Nat.0 - 1` are.
    A value of an alias of `Nat` is a `@Nat`: the type is the checker's, not
    the spelling's."""
    def guarded(expr: ast.Expr) -> bool:
        return is_guarded_nat_subtraction(expr, is_nat)

    if is_nat(value):
        return has_underflow_leaf(value, guarded)
    return narrows_into_nat(
        value, lambda call: "Nat" if is_nat(call) else None, guarded, is_nat)


def narrows_into_nat(
    expr: ast.Expr, fncall_ret: FnCallTypeOracle,
    guarded: GuardedSubtractionOracle,
    slot_is_nat: SlotIsNatOracle = _declared_nat_slot,
) -> bool:
    """True iff binding *expr* into a ``@Nat`` slot needs a ``>= 0`` guard:
    its value is not statically non-negative (:func:`is_static_nat_typed`),
    or it holds a subtraction no `@Nat`-subtraction check covers
    (:func:`has_underflow_leaf`)."""
    if not is_static_nat_typed(expr, fncall_ret, slot_is_nat):
        return True
    return has_underflow_leaf(expr, guarded)
