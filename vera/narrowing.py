"""The one derivation of whether binding a value into a `@Nat` slot needs a
runtime guard (#1205 parity, re-keyed in #1362).

Codegen and the verifier both have to answer "does a guard get planted here?",
and they answered it with two parallel implementations — ``_is_static_nat_typed``
/ ``_is_nat_typed``, and ``_has_underflow_leaf`` written twice.  Two copies of a
rule are two things that can drift, and a drift here is invisible from inside
either component: the verifier reports a status about codegen's behaviour, so if
they disagree the status is simply wrong and nothing local notices.

The RULE lives here once.  What legitimately differs between the callers is the
TYPE ORACLE, not the rule:

* codegen reads a `SlotRef`'s declared ``type_name`` and infers a call's return
  type from its own tables;
* the verifier reads the checker's SEMANTIC types, which are more precise — a
  handler-clause binder declared ``@Nat`` carries the thrown ``@Int`` as its
  semantic source, which is exactly why the verifier obligates a narrowing there
  that codegen does not see.

Both readings are correct for their own question.  The verifier asks "is there a
narrowing to obligate?" and needs the semantic one; the CLASSIFICATION asks
"will codegen plant a guard?" and must be answered with codegen's, or the status
describes a component other than the one it is about.  So the oracle is a
parameter and the rule is not.
"""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass

from vera import ast, binders

#: The effects whose operations code generation can lower at all (#754).
#:
#: A guard is a claim about a RUN, so an operation of an effect codegen
#: refuses cannot be "guarded" in any useful sense: the enclosing function is
#: dropped with a loud E603 and there is no run to guard.  The verifier's
#: op-argument classification therefore has to intersect its guard question
#: with this set, or it repeats the #1268 mistake one boundary over —
#: recording a Tier-3 runtime check for a program that never reaches a
#: runtime.
#:
#: Here rather than in the backend because both sides read it: codegen's
#: `_is_compilable` decides membership FROM this set, and the verifier's
#: `_effect_op_formal_guarded` asks about it.  Two copies of the roster is
#: exactly the drift this module exists to prevent.
COMPILABLE_EFFECTS = frozenset({
    "IO", "State", "Exn", "Http", "Async", "HttpServer",
    "Inference", "DB", "Random",
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

#: Answers "does this subtraction have @Nat provenance?" — the #520-exempt
#: ``0 - 1`` idiom is the case that matters.
NatOriginOracle = Callable[[ast.Expr], bool]


def is_static_nat_typed(expr: ast.Expr, fncall_ret: FnCallTypeOracle) -> bool:
    """True iff *expr* has static type ``@Nat`` under the caller's oracle.

    Returns True for a ``@Nat`` slot reference, a non-negative ``IntLit``,
    arithmetic whose operands are both ``@Nat`` (the ``Nat <: Int`` subtyping
    rule), an ``IfExpr`` / ``MatchExpr`` whose every branch is, and a call whose
    oracle answers ``Nat``.  Conservative False elsewhere — a ``UnaryExpr``
    negation always produces ``@Int``.
    """
    if isinstance(expr, ast.SlotRef):
        return expr.type_name == "Nat"
    if isinstance(expr, ast.IntLit):
        return expr.value >= 0
    if isinstance(expr, ast.BinaryExpr):
        if expr.op in (ast.BinOp.ADD, ast.BinOp.SUB, ast.BinOp.MUL,
                       ast.BinOp.DIV, ast.BinOp.MOD):
            return (is_static_nat_typed(expr.left, fncall_ret)
                    and is_static_nat_typed(expr.right, fncall_ret))
        return False
    if isinstance(expr, ast.IfExpr):
        if expr.else_branch is None:
            return False
        return (is_static_nat_typed(expr.then_branch, fncall_ret)
                and is_static_nat_typed(expr.else_branch, fncall_ret))
    if isinstance(expr, ast.Block):
        return is_static_nat_typed(expr.expr, fncall_ret)
    if isinstance(expr, ast.MatchExpr):
        if not expr.arms:
            return False
        return all(is_static_nat_typed(arm.body, fncall_ret)
                   for arm in expr.arms)
    if isinstance(expr, (ast.FnCall, ast.ModuleCall)):
        return fncall_ret(expr) == "Nat"
    return False


def has_underflow_leaf(expr: ast.Expr, nat_origin: NatOriginOracle) -> bool:
    """True iff a statically-``@Nat`` *expr* hides a pure-literal subtraction.

    The ``0 - 1`` idiom is ``@Nat``-typed by the rule above and can still go
    negative, so it needs a guard even though the type says otherwise.
    """
    if isinstance(expr, ast.BinaryExpr):
        if expr.op == ast.BinOp.SUB and not nat_origin(expr):
            return True
        return (has_underflow_leaf(expr.left, nat_origin)
                or has_underflow_leaf(expr.right, nat_origin))
    if isinstance(expr, ast.Block):
        return has_underflow_leaf(expr.expr, nat_origin)
    if isinstance(expr, ast.IfExpr):
        if expr.else_branch is None:
            return False
        return (has_underflow_leaf(expr.then_branch, nat_origin)
                or has_underflow_leaf(expr.else_branch, nat_origin))
    if isinstance(expr, ast.MatchExpr):
        return any(has_underflow_leaf(arm.body, nat_origin)
                   for arm in expr.arms)
    return False


# =====================================================================
# THE classifier every guard and every obligation reads (#1503)
# =====================================================================
#
# The checker types an arithmetic expression bottom-up: it synthesizes both
# operands with no expected type, a non-negative literal is `@Nat`, and
# `Nat - Nat` is `Nat` — so its table records `0 - 3` as `@Nat`, and a
# constructor or tuple built from it as carrying a `@Nat` component.  That is
# a claim about a value that is -3.  Spec §4.2 types an integer literal from
# its context and §4.4 types arithmetic as the join of its operands, so in an
# `@Int` context `0 - 3` is an `@Int`; §11.2.1 exempts the pure-literal
# subtraction from the underflow guard for exactly that reason ("commonly
# consumed at `@Int` positions").  The table is not corrected here — the
# classifier below is what every guard and obligation decision reads
# instead, so a decision can no longer turn on the table's `@Nat` for a value
# the classifier knows can be negative.

#: The largest value an `@Int` slot holds, and so the largest `@Nat` that
#: widens into one without reinterpreting.
I64_MAX = (1 << 63) - 1

_INT_ARITH_OPS = frozenset({
    ast.BinOp.ADD, ast.BinOp.SUB, ast.BinOp.MUL, ast.BinOp.DIV,
    ast.BinOp.MOD,
})

#: Answers "is this expression's value a genuine `@Nat`?" from its
#: DECLARATION — the checker's resolved type of a slot, a call, an index into
#: an opaque array, an effect operation — for every form
#: :func:`result_is_nat` does not decompose (:data:`RESULT_IS_NAT_READING`
#: ``"declared"``, and an opaque ``"index"``).
DeclaredIsNatOracle = Callable[[ast.Expr], bool]


def is_pure_literal(expr: ast.Expr) -> bool:
    """True iff every value-producing leaf of *expr* is an integer literal.

    Syntactic, so the verifier and code generation answer it identically —
    unlike the `@Nat`-provenance oracles, which read a call's or an index's
    type from two different tables.  A value-producing leaf is a literal
    reached through arithmetic, negation, a block's tail, and the branches of
    an `if` or a `match`; a slot, a call, an index or anything else makes the
    expression not pure.
    """
    if isinstance(expr, ast.IntLit):
        return True
    if isinstance(expr, ast.BinaryExpr):
        return (expr.op in _INT_ARITH_OPS
                and is_pure_literal(expr.left)
                and is_pure_literal(expr.right))
    if isinstance(expr, ast.UnaryExpr):
        return expr.op == ast.UnaryOp.NEG and is_pure_literal(expr.operand)
    if isinstance(expr, ast.Block):
        return expr.expr is not None and is_pure_literal(expr.expr)
    if isinstance(expr, ast.IfExpr):
        return (expr.else_branch is not None
                and is_pure_literal(expr.then_branch)
                and is_pure_literal(expr.else_branch))
    if isinstance(expr, ast.MatchExpr):
        return bool(expr.arms) and all(is_pure_literal(arm.body)
                                       for arm in expr.arms)
    return False


def _truncating_div(a: int, b: int) -> int:
    """`i64.div_s`'s quotient over unbounded integers: truncation toward
    zero, which Python's `//` (flooring) is not for a negative operand."""
    q = abs(a) // abs(b)
    return q if (a >= 0) == (b >= 0) else -q


def literal_range(expr: ast.Expr) -> tuple[int, int] | None:
    """The least and the greatest value a pure-literal *expr* can take,
    folded exactly over unbounded integers; ``None`` when *expr* is not
    pure-literal (:func:`is_pure_literal`) or the fold cannot say — a zero
    divisor, or a division over a range rather than a single value.

    A literal-only expression's value is known at compile time, so its sign
    need not be guessed from its shape: `0 - 3` is -3 and `5 - 3` is 2,
    though the checker types both `Nat - Nat`.  An `if` or a `match` over
    literal arms takes the hull of its arms.
    """
    if isinstance(expr, ast.IntLit):
        return (expr.value, expr.value)
    if isinstance(expr, ast.UnaryExpr):
        if expr.op != ast.UnaryOp.NEG:
            return None
        inner = literal_range(expr.operand)
        return None if inner is None else (-inner[1], -inner[0])
    if isinstance(expr, ast.Block):
        return None if expr.expr is None else literal_range(expr.expr)
    if isinstance(expr, ast.IfExpr):
        if expr.else_branch is None:
            return None
        arms = [literal_range(expr.then_branch),
                literal_range(expr.else_branch)]
    elif isinstance(expr, ast.MatchExpr):
        arms = [literal_range(arm.body) for arm in expr.arms]
    elif isinstance(expr, ast.BinaryExpr) and expr.op in _INT_ARITH_OPS:
        left = literal_range(expr.left)
        right = literal_range(expr.right)
        if left is None or right is None:
            return None
        (a0, a1), (b0, b1) = left, right
        if expr.op == ast.BinOp.ADD:
            return (a0 + b0, a1 + b1)
        if expr.op == ast.BinOp.SUB:
            return (a0 - b1, a1 - b0)
        if expr.op == ast.BinOp.MUL:
            corners = (a0 * b0, a0 * b1, a1 * b0, a1 * b1)
            return (min(corners), max(corners))
        if a0 != a1 or b0 != b1 or b0 == 0:
            return None
        quotient = _truncating_div(a0, b0)
        value = quotient if expr.op == ast.BinOp.DIV else a0 - b0 * quotient
        return (value, value)
    else:
        return None
    if not arms or any(arm is None for arm in arms):
        return None
    return (min(arm[0] for arm in arms if arm is not None),
            max(arm[1] for arm in arms if arm is not None))


def holds_literal_subtraction(expr: ast.Expr) -> bool:
    """True iff *expr*'s value-producing tree holds a subtraction of two
    pure-literal operands — the #520 idiom, whichever way it folds.

    STRUCTURAL, on purpose: it is the node the narrowing classifier's
    underflow leaf (:func:`has_underflow_leaf`) treats as possibly negative,
    so a question asked with it lines up with where a `nat_bind` obligation
    is raised.  :func:`literal_range` is the folded reading, for a question
    about a literal-only value's actual sign.
    """
    if isinstance(expr, ast.BinaryExpr):
        if expr.op not in _INT_ARITH_OPS:
            return False
        if (expr.op == ast.BinOp.SUB and is_pure_literal(expr.left)
                and is_pure_literal(expr.right)):
            return True
        return (holds_literal_subtraction(expr.left)
                or holds_literal_subtraction(expr.right))
    if isinstance(expr, ast.UnaryExpr):
        return holds_literal_subtraction(expr.operand)
    if isinstance(expr, ast.Block):
        return expr.expr is not None and holds_literal_subtraction(expr.expr)
    if isinstance(expr, ast.IfExpr):
        return (expr.else_branch is not None
                and (holds_literal_subtraction(expr.then_branch)
                     or holds_literal_subtraction(expr.else_branch)))
    if isinstance(expr, ast.MatchExpr):
        return any(holds_literal_subtraction(arm.body) for arm in expr.arms)
    return False


def carries_literal_subtraction(expr: ast.Expr) -> bool:
    """:func:`holds_literal_subtraction`, through the components of a
    composite.

    The checker's type for a tuple, a constructor application or an array
    literal is assembled from its components' bottom-up types, so
    `Tuple(1, 0 - 3)` is a `Tuple<Nat, Nat>` and `[0 - 3]` an `Array<Nat>`:
    the `@Nat` the classifier refutes is inside.  This is the question for a
    TYPE the checker derived from such a value — an instantiation it
    inferred from it — rather than for the value's own sign.
    """
    if holds_literal_subtraction(expr):
        return True
    if isinstance(expr, ast.ConstructorCall):
        return any(carries_literal_subtraction(a) for a in expr.args)
    if isinstance(expr, ast.ArrayLit):
        return any(carries_literal_subtraction(e) for e in expr.elements)
    if isinstance(expr, ast.Block):
        return (expr.expr is not None
                and carries_literal_subtraction(expr.expr))
    if isinstance(expr, ast.IfExpr):
        return (expr.else_branch is not None
                and (carries_literal_subtraction(expr.then_branch)
                     or carries_literal_subtraction(expr.else_branch)))
    if isinstance(expr, ast.MatchExpr):
        return any(carries_literal_subtraction(arm.body)
                   for arm in expr.arms)
    return False


def literal_operation_width(expr: ast.Expr) -> str | None:
    """The width an arithmetic operation of two literal-only operands runs
    at, read from their VALUES — ``"Int"`` when either can be negative —
    or ``None`` to leave the question to the checker's operand types.

    The checker types each operand bottom-up, so `(0 - 4) + 1` is a
    `Nat + Nat` and was classified a u64 add: the verifier refused it (E528,
    since -3 is outside the unsigned range) and `(0 - 3) * 2` trapped as an
    unsigned overflow, on programs whose values are -3 and -6.  Both
    operands are known here (:func:`literal_range`), so the one that is
    negative makes the operation the signed one it is.

    Deliberately NOT extended to an operation with a non-literal operand.
    `@Nat.0 + (0 - 1)` mixes a `@Nat` that may exceed `i64.MAX` with a
    negative value, and no one machine width serves both: signed, the `@Nat`
    operand is reinterpreted and a large one returns a wrong value silently;
    unsigned, the negative one is.  That operation keeps the checker's
    width, which refuses rather than reinterprets — mixed-sign arithmetic
    needs an operand-widening check this classifier cannot supply.  A
    subtraction of two NON-negative literals (`0 - 1`) keeps it too: it is
    the #520 idiom, exempt as it always was.
    """
    if not (isinstance(expr, ast.BinaryExpr) and expr.op in _INT_ARITH_OPS):
        return None
    if not (is_pure_literal(expr.left) and is_pure_literal(expr.right)):
        return None
    ranges = [literal_range(operand) for operand in (expr.left, expr.right)]
    # A literal above `i64.MAX` is a `@Nat`-only value, so beside a negative
    # one it is mixed-sign arithmetic in literal form: the signed width would
    # reinterpret it (`18446744073709551615 + (0 - 1)` came back as -2), and
    # the checker's unsigned width refuses instead.
    if any(r is not None and r[1] > I64_MAX for r in ranges):
        return None
    for folded in ranges:
        if folded is None or folded[0] < 0:
            return "Int"
    return None


def is_nonneg_int_literal(expr: ast.Expr) -> bool:
    """True iff *expr* is (a block trailing into) a non-negative integer
    literal — always a value an `@Int` slot can hold unchanged (#813)."""
    while isinstance(expr, ast.Block):
        if expr.expr is None:
            return False
        expr = expr.expr
    return isinstance(expr, ast.IntLit) and expr.value >= 0


def is_nonneg_literal_value(expr: ast.Expr) -> bool:
    """True iff *expr* is literal-only and its folded value cannot be
    negative — `5`, and equally `2 + 3` or `if c then { 1 } else { 2 }`.

    Every join's notion of a `@Nat`-compatible literal: an arm of an `if`,
    a `match` or a `handle` (:func:`arm_nat_compatible`), a component's
    argument (:func:`component_is_nat`), an array element.  Counting only
    a bare `IntLit` left `2 + 3` out, and an arm left out drops the guard on
    its genuine `@Nat` sibling wherever no per-arm guard stands in —
    `if c then { Tuple(1, @Nat.0) } else { Tuple(1, 2 + 3) }` read out at
    `@Int` returned u64.MAX as -1.
    """
    if not is_pure_literal(expr):
        return False
    folded = literal_range(expr)
    return folded is not None and folded[0] >= 0


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


#: How :func:`result_is_nat` reads each expression form: EVERY `ast.Expr`
#: subclass, so a form the rule does not decompose is answered from its
#: declaration rather than falling through to "not a `@Nat`" unread
#: (`tests/test_one_classifier_1503.py` checks the keys against the AST).
#:
#: - ``"fold"``: a literal-only value, classified by its folded value.
#: - ``"flow"``: its value is one of its arms' — a block's tail, an `if`'s
#:   branches, a `match`'s arms, a `handle`'s body and non-resuming clauses —
#:   so it is a join over them.
#: - ``"arith"``: an arithmetic operator, a `@Nat` iff both operands are.
#: - ``"index"``: an array element — the elements themselves where the
#:   array is built here, the declared element type where it is opaque.
#: - ``"declared"``: its type is a declaration's (a slot, a call, an effect
#:   operation, `old` / `new`, a `@T.result`, a hole) — the side's oracle.
#: - ``"never"``: a negation (an `@Int`), or not an integer value at all.
RESULT_IS_NAT_READING: dict[type, str] = {
    ast.IntLit: "fold",
    ast.BinaryExpr: "arith",
    ast.Block: "flow",
    ast.IfExpr: "flow",
    ast.MatchExpr: "flow",
    ast.HandleExpr: "flow",
    ast.IndexExpr: "index",
    ast.SlotRef: "declared",
    ast.ResultRef: "declared",
    ast.FnCall: "declared",
    ast.ModuleCall: "declared",
    ast.QualifiedCall: "declared",
    ast.OldExpr: "declared",
    ast.NewExpr: "declared",
    ast.HoleExpr: "declared",
    ast.UnaryExpr: "never",
    ast.ConstructorCall: "never",
    ast.NullaryConstructor: "never",
    ast.ArrayLit: "never",
    ast.StringLit: "never",
    ast.InterpolatedString: "never",
    ast.BoolLit: "never",
    ast.FloatLit: "never",
    ast.UnitLit: "never",
    ast.AnonFn: "never",
    ast.AssertExpr: "never",
    ast.AssumeExpr: "never",
    ast.ForallExpr: "never",
    ast.ExistsExpr: "never",
}


def flow_arms(expr: ast.Expr) -> tuple[ast.Expr, ...] | None:
    """The arms a ``"flow"`` form's value is one of, or ``None`` for any
    other form.  An `if` without an `else`, and a block with no tail, have
    no value to join and give ``()``."""
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
    """The expressions *expr*'s value is one of, read through the
    ``"flow"`` forms (:func:`flow_arms`); *expr* itself for any other
    form."""
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


def result_is_nat(expr: ast.Expr, declared_is_nat: DeclaredIsNatOracle) -> bool:
    """True iff the VALUE of *expr* is a genuine runtime `@Nat` — one that
    can exceed `i64.MAX`, so binding it into an `@Int` slot is a widening
    that needs the `nat_to_int_coerce` obligation and its guard (#813).

    THE rule, read by the verifier's obligation legs and by code
    generation's guards alike; before #1503 each side carried a copy.  Each
    form is read as :data:`RESULT_IS_NAT_READING` says.

    Only what is LITERAL-DERIVED is classified by its value: a literal-only
    expression's value is known (:func:`literal_range`), and one no greater
    than `i64.MAX` needs no widening check — in an `@Int` context it is
    range-checked against its target (#812) — while one above `i64.MAX` is a
    value only a `@Nat` holds, a widening that cannot succeed.  A value
    built here is read where it is built: arithmetic is a `@Nat` iff BOTH
    operands are genuine, a join (:func:`flow_arms`) iff every arm is
    `@Nat`-compatible — a genuine `@Nat` or a non-negative literal — and at
    least one is genuine (#813 site 2a), an array element iff the elements
    of an array built here are (:func:`element_sources`).  Every other form
    — a slot, a call, an index into an opaque array, an effect operation —
    has a declaration, and *declared_is_nat* answers from it: that is the
    checker's resolved type, which is right for every shape not built from
    a literal.  `nat_to_int(x)` is the explicit conversion built-in, whose
    value is its argument's.  A negation, and a non-integer, is not a
    `@Nat`.
    """
    if is_pure_literal(expr):
        folded = literal_range(expr)
        return folded is not None and folded[0] >= 0 and folded[1] > I64_MAX
    reading = RESULT_IS_NAT_READING.get(type(expr), "never")
    if reading == "flow":
        arms = flow_arms(expr) or ()
        return (
            bool(arms)
            and all(arm_nat_compatible(arm, declared_is_nat) for arm in arms)
            and any(result_is_nat(arm, declared_is_nat) for arm in arms)
        )
    if reading == "arith" and isinstance(expr, ast.BinaryExpr):
        if expr.op in _INT_ARITH_OPS:
            return (result_is_nat(expr.left, declared_is_nat)
                    and result_is_nat(expr.right, declared_is_nat))
        return False
    if reading == "index" and isinstance(expr, ast.IndexExpr):
        sources = element_sources(expr.collection)
        if not any(s.is_argument for s in sources):
            return declared_is_nat(expr)
        compatible = True
        genuine = False
        for source in sources:
            if source.is_argument:
                nat = result_is_nat(source.expr, declared_is_nat)
                compatible = compatible and (
                    nat or is_nonneg_literal_value(source.expr))
            else:
                nat = declared_is_nat(expr)
                compatible = compatible and nat
            genuine = genuine or nat
        return compatible and genuine
    if reading == "declared":
        if isinstance(expr, ast.SlotRef) and expr.type_name == "Nat":
            return True
        if (isinstance(expr, ast.FnCall) and expr.name == "nat_to_int"
                and expr.args
                and result_is_nat(expr.args[0], declared_is_nat)):
            return True
        return declared_is_nat(expr)
    return False


def arm_nat_compatible(
    expr: ast.Expr, declared_is_nat: DeclaredIsNatOracle,
) -> bool:
    """A join's arm is `@Nat`-compatible if its value is a genuine `@Nat`
    (:func:`result_is_nat`) or a literal-only value that cannot be negative
    (#813 site 2a; :func:`is_nonneg_literal_value`, so `2 + 3` counts as
    `5` does).

    Such a literal no greater than ``i64.MAX`` (#812 range-checks it) can
    neither out-of-range-widen nor false-trap the boundary widen guard, and
    one above it is a genuine `@Nat`, which the guard refuses.  Treating it as compatible keeps a heterogeneous-with-literal join
    (``if c then { @Nat.0 } else { 0 }``) classified `@Nat`, so the REAL
    `@Nat` arm is obligated and guarded at the single boundary site without
    the per-arm join type, which the checker's side-tables do not record.  A
    genuine `@Int` arm (a slot or call that can be negative) is NOT
    compatible: it makes the join `@Int`, and a `@Nat` sibling widening into
    it is the heterogeneous per-arm case — obligated through the verifier's
    `_is_hetero_int_widen_join` and guarded per-arm by codegen (#820), not a
    boundary widening."""
    return (result_is_nat(expr, declared_is_nat)
            or is_nonneg_literal_value(expr))


# ---------------------------------------------------------------------
# Components: what a destructure or a constructor sub-pattern binds
# ---------------------------------------------------------------------

@dataclass(frozen=True)
class ComponentSource:
    """One expression that can supply the component a pattern binds.

    ``is_argument`` says which question the expression answers.  True: it is
    the argument a constructor was applied to, so the component IS its value
    and the scalar classifier applies to it.  False: it is an opaque
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

    Reads the value the way it flows: through the ``"flow"`` forms
    (:func:`flow_arms` — a block's tail, both branches of an `if`, every arm
    of a `match`, a `handle`'s body and non-resuming clauses) and an index
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
    the whole: `Tuple(1, 0 - 3)` supplies `0 - 3`, which the classifier calls
    an `@Int`, where the checker's `Tuple<Nat, Nat>` says `@Nat`.
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
#: is claimed neither a widening nor a narrowing.
LeafComponentIsNat = Callable[[ComponentSource, int], "bool | None"]


def component_is_nat(
    sources: tuple[ComponentSource, ...],
    index: int,
    declared_is_nat: DeclaredIsNatOracle,
    leaf_component_is_nat: LeafComponentIsNat,
) -> bool:
    """True iff the component *sources* supply is a genuine `@Nat` — the
    widening question for an `@Int` binding, joined over the sources the
    way :func:`result_is_nat` joins the arms of an `if`: every source
    `@Nat`-compatible (a genuine `@Nat`, or a literal-only value that cannot
    be negative, :func:`is_nonneg_literal_value`), at least one genuine."""
    if not sources:
        return False
    compatible = True
    genuine = False
    for source in sources:
        if source.is_argument:
            nat = result_is_nat(source.expr, declared_is_nat)
            compatible = compatible and (
                nat or is_nonneg_literal_value(source.expr))
        else:
            nat = leaf_component_is_nat(source, index) is True
            compatible = compatible and nat
        genuine = genuine or nat
    return compatible and genuine


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
    here from `0 - 5` has the checker's `Nat` for its type and -5 for its
    value."""
    return bool(sources) and all(not s.is_argument for s in sources)


def measure_component_needs_range_check(resolved_ty: object) -> bool:
    """True iff a ``decreases`` measure component of resolved type
    *resolved_ty* can read differently to the prover and to the runtime
    guard (#1222).

    Clause of THE RULE, for the termination measure.  The proof reasons over
    unbounded integers and the guard compares with ``i64.lt_s`` /
    ``i64.ge_s``, so the two agree exactly while the component's value is an
    i64.  A ``@Nat`` is a u64 in that i64 and is the only component that can
    leave it; an ``@Int`` IS that i64, and an ADT component is ranked by a
    heap-bounded structural size.

    Takes the CHECKER's resolved type — duck-typed, so this module keeps its
    single ``vera.ast`` import — because the two consumers previously asked
    two different oracles and the wrong one had a fallback that coincided
    with a real answer: the verifier read the checker's types (a user
    function's declared ``@Nat`` return resolves), while codegen re-derived
    from its own walker, which answers ``'Int'`` for a call — and ``'Int'``
    is also the value meaning "no check needed", so a call-result measure was
    obligated and never guarded, silently.  A component this cannot classify
    is ``None`` at the table, which is distinct from ``Int`` and therefore
    cannot be mistaken for a decision.
    """
    base = getattr(resolved_ty, "base", resolved_ty)
    return getattr(base, "name", None) == "Nat"


def measure_component_is_effect_free(expr: ast.Expr) -> bool:
    """True iff evaluating *expr* an EXTRA time can be observed (#1222,
    CodeRabbit review).

    Clause of THE RULE, for the one place a ``decreases`` measure is
    evaluated that the chain guard does not already evaluate it: the range
    check emitted beside a DECLINED chain guard.  On the chain path the
    measure is evaluated once and the range check reads the locals, so
    nothing new runs; on the decline path the check evaluates the component
    itself, and for an effectful component that is a new observable action
    at function entry.

    Measured: `decreases(risky(@Nat.0))` on a function declaring
    `Exn<Int>`, where `risky` throws — the chain guard is declined for
    exactly that reason, and evaluating the measure at entry turned a
    program that returned 0 into one that throws before its body runs.

    Syntactic and deliberately narrow: a slot reference, an integer
    literal, and arithmetic over those.  Every measure in the corpus is a
    slot reference.  A CALL is excluded whatever its declared row, because
    the row is not what this asks — an extra evaluation of a pure call is
    still extra work at every activation, and the honest answer where the
    check cannot be emitted is to disclose it rather than to pay for it.
    """
    if isinstance(expr, (ast.SlotRef, ast.IntLit)):
        return True
    if isinstance(expr, ast.BinaryExpr):
        return (measure_component_is_effect_free(expr.left)
                and measure_component_is_effect_free(expr.right))
    if isinstance(expr, ast.UnaryExpr):
        return measure_component_is_effect_free(expr.operand)
    return False


def narrows_into_nat(
    expr: ast.Expr, fncall_ret: FnCallTypeOracle, nat_origin: NatOriginOracle,
) -> bool:
    """True iff binding *expr* into a ``@Nat`` slot needs a ``>= 0`` guard."""
    if not is_static_nat_typed(expr, fncall_ret):
        return True
    return has_underflow_leaf(expr, nat_origin)
