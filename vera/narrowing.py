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

from vera import ast

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
