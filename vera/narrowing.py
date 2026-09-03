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


def narrows_into_nat(
    expr: ast.Expr, fncall_ret: FnCallTypeOracle, nat_origin: NatOriginOracle,
) -> bool:
    """True iff binding *expr* into a ``@Nat`` slot needs a ``>= 0`` guard."""
    if not is_static_nat_typed(expr, fncall_ret):
        return True
    return has_underflow_leaf(expr, nat_origin)
