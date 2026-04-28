"""Tail-position analysis for #517 (WASM `return_call`).

A WASM ``return_call $foo`` instruction is the tail-call equivalent of
``call $foo`` — instead of pushing a fresh activation frame for the
callee, it reuses the current frame.  This keeps the call stack flat
across tail-recursive functions, which is exactly what `SKILL.md`
documents as the canonical Vera iteration idiom (no `for` / `while`
— iteration is tail recursion).

Pre-fix, every Vera ``call`` site emitted a plain WASM ``call``,
including syntactic tail calls.  A loop-shaped recursion (``f(n) =
... f(n-1)``) thus pushed one frame per iteration and trapped with
"call stack exhausted" at ~tens of thousands of frames.  This
module identifies the FnCall AST nodes that are in tail position so
the translator (`vera/wasm/calls.py::_translate_call`) can emit
``return_call`` instead of ``call``.

Tail position is a syntactic property defined recursively on the
function body:

* The body's trailing expression IS in tail position.
* If a sub-expression is in tail position and is an ``IfExpr``, both
  branch bodies are in tail position.  The condition is NOT.
* If a sub-expression is in tail position and is a ``MatchExpr``,
  every arm body is in tail position.  The scrutinee is NOT.
* If a sub-expression is in tail position and is a ``Block``, only
  the trailing expression is in tail position.  Statement values
  (``let`` initialisers, ``ExprStmt`` expressions) are NOT.

All other constructs (call arguments, quantifier bodies, assert /
assume conditions, handle bodies, anonymous-fn bodies, indexing)
are NOT tail-transparent — calls inside them are NOT in tail
position regardless of the parent's status.

The analyzer returns a ``set[int]`` of ``id(FnCall)`` nodes.  The
translator looks up ``id(call) in tail_call_sites`` at emit time.
``id``-based identity is stable for the lifetime of a single
``compile_fn`` invocation (the FnDecl is not mutated and not cloned
between analysis and emit), and per-fn isolation prevents
cross-function id collisions because each ``_compile_fn`` builds a
fresh ``WasmContext`` and computes a fresh tail-call set.

The translator pairs the syntactic-tail-position check with a
runtime-side type-safety check: WASM ``return_call`` requires the
callee's signature to match the caller's, so the translator falls
back to plain ``call`` whenever the resolved callee's WASM return
type doesn't match the current function's return type.  The
analyzer is intentionally agnostic to type compatibility — it only
identifies syntactic tail positions.
"""

from __future__ import annotations

from vera import ast


def compute_tail_call_sites(decl: ast.FnDecl) -> set[int]:
    """Return ``{id(call)}`` for every ``FnCall`` in tail position
    inside ``decl.body``.

    The body's trailing expression is the seed; tail position
    propagates inward through ``IfExpr`` / ``MatchExpr`` / ``Block``
    in the rules documented at the module level.  Any other
    construct stops the propagation.

    Returns an empty set if the body has no syntactic tail calls,
    or if the body is missing (defensive — shouldn't happen for
    successfully-parsed FnDecls).
    """
    sites: set[int] = set()
    if decl.body is None:  # pragma: no cover — defensive
        return sites

    def visit_tail(expr: ast.Expr) -> None:
        """Mark FnCalls in tail position rooted at ``expr``.

        Caller guarantees ``expr`` itself is in tail position.
        """
        if isinstance(expr, ast.FnCall):
            sites.add(id(expr))
            return
        if isinstance(expr, ast.IfExpr):
            visit_tail(expr.then_branch)
            if expr.else_branch is not None:
                visit_tail(expr.else_branch)
            return
        if isinstance(expr, ast.MatchExpr):
            for arm in expr.arms:
                visit_tail(arm.body)
            return
        if isinstance(expr, ast.Block):
            # Statements are NOT in tail position; only the trailing
            # expression inherits tail status from the enclosing
            # block.
            visit_tail(expr.expr)
            return
        # All other constructs (literals, slot refs, BinaryExpr,
        # UnaryExpr, QualifiedCall, ConstructorCall, AnonFn,
        # HandleExpr, ArrayLit, IndexExpr, AssertExpr, AssumeExpr,
        # quantifiers, OldExpr / NewExpr, InterpolatedString,
        # StringLit, ResultRef, NullaryConstructor, ModuleCall) are
        # NOT tail-transparent.  A call inside their sub-expressions
        # is not in tail position.  No further marking required.

    visit_tail(decl.body)
    return sites
