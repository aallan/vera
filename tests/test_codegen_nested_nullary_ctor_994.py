"""Regression: nested payload-less constructor in a forall ``==``/``!=`` (#994 F2).

PR #994 (the #979/#981 checker adoption) newly accepts a ``forall<T>`` function
whose ``ensures`` compares a payload-less nested constructor (``Some(None)``)
against ``@Option<Option<T>>.result``.  ``vera check`` and ``vera verify`` pass,
but ``vera compile`` raised a spurious **E613** — the codegen structural-Eq
derivation could not resolve the operand's type argument:

* the inner ``None`` renders as the bare ``Option`` (no payload to recover
  ``<Int>`` from), so ``Some(None)`` recovers as the erased ``Option<Option>``;
* the dead base generic clone's slot operand renders as ``Option<Option<T>>``,
  whose nested free ``T`` the top-level-only free-var check missed — so the
  base clone routed to structural derivation instead of the scalar (dead-code)
  lowering, raising E613.

Both operands of a ``==`` share a type (checker E142 otherwise), and a
monomorphized clone substitutes the sibling slot to a fully concrete name, so
the fix recovers the fully-concrete name from whichever operand carries it and
falls back to the scalar lowering only when NEITHER is fully resolved (the dead
base clone).  Every program below must ``check`` + ``verify`` + ``compile`` +
RUN to its sentinel — the whole pipeline, not just ``check``.
"""
from __future__ import annotations

from vera.checker import typecheck_with_artifacts
from vera.codegen import CompileResult, compile as codegen_compile, execute
from vera.parser import parse_to_ast
from vera.verifier import verify


def _check_compile_run(source: str) -> int:
    """Mirror the CLI: typecheck (with artifacts) -> verify -> compile -> run.

    Threads the #747 semantic/target side-tables into both verify and compile,
    exactly as ``cmd_verify`` / ``cmd_compile`` do, so this exercises the same
    lowering the CLI hit.
    """
    ast = parse_to_ast(source)
    check_diags, arts = typecheck_with_artifacts(ast, source)
    assert not [d for d in check_diags if d.severity == "error"], (
        f"check errors: {[d.description for d in check_diags if d.severity == 'error']}"
    )
    vr = verify(
        ast, source,
        expr_types=arts.expr_semantic_types,
        expr_target_types=arts.expr_target_types,
    )
    assert not [d for d in vr.diagnostics if d.severity == "error"], (
        f"verify errors: {[d.description for d in vr.diagnostics if d.severity == 'error']}"
    )
    result: CompileResult = codegen_compile(
        ast, source=source,
        expr_semantic_types=arts.expr_semantic_types,
        expr_target_types=arts.expr_target_types,
    )
    assert not [d for d in result.diagnostics if d.severity == "error"], (
        f"compile errors: {[d.description for d in result.diagnostics if d.severity == 'error']}"
    )
    exec_result = execute(result, fn_name=None, args=None)
    assert exec_result.value is not None
    return exec_result.value


# p5a: `Some(None) == @Option<Option<T>>.result` (ctor operand on the LEFT).
# main matches nested `Some(None)`: outer Some -> inner None -> sentinel 55.
_P5A = """
private forall<T> fn f(@Unit -> @Option<Option<T>>)
  requires(true)
  ensures(Some(None) == @Option<Option<T>>.result)
  effects(pure)
{
  Some(None)
}

public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  match f(()) { Some(@Option<Int>) -> match @Option<Int>.0 { Some(@Int) -> 1, None -> 55 }, None -> 2 }
}
"""

# p5b: `@Option<Option<T>>.result == Some(None)` (ctor operand on the RIGHT).
_P5B = """
private forall<T> fn f(@Unit -> @Option<Option<T>>)
  requires(true)
  ensures(@Option<Option<T>>.result == Some(None))
  effects(pure)
{
  Some(None)
}

public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  match f(()) { Some(@Option<Int>) -> match @Option<Int>.0 { Some(@Int) -> 1, None -> 55 }, None -> 2 }
}
"""

# The `!=` sibling: `Some(None) != None` under forall (finding-1 shape whose
# ensures ALSO lowers to a runtime `!=`).  main reaches the inner None -> 55.
_NEQ_FORALL = """
private forall<T> fn f(@Unit -> @Option<Option<T>>)
  requires(true)
  ensures(@Option<Option<T>>.result != None)
  effects(pure)
{
  Some(None)
}

public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  match f(()) { Some(@Option<Int>) -> match @Option<Int>.0 { Some(@Int) -> 1, None -> 55 }, None -> 2 }
}
"""

# `Some(None)` in the ==-body of a forall combinator (z_body_some_none_eq):
# `Some(None) == @Option<Option<T>>.0`, main drives it to the `false` branch
# (the parameter is Some(Some(0)), not Some(None)).
_BODY_EQ = """
private forall<T> fn cmp(@Option<Option<T>> -> @Bool)
  requires(true)
  ensures(true)
  effects(pure)
{
  Some(None) == @Option<Option<T>>.0
}

public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  if cmp(Some(Some(0))) then { 1 } else { 77 }
}
"""


def test_p5a_ctor_operand_left_compiles_and_runs() -> None:
    assert _check_compile_run(_P5A) == 55


def test_p5b_ctor_operand_right_compiles_and_runs() -> None:
    assert _check_compile_run(_P5B) == 55


def test_neq_none_forall_compiles_and_runs() -> None:
    assert _check_compile_run(_NEQ_FORALL) == 55


def test_body_nested_none_eq_compiles_and_runs() -> None:
    # `Some(None) == Some(Some(0))` is FALSE structurally, so cmp returns false
    # -> the else sentinel 77.  A wrong scalar (pointer) lowering on the
    # reachable clone would compare two distinct heap pointers and could give
    # either branch — pinning the value guards that.
    assert _check_compile_run(_BODY_EQ) == 77


_BODY_EQ_TRUE = """
private forall<T> fn cmp(@Option<Option<T>> -> @Bool)
  requires(true)
  ensures(true)
  effects(pure)
{
  Some(None) == @Option<Option<T>>.0
}

public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  if cmp(Some(None)) then { 55 } else { 1 }
}
"""


def test_body_nested_none_eq_true_branch_distinguishes_pointer_identity() -> None:
    # Two SEPARATELY constructed `Some(None)` values are structurally EQUAL,
    # so cmp returns true -> 55.  This is the case a pointer-identity lowering
    # CANNOT satisfy: the operands live at distinct heap addresses, so an
    # identity compare returns false (-> 1).  The false-branch sibling test
    # above cannot distinguish that lowering (structurally-unequal values are
    # also pointer-unequal); this one pins structural equality specifically.
    assert _check_compile_run(_BODY_EQ_TRUE) == 55


# ---------------------------------------------------------------------------
# Controls that must KEEP compiling+running (no regression from the fix).
# ---------------------------------------------------------------------------

# Concrete (non-generic) nested `==` — the operand is already fully resolved.
_CONCRETE_NONE = """
private fn f(@Unit -> @Option<Option<Int>>)
  requires(true)
  ensures(@Option<Option<Int>>.result == Some(None))
  effects(pure)
{
  Some(None)
}

public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  match f(()) { Some(@Option<Int>) -> match @Option<Int>.0 { Some(@Int) -> 1, None -> 55 }, None -> 2 }
}
"""

# Payload-carrying nested `==` under forall — the @T.0 payload already fixes
# the type argument, so this compiled before the fix and must stay structural.
_PAYLOAD_CARRYING = """
private forall<T> fn f(@T -> @Option<Option<T>>)
  requires(true)
  ensures(@Option<Option<T>>.result == Some(Some(@T.0)))
  effects(pure)
{
  Some(Some(@T.0))
}

public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  match f(9) { Some(@Option<Int>) -> match @Option<Int>.0 { Some(@Int) -> @Int.0, None -> 0 }, None -> 0 }
}
"""


def test_concrete_nested_none_still_runs() -> None:
    assert _check_compile_run(_CONCRETE_NONE) == 55


def test_payload_carrying_nested_still_runs() -> None:
    assert _check_compile_run(_PAYLOAD_CARRYING) == 9
