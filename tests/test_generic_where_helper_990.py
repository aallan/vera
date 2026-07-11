"""#990: a ``forall<T>`` where-helper under a NON-generic parent never gets
monomorphized — check and verify are green, but compile emits a dangling call.

Mechanism: ``_monomorphize`` builds its ``generic_decls`` from top-level
``program.declarations`` only (``vera/codegen/monomorphize.py``), so a generic
helper nested in a non-generic parent's ``where`` block is invisible to
instantiation discovery: no clone is emitted, and the parent's concrete call
lowers to the unmangled ``$gid``, which fails WAT assembly (``unknown func``,
surfaced as an error diagnostic from ``compile``).  The checker accepts the
program and the verifier merely downgrades the uninstantiated generic, so the
failure is codegen-only.

The generic-under-GENERIC-parent shape is NOT this bug: those helpers are
carried into each parent clone and hoisted per-instantiation by
``_hoist_clone_where_fns`` (#904).  The control below pins that path — and
specifically that nested discovery does not double-emit a helper that the
hoisting path already clones.
"""

from __future__ import annotations

import re

import wasmtime

from vera.checker import typecheck_with_artifacts
from vera.codegen import compile as codegen_compile
from vera.codegen import execute
from vera.parser import parse_to_ast

# The issue's repro: non-generic parent, generic where-helper, one concrete
# instantiation (T=Int) reached from the parent body.
_NESTED_GENERIC = """\
private fn parent(@Int -> @Int)
  requires(true) ensures(@Int.result == @Int.0 + 5) effects(pure)
{ gid(@Int.0) + 5 }
where {
  forall<T> fn gid(@T -> @T)
    requires(true) ensures(@T.result == @T.0) effects(pure)
  { @T.0 }
}
public fn main(@Unit -> @Int)
  requires(true) ensures(@Int.result == 15) effects(pure)
{ parent(10) }
"""

# One level deeper: the generic helper hangs off a PLAIN where-child of the
# non-generic parent (the whole ancestor chain is non-generic).
_NESTED_GENERIC_GRANDCHILD = """\
private fn parent(@Int -> @Int)
  requires(true) ensures(@Int.result == @Int.0 + 5) effects(pure)
{ child(@Int.0) }
where {
  fn child(@Int -> @Int)
    requires(true) ensures(@Int.result == @Int.0 + 5) effects(pure)
  { gid(@Int.0) + 5 }
  where {
    forall<T> fn gid(@T -> @T)
      requires(true) ensures(@T.result == @T.0) effects(pure)
    { @T.0 }
  }
}
public fn main(@Unit -> @Int)
  requires(true) ensures(@Int.result == 15) effects(pure)
{ parent(10) }
"""

# Two distinct instantiations of the same nested helper (T=Int via the sum,
# T=Bool via the branch condition) — both clones must be emitted.
_TWO_INSTANTIATIONS = """\
private fn parent(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ if gid(true) then { gid(@Int.0) + 5 } else { 0 } }
where {
  forall<T> fn gid(@T -> @T)
    requires(true) ensures(@T.result == @T.0) effects(pure)
  { @T.0 }
}
public fn main(@Unit -> @Int)
  requires(true) ensures(@Int.result == 15) effects(pure)
{ parent(10) }
"""

# CONTROL (#904 path, green before and after): a T-dependent PLAIN helper
# under a GENERIC parent is carried into each parent clone and hoisted as
# ``parent$Int$where$helper`` — nested discovery must NOT also emit it
# standalone (double emission).
_GENERIC_PARENT_CONTROL = """\
private forall<T> fn wrap(@T -> @T)
  requires(true) ensures(true) effects(pure)
{ helper(@T.0) }
where {
  fn helper(@T -> @T)
    requires(true) ensures(@T.result == @T.0) effects(pure)
  { @T.0 }
}
public fn main(@Unit -> @Int)
  requires(true) ensures(@Int.result == 10) effects(pure)
{ wrap(10) }
"""


def _compile(source: str):
    program = parse_to_ast(source)
    diags, arts = typecheck_with_artifacts(program, source)
    errors = [d for d in diags if d.severity == "error"]
    assert not errors, f"typecheck errors: {[d.description for d in errors]}"
    result = codegen_compile(
        program, source=source,
        expr_semantic_types=arts.expr_semantic_types,
        expr_target_types=arts.expr_target_types,
    )
    return result


def _run_main(result) -> int:
    return execute(result, fn_name="main").value


def _assert_compiles_and_runs(source: str, expected: int) -> None:
    result = _compile(source)
    errs = [d for d in result.diagnostics if d.severity == "error"]
    assert not errs, (
        f"codegen errors (the #990 dangling-clone shape): "
        f"{[d.description for d in errs]}"
    )
    try:
        value = _run_main(result)
    except (wasmtime.WasmtimeError, wasmtime.Trap, RuntimeError) as exc:
        raise AssertionError(f"main() raised instead of running: {exc}") from exc
    assert value == expected


def _func_names(wat: str) -> list[str]:
    return re.findall(r"\(func \$([^\s)]+)", wat)


class TestNestedGenericWhereHelper990:
    def test_generic_helper_under_nongeneric_parent_runs(self) -> None:
        # THE BUG: check green, compile drops the clone, `call $gid` dangles.
        _assert_compiles_and_runs(_NESTED_GENERIC, 15)

    def test_clone_emitted_exactly_once(self) -> None:
        # The T=Int clone exists exactly once, and the uncompilable @T
        # template is not emitted at all.
        result = _compile(_NESTED_GENERIC)
        names = _func_names(result.wat)
        clones = [n for n in names if n.startswith("gid$")]
        assert clones == ["gid$Int"], f"expected one gid$Int clone, got {clones}"
        assert "gid" not in names, "the @T template must not be emitted"

    def test_generic_grandchild_under_plain_child_runs(self) -> None:
        # The issue's one-level-deeper variant: every ancestor is non-generic.
        _assert_compiles_and_runs(_NESTED_GENERIC_GRANDCHILD, 15)

    def test_two_instantiations_both_emitted(self) -> None:
        _assert_compiles_and_runs(_TWO_INSTANTIATIONS, 15)
        result = _compile(_TWO_INSTANTIATIONS)
        names = _func_names(result.wat)
        clones = sorted(n for n in names if n.startswith("gid$"))
        assert clones == ["gid$Bool", "gid$Int"], (
            f"expected both instantiation clones, got {clones}"
        )

    def test_nested_generic_with_own_where_child_runs(self) -> None:
        # The nested generic carries its OWN where-child: the child is emitted
        # per-clone by the hoisting path (`gid$Int$where$dbl`), and the Pass-2
        # where-fn sweep must NOT also emit it standalone (it stops at the
        # generic template).
        # Two children under the generic helper: a T-DEPENDENT one (only
        # compilable inside a clone) and a T-INDEPENDENT one (would compile
        # standalone, so a Pass-2 sweep that wrongly descends the generic's
        # subtree emits a dead bare copy — the observable this test pins).
        source = """\
private fn parent(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ gid(@Int.0) + 5 }
where {
  forall<T> fn gid(@T -> @T)
    requires(true) ensures(@T.result == @T.0) effects(pure)
  { bump(0); pass_through(@T.0) }
  where {
    fn pass_through(@T -> @T)
      requires(true) ensures(@T.result == @T.0) effects(pure)
    { @T.0 }
    fn bump(@Int -> @Int)
      requires(true) ensures(@Int.result == @Int.0 + 1) effects(pure)
    { @Int.0 + 1 }
  }
}
public fn main(@Unit -> @Int)
  requires(true) ensures(@Int.result == 15) effects(pure)
{ parent(10) }
"""
        _assert_compiles_and_runs(source, 15)
        result = _compile(source)
        names = _func_names(result.wat)
        hoisted = sorted(n for n in names if "$where$" in n)
        assert hoisted == [
            "gid$Int$where$bump", "gid$Int$where$pass_through",
        ], f"expected exactly the per-clone hoisted children, got {hoisted}"
        for bare in ("pass_through", "bump"):
            assert bare not in names, (
                f"the generic's child '{bare}' must not ALSO be emitted "
                f"standalone by the Pass-2 where-fn sweep (dead duplicate)"
            )

    def test_helper_under_generic_parent_hoisting_unchanged(self) -> None:
        # CONTROL (#904): the helper is cloned INTO the parent instantiation
        # (`wrap$Int$where$helper`), and nested discovery must not emit a
        # second standalone copy of it.
        result = _compile(_GENERIC_PARENT_CONTROL)
        errs = [d for d in result.diagnostics if d.severity == "error"]
        assert not errs, f"codegen errors: {[d.description for d in errs]}"
        assert _run_main(result) == 10
        names = _func_names(result.wat)
        hoisted = [n for n in names if "where" in n and "helper" in n]
        assert len(hoisted) == 1, (
            f"expected exactly one hoisted helper clone, got {hoisted}"
        )
        assert "helper" not in names, (
            "the helper must not ALSO be emitted under its bare name"
        )
