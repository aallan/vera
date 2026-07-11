"""#991: duplicate ``where``-helper names crash WAT assembly on the non-generic
path (``duplicate func identifier``) — and pre-#978 a colliding grandchild was
silently dropped, binding its call to a same-named top-level function.

Root cause: non-generic helper WAT emission used the bare Vera name (``(func
$leaf``) and ``_fn_sigs`` registration was flat / last-wins, so two same-named
helpers in different parent trees — or a helper named like a top-level function
— collided in the single flat WAT namespace.  The generic path already solves
this by parent-qualified mangling (``$parent$Int$where$helper``); the fix gives
the non-generic path the same canonical treatment (``$parent$where$helper``).

The DESIGN call is mangling, not a checker rejection: spec §5 makes two
same-named helpers under different parents a semantically VALID program (helpers
"are always local to the parent function"), so the collision is codegen's flat
namespace leaking, not a user error.

Every assertion executes the compiled program and checks a RUN VALUE chosen so
that resolving a call to the WRONG same-named body yields a DIFFERENT number —
compile-success alone would not catch wrong-body resolution.
"""

from __future__ import annotations

import re

import wasmtime

from vera.checker import typecheck_with_artifacts
from vera.codegen import compile as codegen_compile
from vera.codegen import execute
from vera.parser import parse_to_ast


# Shape (a): two siblings each carry a nested helper named `leaf` with a
# DISTINCT body (100 vs 200).  The parent sums both branches, so the only value
# consistent with each `leaf` call resolving to ITS OWN sibling's body is
# 100 + 200 == 300 (last-wins collapse to one body would give 200 or 400).
_SIBLING_LEAF_COLLISION = """\
public fn compute(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  branchA(@Int.0) + branchB(@Int.0)
} where {
  fn branchA(@Int -> @Int)
    requires(true) ensures(true) effects(pure)
  {
    leaf(@Int.0)
  } where {
    fn leaf(@Int -> @Int)
      requires(true) ensures(true) effects(pure)
    {
      100
    }
  }
  fn branchB(@Int -> @Int)
    requires(true) ensures(true) effects(pure)
  {
    leaf(@Int.0)
  } where {
    fn leaf(@Int -> @Int)
      requires(true) ensures(true) effects(pure)
    {
      200
    }
  }
}
"""

# Shape (b): a nested helper named exactly like a top-level function.  The
# nested `helper` (result + 1) must win inside `driver`, and the top-level
# `helper` (result * 10) must stay independently callable.  driver(5) == 6
# proves the nested body ran; helper(5) == 50 proves the top-level body is
# still reachable under its bare export name.
_HELPER_SHADOWS_TOP_LEVEL = """\
public fn helper(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  @Int.0 * 10
}

public fn driver(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  outer(@Int.0)
} where {
  fn outer(@Int -> @Int)
    requires(true) ensures(true) effects(pure)
  {
    helper(@Int.0)
  } where {
    fn helper(@Int -> @Int)
      requires(true) ensures(true) effects(pure)
    {
      @Int.0 + 1
    }
  }
}
"""

# Shape (d): a nested helper calls an "aunt" — a helper in an ANCESTOR scope
# (a sibling of its parent), not its own child/sibling.  Full lexical
# resolution must redirect the call across scope levels: top → branchA →
# grandchild → aunt (top's own helper).  top(1) == aunt(1) == 8.
_AUNT_CALL = """\
public fn top(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  branchA(@Int.0)
} where {
  fn branchA(@Int -> @Int)
    requires(true) ensures(true) effects(pure)
  {
    grandchild(@Int.0)
  } where {
    fn grandchild(@Int -> @Int)
      requires(true) ensures(true) effects(pure)
    {
      aunt(@Int.0)
    }
  }
  fn aunt(@Int -> @Int)
    requires(true) ensures(true) effects(pure)
  {
    @Int.0 + 7
  }
}
"""

# Shape (e): an inner helper SHADOWS an outer same-named helper for its own
# subtree.  `outer_call` sees the outer `shared` (== 1); `mid`, which carries
# its OWN `shared` (== 2), must resolve its bare `shared` call to the inner one.
# s(0) == 1 + 2 == 3; a shadowing miss (both → outer) would give 2.
_INNER_SHADOWS_OUTER = """\
public fn s(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  outer_call(@Int.0) + mid(@Int.0)
} where {
  fn shared(@Int -> @Int)
    requires(true) ensures(true) effects(pure)
  {
    1
  }
  fn outer_call(@Int -> @Int)
    requires(true) ensures(true) effects(pure)
  {
    shared(@Int.0)
  }
  fn mid(@Int -> @Int)
    requires(true) ensures(true) effects(pure)
  {
    shared(@Int.0)
  } where {
    fn shared(@Int -> @Int)
      requires(true) ensures(true) effects(pure)
    {
      2
    }
  }
}
"""

# Shape (c): a non-generic collision COEXISTING with a nested generic helper —
# the generic helper (mono's job) must keep compiling while the non-generic
# `leaf` collision is mangled.  compute(0) == 100 + 200 + gid(0) == 300.
_COLLISION_WITH_NESTED_GENERIC = """\
public fn compute(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  branchA(@Int.0) + branchB(@Int.0)
} where {
  fn branchA(@Int -> @Int)
    requires(true) ensures(true) effects(pure)
  {
    leaf(@Int.0)
  } where {
    fn leaf(@Int -> @Int)
      requires(true) ensures(true) effects(pure)
    {
      100
    }
  }
  fn branchB(@Int -> @Int)
    requires(true) ensures(true) effects(pure)
  {
    leaf(@Int.0) + gid(@Int.0)
  } where {
    fn leaf(@Int -> @Int)
      requires(true) ensures(true) effects(pure)
    {
      200
    }
    forall<T> fn gid(@T -> @T)
      requires(true) ensures(@T.result == @T.0) effects(pure)
    {
      @T.0
    }
  }
}
"""


def _compile(source: str):
    program = parse_to_ast(source)
    diags, arts = typecheck_with_artifacts(program, source)
    errors = [d for d in diags if d.severity == "error"]
    assert not errors, f"typecheck errors: {[d.description for d in errors]}"
    return codegen_compile(
        program, source=source,
        expr_semantic_types=arts.expr_semantic_types,
        expr_target_types=arts.expr_target_types,
    )


def _run(source: str, fn: str, args: list[int]) -> int:
    result = _compile(source)
    errs = [d for d in result.diagnostics if d.severity == "error"]
    assert not errs, (
        f"codegen errors (the #991 duplicate-func / dangling shape): "
        f"{[d.description for d in errs]}"
    )
    try:
        return execute(result, fn_name=fn, args=args).value
    except (wasmtime.WasmtimeError, wasmtime.Trap, RuntimeError) as exc:
        raise AssertionError(f"{fn}() raised instead of running: {exc}") from exc


def _func_names(wat: str) -> list[str]:
    return re.findall(r"\(func \$([^\s)]+)", wat)


class TestWhereHelperNameCollision991:
    def test_sibling_leaf_collision_runs_each_own_body(self) -> None:
        # THE BUG (shape a): compile crashed with `duplicate func identifier
        # $leaf`.  300 proves each `leaf` call resolves to its OWN sibling body.
        assert _run(_SIBLING_LEAF_COLLISION, "compute", [0]) == 300

    def test_sibling_leaf_no_duplicate_and_mangled(self) -> None:
        result = _compile(_SIBLING_LEAF_COLLISION)
        names = _func_names(result.wat)
        assert not [
            d for d in result.diagnostics if d.severity == "error"
        ], "expected a clean compile"
        # No bare `$leaf` collision — both are parent-qualified and distinct.
        assert names.count("leaf") == 0, "bare $leaf must not be emitted"
        leaf_names = sorted(n for n in names if n.endswith("$where$leaf"))
        assert leaf_names == [
            "compute$where$branchA$where$leaf",
            "compute$where$branchB$where$leaf",
        ], f"expected two parent-qualified leaves, got {leaf_names}"
        # The exported top-level function keeps its bare name.
        assert "compute" in names

    def test_helper_shadows_top_level_both_reachable(self) -> None:
        # THE BUG (shape b): nested `helper` collided with the top-level
        # `helper`.  driver(5) == 6 (nested body) and helper(5) == 50
        # (top-level body) prove both are distinctly reachable.
        assert _run(_HELPER_SHADOWS_TOP_LEVEL, "driver", [5]) == 6
        assert _run(_HELPER_SHADOWS_TOP_LEVEL, "helper", [5]) == 50

    def test_helper_shadows_top_level_name_scheme(self) -> None:
        result = _compile(_HELPER_SHADOWS_TOP_LEVEL)
        names = _func_names(result.wat)
        # Top-level `helper` stays bare (export + execute lookup depend on it);
        # the nested one is parent-qualified.
        assert "helper" in names, "top-level helper must keep its bare name"
        assert "driver$where$outer$where$helper" in names, (
            f"nested helper must be parent-qualified, got "
            f"{[n for n in names if 'helper' in n]}"
        )

    def test_nested_helper_calls_ancestor_scope_aunt(self) -> None:
        # Full lexical resolution: a grandchild's bare call to an "aunt" (a
        # helper in an ancestor's `where` block, not its own child/sibling) is
        # redirected across scope levels.  Worked pre-fix under bare names;
        # parent-qualified mangling must preserve it (regression guard).
        assert _run(_AUNT_CALL, "top", [1]) == 8

    def test_inner_helper_shadows_outer_same_name(self) -> None:
        # An inner helper shadows an outer same-named one for its subtree:
        # `mid` resolves `shared` to its OWN nested helper (== 2), `outer_call`
        # to the outer one (== 1).  s(0) == 3 (a shadowing miss gives 2).
        assert _run(_INNER_SHADOWS_OUTER, "s", [0]) == 3

    def test_collision_coexists_with_nested_generic(self) -> None:
        # Shape (c): the non-generic `leaf` collision is mangled while the
        # nested generic `gid` still monomorphizes (mono's job, untouched).
        assert _run(_COLLISION_WITH_NESTED_GENERIC, "compute", [0]) == 300
        result = _compile(_COLLISION_WITH_NESTED_GENERIC)
        names = _func_names(result.wat)
        assert "gid$Int" in names, (
            f"the nested generic clone must still be emitted, got "
            f"{[n for n in names if 'gid' in n]}"
        )
