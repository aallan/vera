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

from tests.verifier_helpers import _verify
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


# PR #1013 review: the Pass-0.5 rewrite must be SHADOW-AWARE when it descends
# into a RETAINED generic subtree.  A generic helper's body call to a name its
# OWN nested helper defines — which ALSO exists as a non-generic ancestor
# helper — must stay bare (the mono path redirects it per-clone to the clone's
# own helper), not be captured onto the ancestor's hoisted name.

# `gen`'s body calls `shared(5)`; gen's OWN nested `shared` is +20, the
# ancestor's is +10.  Correct p(0) = shared(0) + gen(0) = 10 + 25 = 35 (base
# 1fd4043 returns 35); the capture bug bound gen's call to the ancestor's
# shared and returned 25 silently — check-green, verify-green, exit 0.
_GENERIC_HELPER_OWN_SHADOW = """\
public fn p(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  shared(@Int.0) + gen(@Int.0)
} where {
  fn shared(@Int -> @Int)
    requires(true) ensures(true) effects(pure)
  {
    @Int.0 + 10
  }
  forall<T> fn gen(@Int -> @Int)
    requires(true) ensures(true) effects(pure)
  {
    shared(5)
  } where {
    fn shared(@Int -> @Int)
      requires(true) ensures(true) effects(pure)
    {
      @Int.0 + 20
    }
  }
}
"""

# The FALSE-TIER-1 differential: same shape with pinning contracts.  The
# verifier's scoped lookup resolves gen's `shared(5)` to gen's OWN shared
# (5 + 20 == 25) and proves `ensures(@Int.result == 25)` Tier-1 — while the
# captured codegen ran the ancestor's shared (15) and TRAPPED on the runtime
# postcondition check.  Verifier↔codegen agreement is pinned by asserting BOTH
# the verify verdict AND the run value.
_GENERIC_HELPER_OWN_SHADOW_ENSURES = """\
public fn p(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  shared(@Int.0) + gen(@Int.0)
} where {
  fn shared(@Int -> @Int)
    requires(true) ensures(@Int.result == @Int.0 + 10) effects(pure)
  {
    @Int.0 + 10
  }
  forall<T> fn gen(@Int -> @Int)
    requires(true) ensures(@Int.result == 25) effects(pure)
  {
    shared(5)
  } where {
    fn shared(@Int -> @Int)
      requires(true) ensures(@Int.result == @Int.0 + 20) effects(pure)
    {
      @Int.0 + 20
    }
  }
}
"""

# NO-REGRESSION GUARD: a generic helper legitimately calling an ancestor
# helper it does NOT shadow — that call MUST still be redirected to the
# hoisted mangled name.  q(0) = aunt(0) + gen(0) = 7 + 107 = 114.
_GENERIC_LEGIT_ANCESTOR_CALL = """\
public fn q(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  aunt(@Int.0) + gen(@Int.0)
} where {
  fn aunt(@Int -> @Int)
    requires(true) ensures(true) effects(pure)
  {
    @Int.0 + 7
  }
  forall<T> fn gen(@Int -> @Int)
    requires(true) ensures(true) effects(pure)
  {
    aunt(@Int.0) + 100
  }
}
"""

# The generic-CHILD-shadows-ancestor variant: `child`'s nested GENERIC `foo`
# shadows the ancestor's non-generic `foo` for child's body, so `foo(5)` must
# stay bare and route through mono to the clone (+20): r(0) == 25 (the
# checker's last-wins resolution agrees).  At base this shape was a LOUD
# #991-family `duplicate func identifier` crash; a shadow map built from
# non-generic names only silently captured the call onto the ancestor's foo
# (15) — a loud failure downgraded to a silent wrong value.
_GENERIC_CHILD_SHADOWS_ANCESTOR = """\
public fn r(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  child(@Int.0)
} where {
  fn foo(@Int -> @Int)
    requires(true) ensures(true) effects(pure)
  {
    @Int.0 + 10
  }
  fn child(@Int -> @Int)
    requires(true) ensures(true) effects(pure)
  {
    foo(5)
  } where {
    forall<T> fn foo(@Int -> @Int)
      requires(true) ensures(true) effects(pure)
    {
      @Int.0 + 20
    }
  }
}
"""


# PR #1013 round 3 (CodeRabbit outside-diff): the CHECKER leg of #991.  The
# checker resolved bare calls through the flat, last-wins `env.functions`, so
# a diamond whose two same-named `leaf`s differ in SIGNATURE was falsely
# REJECTED: branchA's `leaf(@Int.0)` synthesized against branchB's
# `@Int -> @String` leaf (registered last) and E121'd branchA's body ("has
# type String, expected Int") on a valid program.  compute(1) =
# branchA(1) + branchB(1) = (1 + 1) + string_length("ab") = 4 — a value only
# reachable when ALL THREE subsystems (checker, verifier, codegen) resolve
# each `leaf` to its own parent's helper.
_SIBLING_LEAF_DIFFERENT_SIGNATURES = """\
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
      @Int.0 + 1
    }
  }
  fn branchB(@Int -> @Int)
    requires(true) ensures(true) effects(pure)
  {
    string_length(leaf(@Int.0))
  } where {
    fn leaf(@Int -> @String)
      requires(true) ensures(true) effects(pure)
    {
      "ab"
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


class TestGenericSubtreeShadowing1013:
    """PR #1013 review: the ancestor-scope rewrite must honour a retained
    generic subtree's OWN shadowing.

    The blunt full-subtree `_rewrite_call_names(stripped, combined)` descended
    into retained generic helpers' bodies and rewrote bare calls against the
    ancestor scope without re-applying the subtree's inner shadowing — so a
    generic helper's call to its OWN nested `shared` was captured onto the
    ancestor's `p$where$shared`.  Mono then cloned the generic with the call
    already rewritten, so `_hoist_clone_where_fns` never redirected it to the
    clone's own helper: a silent wrong value, and — with contracts — a false
    Tier-1 (the verifier's scoped lookup resolves the call correctly while the
    compiled program runs the ancestor's body and traps on the runtime
    postcondition check).
    """

    def test_generic_helper_own_shadow_runs_own_body(self) -> None:
        # SILENT WRONG VALUE: base 1fd4043 returns 35; the capture bug
        # returned 25 (gen's `shared(5)` bound to the ancestor's +10 body).
        assert _run(_GENERIC_HELPER_OWN_SHADOW, "p", [0]) == 35

    def test_generic_helper_own_shadow_verify_run_agree(self) -> None:
        # FALSE TIER-1 differential: verify must prove gen's
        # `ensures(@Int.result == 25)` statically (no E500, every ensures
        # obligation Tier-1 verified) AND the compiled program must run to 35
        # with gen returning 25 from its OWN shared — the capture bug passed
        # verify identically but TRAPPED at runtime on gen's postcondition.
        result = _verify(_GENERIC_HELPER_OWN_SHADOW_ENSURES)
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert errors == [], (
            f"verify must be clean: {[e.description for e in errors]}"
        )
        ensures = [o for o in result.obligations if o.kind == "ensures"]
        assert ensures and all(o.status == "verified" for o in ensures), (
            f"every ensures must be Tier-1 verified, got "
            f"{[(o.fn_name, o.expr_text, o.status) for o in ensures]}"
        )
        assert _run(_GENERIC_HELPER_OWN_SHADOW_ENSURES, "p", [0]) == 35

    def test_generic_helper_unshadowed_ancestor_call_still_redirected(
        self,
    ) -> None:
        # NO-REGRESSION GUARD: a generic helper calling an ancestor helper it
        # does NOT shadow must keep resolving to the hoisted mangled name.
        assert _run(_GENERIC_LEGIT_ANCESTOR_CALL, "q", [0]) == 114

    def test_generic_child_shadows_ancestor_name(self) -> None:
        # A GENERIC helper's name must also shadow an ancestor's non-generic
        # entry for its level's subtree: child's `foo(5)` routes through mono
        # to child's own generic foo (+20), not the ancestor's +10 body.
        assert _run(_GENERIC_CHILD_SHADOWS_ANCESTOR, "r", [0]) == 25


class TestCheckerHelperScope991:
    """PR #1013 round 3: the CHECKER leg of #991's "checker, verifier, and
    codegen must agree on helper-name scoping".

    The checker resolved bare calls through the flat, last-wins
    ``env.functions`` registry, so a diamond whose two same-named `leaf`s
    differ in SIGNATURE was falsely rejected — branchA's `leaf(@Int.0)` call
    synthesized against branchB's `@Int -> @String` leaf (registered last),
    E121 "branchA body has type String, expected Int" on a valid program.
    The scoped lookup (`_lookup_function_scoped`) resolves the nearest
    same-named helper in the `_fn_scope_stack` (innermost-out), then the
    top-level function, then the flat registry — mirroring the verifier's
    `_scoped_fn_lookup` and codegen's parent-qualified hoist.
    """

    def test_diamond_different_signatures_checks_clean(self) -> None:
        # THE BUG: false E121 on branchA (its `leaf` call resolved against
        # branchB's String-returning leaf).  The valid program must check.
        program = parse_to_ast(_SIBLING_LEAF_DIFFERENT_SIGNATURES)
        diags, _arts = typecheck_with_artifacts(
            program, _SIBLING_LEAF_DIFFERENT_SIGNATURES,
        )
        errors = [d for d in diags if d.severity == "error"]
        assert errors == [], (
            f"check must be clean: {[e.description for e in errors]}"
        )

    def test_diamond_different_signatures_runs(self) -> None:
        # All three subsystems agree: compute(1) == (1 + 1) +
        # string_length("ab") == 4, each `leaf` call reaching its own
        # parent's helper end-to-end.
        assert _run(_SIBLING_LEAF_DIFFERENT_SIGNATURES, "compute", [1]) == 4
