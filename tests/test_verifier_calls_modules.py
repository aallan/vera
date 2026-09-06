"""Tests for vera.verifier — calls_modules (call-site preconditions, pipe operator, cross-module contracts).

Split from tests/test_verifier.py (#839). Shared helpers live in tests/verifier_helpers.py.
"""
from __future__ import annotations

from pathlib import Path

import pytest

from vera.codegen import execute
from vera.obligations.core import ProofObligation
from vera.parser import parse_to_ast
from vera.checker import typecheck
from vera.resolver import ResolvedModule
from vera.runtime.traps import WasmTrapError
from vera.verifier import VerifyResult, verify

from tests.codegen_helpers import _compile_ok, _run
from tests.verifier_helpers import (
    _verify,
    _verify_err,
    _verify_ok,
    _verify_warn,
)


# =====================================================================
# Call-site precondition verification (C6b)
# =====================================================================

class TestCallSiteVerification:
    """Modular verification: callee preconditions checked at call sites."""

    def test_call_satisfied_precondition(self) -> None:
        """Calling with a literal that satisfies requires(@Int.0 != 0)."""
        _verify_ok("""
private fn non_zero(@Int -> @Int)
  requires(@Int.0 != 0)
  ensures(true)
  effects(pure)
{ @Int.0 }

private fn caller(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ non_zero(1) }
""")

    def test_call_violated_precondition(self) -> None:
        """Calling with literal 0 violates requires(@Int.0 != 0)."""
        _verify_err("""
private fn non_zero(@Int -> @Int)
  requires(@Int.0 != 0)
  ensures(true)
  effects(pure)
{ @Int.0 }

private fn bad_caller(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ non_zero(0) }
""", "precondition")

    def test_call_precondition_forwarded(self) -> None:
        """Caller's precondition implies callee's — passes."""
        _verify_ok("""
private fn non_zero(@Int -> @Int)
  requires(@Int.0 != 0)
  ensures(true)
  effects(pure)
{ @Int.0 }

private fn safe_caller(@Int -> @Int)
  requires(@Int.0 != 0)
  ensures(true)
  effects(pure)
{ non_zero(@Int.0) }
""")

    # ---- #730: preconditions for calls in STATEMENT position ----
    # A call whose result is discarded (a bare `f(x);` statement) must still be
    # checked against its requires(...) — DESIGN.md: contracts are checked "at
    # every call site".  Before #730 the SMT body translation skipped ExprStmt.

    def test_call_violated_precondition_stmt_position(self) -> None:
        """#730 (headline): a statement-position call (result discarded) whose
        precondition is violated must fire E501 — the gap this fix closes."""
        _verify_err("""
private fn non_zero(@Int -> @Int)
  requires(@Int.0 != 0)
  ensures(true)
  effects(pure)
{ @Int.0 }

private fn bad_caller(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ non_zero(0); 1 }
""", "precondition")

    def test_call_satisfied_precondition_stmt_position(self) -> None:
        """#730 guard: a satisfied precondition in statement position must NOT
        fire a spurious E501 (the fix must not over-fire)."""
        _verify_ok("""
private fn non_zero(@Int -> @Int)
  requires(@Int.0 != 0)
  ensures(true)
  effects(pure)
{ @Int.0 }

private fn ok_caller(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ non_zero(1); 1 }
""")

    def test_call_violated_precondition_stmt_position_in_if_branch(self) -> None:
        """#730: a statement-position call inside an if-branch block (routed via
        _translate_if -> _translate_block) is precondition-checked."""
        _verify_err("""
private fn non_zero(@Int -> @Int)
  requires(@Int.0 != 0)
  ensures(true)
  effects(pure)
{ @Int.0 }

private fn caller(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ if @Int.0 > 5 then { non_zero(0); @Int.0 } else { @Int.0 } }
""", "precondition")

    def test_call_violated_precondition_stmt_position_in_match_arm(self) -> None:
        """#730: a statement-position call inside a match-arm block (routed via
        _translate_match -> _translate_block) is precondition-checked."""
        _verify_err("""
private fn non_zero(@Int -> @Int)
  requires(@Int.0 != 0)
  ensures(true)
  effects(pure)
{ @Int.0 }

public data Flag {
  On,
  Off
}

private fn caller(@Flag -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ match @Flag.0 { On -> { non_zero(0); 1 }, Off -> 2 } }
""", "precondition")

    def test_call_stmt_position_sees_preceding_let(self) -> None:
        """#730: a statement-position call sees preceding let bindings — the env
        is threaded through ExprStmt translation (here @Int.0 == 0 violates)."""
        _verify_err("""
private fn non_zero(@Int -> @Int)
  requires(@Int.0 != 0)
  ensures(true)
  effects(pure)
{ @Int.0 }

private fn caller(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ let @Int = 0; non_zero(@Int.0); 1 }
""", "precondition")

    def test_call_stmt_position_no_double_count(self) -> None:
        """#730: a single statement-position violating call yields EXACTLY ONE
        call_pre E501 obligation — not zero (the bug pre-fix), not accidentally
        more.  In statement position the call is translated once, so this is a
        precise-count guard; the span-keyed #727 dedup's no-OVER-collapse
        property is pinned separately by
        test_two_distinct_stmt_position_violations_each_fire."""
        result = _verify("""
private fn non_zero(@Int -> @Int)
  requires(@Int.0 != 0)
  ensures(true)
  effects(pure)
{ @Int.0 }

private fn caller(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ non_zero(0); 1 }
""")
        e501 = [o for o in result.obligations
                if o.kind == "call_pre" and o.error_code == "E501"]
        assert len(e501) == 1, (
            f"expected exactly one call_pre E501 obligation, got {len(e501)}: "
            f"{[(o.line, o.column) for o in e501]}"
        )

    def test_call_stmt_position_effect_op_degrades(self) -> None:
        """#730 guard: an untranslatable statement (an effect op) is ignored, not
        crashed on, and does not abort verification of the rest of the block."""
        _verify_ok("""
private fn logged(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(<IO>)
{ IO.print("hi"); @Int.0 }
""")

    def test_call_violated_precondition_after_untranslatable_stmt(self) -> None:
        """#730 soundness: an untranslatable statement (an effect op) preceding a
        decidable violating call must NOT abort the block — the later call is
        still precondition-checked.  Guards the `_translate_block` invariant that
        a None-returning ExprStmt is IGNORED, not propagated as a block bail: the
        abort-on-None wrong-fix passes every other statement-position test yet
        silently drops this E501 (PR #777 review)."""
        _verify_err("""
private fn non_zero(@Int -> @Int)
  requires(@Int.0 != 0)
  ensures(true)
  effects(pure)
{ @Int.0 }

private fn caller(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(<IO>)
{ IO.print("side"); non_zero(0); @Int.0 }
""", "precondition")

    def test_two_distinct_stmt_position_violations_each_fire(self) -> None:
        """Two distinct statement-position violating calls produce TWO E501
        obligations — the span-keyed #727 dedup collapses a re-translated SAME
        site to one, but must NOT over-collapse genuinely-different sites
        (PR #777 review)."""
        result = _verify("""
private fn non_zero(@Int -> @Int)
  requires(@Int.0 != 0)
  ensures(true)
  effects(pure)
{ @Int.0 }

private fn caller(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ non_zero(0); non_zero(0); 1 }
""")
        e501 = [o for o in result.obligations
                if o.kind == "call_pre" and o.error_code == "E501"]
        assert len(e501) == 2, (
            f"two distinct statement-position violations must each fire, got "
            f"{len(e501)}: {[(o.line, o.column) for o in e501]}"
        )

    def test_call_violated_precondition_nested_in_stmt_expr(self) -> None:
        """A violating call buried inside a larger statement-position expression
        (`non_zero(0) + 5;`) is precondition-checked — the ExprStmt translation
        recurses into sub-expressions, not just the outermost node (PR #777
        review)."""
        _verify_err("""
private fn non_zero(@Int -> @Int)
  requires(@Int.0 != 0)
  ensures(true)
  effects(pure)
{ @Int.0 }

private fn caller(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ non_zero(0) + 5; 1 }
""", "precondition")

    def test_decreases_resolves_via_stmt_position_recursive_call(self) -> None:
        """A recursive call in STATEMENT position (result discarded) is seen by
        the termination walker, so `decreases` still resolves to Tier-1 — the
        third statement-iterating walker (`_walk_for_calls`) recurses into
        ExprStmt (the branch that was the last `# pragma: no cover`).  Without it
        the recursive call is invisible and `decreases` silently degrades to
        Tier-3 (PR #777 review)."""
        result = _verify("""
private fn countdown(@Nat -> @Nat)
  requires(true)
  ensures(true)
  decreases(@Nat.0)
  effects(pure)
{ if @Nat.0 == 0 then { 0 } else { countdown(@Nat.0 - 1); 0 } }
""")
        decr = [o for o in result.obligations
                if o.fn_name == "countdown" and o.kind == "decreases"]
        assert len(decr) == 1 and decr[0].status == "verified", (
            "decreases must resolve to Tier-1 via the statement-position "
            f"recursive call; got {[(o.kind, o.status) for o in decr]}"
        )
        assert [d for d in result.diagnostics if d.severity == "error"] == []

    def test_call_postcondition_assumed(self) -> None:
        """Caller's ensures relies on callee's postcondition."""
        _verify_ok("""
private fn succ(@Int -> @Int)
  requires(true)
  ensures(@Int.result == @Int.0 + 1)
  effects(pure)
{ @Int.0 + 1 }

private fn add_two(@Int -> @Int)
  requires(true)
  ensures(@Int.result == @Int.0 + 2)
  effects(pure)
{ succ(succ(@Int.0)) }
""")

    def test_recursive_call_uses_postcondition(self) -> None:
        """Recursive factorial: ensures(@Nat.result >= 1) now Tier 1.

        The postcondition is assumed at the recursive call site,
        and base case returns 1, so result >= 1 is provable.
        """
        result = _verify("""
private fn factorial(@Nat -> @Nat)
  requires(true)
  ensures(@Nat.result >= 1)
  decreases(@Nat.0)
  effects(pure)
{
  if @Nat.0 == 0 then { 1 }
  else { @Nat.0 * factorial(@Nat.0 - 1) }
}
""")
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert errors == [], f"Expected no errors, got: {[e.description for e in errors]}"
        # ensures now Tier 1 (modular verification), decreases still Tier 3
        assert result.summary.tier1_verified >= 2

    def test_call_trivial_precondition(self) -> None:
        """Callee with requires(true) — always satisfied."""
        _verify_ok("""
private fn id(@Int -> @Int)
  requires(true)
  ensures(@Int.result == @Int.0)
  effects(pure)
{ @Int.0 }

private fn caller(@Int -> @Int)
  requires(true)
  ensures(@Int.result == @Int.0)
  effects(pure)
{ id(@Int.0) }
""")

    def test_call_in_let_binding(self) -> None:
        """Call result used via let binding, passed to second call."""
        _verify_ok("""
private fn succ(@Int -> @Int)
  requires(true)
  ensures(@Int.result == @Int.0 + 1)
  effects(pure)
{ @Int.0 + 1 }

private fn add_two_let(@Int -> @Int)
  requires(true)
  ensures(@Int.result == @Int.0 + 2)
  effects(pure)
{
  let @Int = succ(@Int.0);
  succ(@Int.0)
}
""")

    def test_where_block_call(self) -> None:
        """Call to a where-block helper function."""
        _verify_ok("""
private fn outer(@Int -> @Int)
  requires(true)
  ensures(@Int.result == @Int.0 + 1)
  effects(pure)
{ helper(@Int.0) }
where {
  fn helper(@Int -> @Int)
    requires(true)
    ensures(@Int.result == @Int.0 + 1)
    effects(pure)
  { @Int.0 + 1 }
}
""")

    def test_generic_call_verified_per_instantiation(self) -> None:
        """#732: a generic instantiated by a caller is verified statically per
        monomorphization — Tier 1, not the old Tier-3 bail."""
        result = _verify("""
private forall<T>
fn id(@T -> @T)
  requires(true)
  ensures(@T.result == @T.0)
  effects(pure)
{ @T.0 }

private fn caller(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ id(@Int.0) }
""")
        # id<Int>'s ensures(@T.result == @T.0) holds for the body @T.0, so the
        # instantiated generic is now discharged statically with no Tier-3
        # fallback — the core #732 behavior change.
        assert result.summary.tier3_runtime == 0
        assert not result.diagnostics
        # Check id's OWN ensures is the verified obligation, not just the
        # summary counter (which a non-generic obligation could also bump).
        assert any(
            o.fn_name == "id" and o.kind == "ensures" and o.status == "verified"
            for o in result.obligations
        )

    def test_multiple_preconditions_all_checked(self) -> None:
        """Two requires on callee, second one violated."""
        _verify_err("""
private fn guarded(@Int -> @Int)
  requires(@Int.0 > 0)
  requires(@Int.0 < 100)
  ensures(true)
  effects(pure)
{ @Int.0 }

private fn bad_caller(@Int -> @Int)
  requires(@Int.0 > 0)
  ensures(true)
  effects(pure)
{ guarded(@Int.0) }
""", "precondition")

    def test_precondition_via_caller_requires(self) -> None:
        """Caller's requires forwards two constraints to satisfy callee."""
        _verify_ok("""
private fn guarded(@Int -> @Int)
  requires(@Int.0 > 0)
  requires(@Int.0 < 100)
  ensures(true)
  effects(pure)
{ @Int.0 }

private fn good_caller(@Int -> @Int)
  requires(@Int.0 > 0)
  requires(@Int.0 < 100)
  ensures(true)
  effects(pure)
{ guarded(@Int.0) }
""")

    def test_multiple_calls_in_sequence(self) -> None:
        """Two calls in sequence, each gets a fresh return variable."""
        _verify_ok("""
private fn inc(@Int -> @Int)
  requires(true)
  ensures(@Int.result == @Int.0 + 1)
  effects(pure)
{ @Int.0 + 1 }

private fn add_two_seq(@Int -> @Int)
  requires(true)
  ensures(@Int.result == @Int.0 + 2)
  effects(pure)
{
  let @Int = inc(@Int.0);
  inc(@Int.0)
}
""")

    def test_violation_error_mentions_callee_name(self) -> None:
        """Error message includes the callee function name."""
        errors = _verify_err("""
private fn non_zero(@Int -> @Int)
  requires(@Int.0 != 0)
  ensures(true)
  effects(pure)
{ @Int.0 }

private fn bad(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ non_zero(0) }
""", "precondition")
        # Check that the error mentions the callee name
        assert any("non_zero" in e.description for e in errors)

    # -- Branch-aware precondition checking (#283) -------------------------

    def test_call_precondition_satisfied_by_if_guard(self) -> None:
        """Call inside if-branch where branch condition implies precondition."""
        _verify_ok("""
private fn positive(@Int -> @Int)
  requires(@Int.0 > 0)
  ensures(true)
  effects(pure)
{ @Int.0 }

private fn caller(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  if @Int.0 > 0 then { positive(@Int.0) }
  else { 0 }
}
""")

    def test_call_precondition_with_else_guard(self) -> None:
        """Call inside else-branch where negated condition implies precondition."""
        _verify_ok("""
private fn non_negative(@Int -> @Int)
  requires(@Int.0 >= 0)
  ensures(true)
  effects(pure)
{ @Int.0 }

private fn caller(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  if @Int.0 < 0 then { 0 }
  else { non_negative(@Int.0) }
}
""")

    def test_recursive_call_guarded_by_if(self) -> None:
        """Recursive call guarded by if — the fizzbuzz pattern (#283).

        De Bruijn: @Nat.0 = counter (second param, most recent),
        @Nat.1 = limit (first param).  The recursive call passes
        limit first, counter+1 second: loop(@Nat.1, @Nat.0 + 1).
        """
        _verify_ok("""
private fn loop(@Nat, @Nat -> @Nat)
  requires(@Nat.0 <= @Nat.1)
  ensures(true)
  effects(pure)
{
  if @Nat.0 < @Nat.1 then {
    loop(@Nat.1, @Nat.0 + 1)
  } else { @Nat.0 }
}
""")

    def test_call_precondition_with_match_guard(self) -> None:
        """Call inside match arm with nested if-guard."""
        _verify_ok("""
private data Maybe {
  Nothing,
  Just(Int)
}

private fn use_positive(@Int -> @Int)
  requires(@Int.0 > 0)
  ensures(true)
  effects(pure)
{ @Int.0 }

private fn process(@Maybe -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match @Maybe.0 {
    Just(@Int) -> if @Int.0 > 0 then { use_positive(@Int.0) } else { 0 },
    Nothing -> 0
  }
}
""")

    def test_call_precondition_nested_if(self) -> None:
        """Nested if-branches compounding conditions."""
        _verify_ok("""
private fn bounded(@Int -> @Int)
  requires(@Int.0 > 0)
  requires(@Int.0 < 100)
  ensures(true)
  effects(pure)
{ @Int.0 }

private fn caller(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  if @Int.0 > 0 then {
    if @Int.0 < 100 then {
      bounded(@Int.0)
    } else { 0 }
  } else { 0 }
}
""")

    def test_call_precondition_violated_despite_branch(self) -> None:
        """Call violates precondition even inside an if-branch."""
        _verify_err("""
private fn positive(@Int -> @Int)
  requires(@Int.0 > 0)
  ensures(true)
  effects(pure)
{ @Int.0 }

private fn bad_caller(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  if @Int.0 > 10 then { positive(@Int.0) }
  else { positive(@Int.0) }
}
""", "precondition")


# =====================================================================
# #764: block translation continues through a let-destructure
# =====================================================================

class TestCallPreAfterDestructure:
    """#764: `_translate_block` models a `LetDestruct` — binding each
    component via the RHS datatype's accessors — instead of truncating the
    block, so a call precondition (E501) at or after the destructure is
    statically checked again.

    Before the fix the block translation returned ``None`` at the first
    ``LetDestruct``, so every statement from the destructure onward —
    including the block's final expression — was never seen by the E501
    check or the postcondition proof.  The callee's runtime ``requires``
    guard was the only backstop.

    A *satisfied* call precondition discharges silently — verified
    call-site checks are not enumerated in the obligation stream (Phase A,
    ``vera/obligations/core.py``) — so the clean side of the fix is pinned
    by the OK-half of ``test_destructure_component_debruijn_order``, whose
    violating twin proves the check actually runs.
    """

    def test_call_violated_precondition_after_destructure(self) -> None:
        """The issue's repro: an unconstrained destructured component fed to
        a ``requires(> 0)`` callee must fire E501 (it verified silently
        clean, Tier 1, before the fix)."""
        _verify_err("""
private fn needs_pos(@Int -> @Int)
  requires(@Int.0 > 0)
  ensures(true)
  effects(pure)
{ @Int.0 }

private fn mk(@Int -> @Tuple<Int, Int>)
  requires(true)
  ensures(true)
  effects(pure)
{ Tuple(@Int.0, 3) }

private fn caller(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let Tuple<@Int, @Int> = mk(@Int.0);
  needs_pos(@Int.1)
}
""", "precondition")

    def test_destructure_component_debruijn_order(self) -> None:
        """Components bind leftmost-first, so for ``Tuple(5, -3)`` the slot
        ``@Int.1`` is the FIRST component (5) and ``@Int.0`` the second
        (-3).  A reversed push order flips both outcomes; the values are
        distinct and non-coincident with any fallback."""
        _verify_ok("""
private fn needs_pos(@Int -> @Int)
  requires(@Int.0 > 0)
  ensures(true)
  effects(pure)
{ @Int.0 }

private fn caller(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let Tuple<@Int, @Int> = Tuple(5, -3);
  needs_pos(@Int.1)
}
""")
        _verify_err("""
private fn needs_pos(@Int -> @Int)
  requires(@Int.0 > 0)
  ensures(true)
  effects(pure)
{ @Int.0 }

private fn caller(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let Tuple<@Int, @Int> = Tuple(5, -3);
  needs_pos(@Int.0)
}
""", "precondition")

    def test_ensures_after_destructure_proves_tier1(self) -> None:
        """The block's final expression is translated again, so a
        postcondition over it proves at Tier 1 (pre-fix the truncated body
        demoted the ensures proof to the runtime tier).  The combination is
        SUBTRACTION, not addition, so the proof is order-sensitive: with
        components (5, 3), ``@Int.1 - @Int.0`` is first-minus-second = 2,
        and a reversed push order would prove -2 instead (CodeRabbit,
        PR #1200 round 5 — a commutative combiner masks the ordering)."""
        result = _verify("""
private fn summed(@Unit -> @Int)
  requires(true)
  ensures(@Int.result == 2)
  effects(pure)
{
  let Tuple<@Int, @Int> = Tuple(5, 3);
  @Int.1 - @Int.0
}
""")
        assert not result.diagnostics
        assert result.summary.tier3_runtime == 0, (
            f"expected a fully Tier-1 result, got "
            f"tier3_runtime={result.summary.tier3_runtime}"
        )
        ensures = [o for o in result.obligations if o.kind == "ensures"]
        assert ensures and all(o.status == "verified" for o in ensures)

    def test_stmt_position_call_after_destructure(self) -> None:
        """The #730 × #764 product case: a statement-position (discarded-
        result) violating call AFTER the destructure is still checked — the
        ExprStmt arm runs on the post-destructure env."""
        _verify_err("""
private fn non_zero(@Int -> @Int)
  requires(@Int.0 != 0)
  ensures(true)
  effects(pure)
{ @Int.0 }

private fn caller(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let Tuple<@Int, @Int> = Tuple(0, 7);
  non_zero(@Int.1);
  @Int.0
}
""", "precondition")

    def test_call_before_destructure_still_checked(self) -> None:
        """Regression guard for the pre-fix behaviour that DID work: a
        violating call before the destructure keeps firing E501."""
        _verify_err("""
private fn non_zero(@Int -> @Int)
  requires(@Int.0 != 0)
  ensures(true)
  effects(pure)
{ @Int.0 }

private fn caller(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  non_zero(0);
  let Tuple<@Int, @Int> = Tuple(1, 2);
  @Int.1
}
""", "precondition")


# =====================================================================
# #1199: block translation continues through an untranslatable let
# =====================================================================

class TestCallPreAfterOpaqueLet:
    """#1199 (folded into the #764 fix): a `let` whose value the SMT layer
    cannot translate — an effect-op result — no longer truncates the block.
    The slot binds to a fresh unconstrained constant of the value's
    recorded type and translation continues, so a later call's E501 is
    still checked.  Against an opaque value an unprovable precondition
    fires — the posture an opaque *function* result already had — and the
    repair is an `assert`/`assume`, whose fact the #804 threading carries
    into the check.  Opaque constants are span-keyed: distinct statements
    yield distinct constants (two effect results are never provably
    equal), while every translation pass over one statement sees the same
    term.
    """

    def test_call_violated_after_opaque_let(self) -> None:
        """An unconstrained effect-op value fed to `requires(> 0)` fires
        E501 (pre-fix the block truncated and this verified silently
        clean)."""
        _verify_err("""
private fn needs_pos(@Int -> @Int)
  requires(@Int.0 > 0)
  ensures(true)
  effects(pure)
{ @Int.0 }

private fn caller(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(<Random>)
{
  let @Int = Random.random_int(0, 9);
  needs_pos(@Int.0)
}
""", "precondition")

    def test_assert_repairs_opaque_let_call(self) -> None:
        """The documented repair: an `assert` on the opaque value threads
        its fact (#804) into the call check, so the precondition proves and
        no E501 fires.  Green pre-fix too (nothing was checked at all) —
        kept as the over-fire guard for the opaque path."""
        _verify_ok("""
private fn needs_pos(@Int -> @Int)
  requires(@Int.0 > 0)
  ensures(true)
  effects(pure)
{ @Int.0 }

private fn caller(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(<Random>)
{
  let @Int = Random.random_int(1, 9);
  assert(@Int.0 > 0);
  needs_pos(@Int.0)
}
""")

    def test_two_opaque_lets_are_distinct(self) -> None:
        """Two effect-op lets bind DISTINCT opaque constants — a
        `requires(@Int.0 == @Int.1)` callee cannot prove them equal, so
        E501 fires.  A shared-constant bug (same name for both) would prove
        the equality and silently drop this E501."""
        _verify_err("""
private fn same(@Int, @Int -> @Int)
  requires(@Int.0 == @Int.1)
  ensures(true)
  effects(pure)
{ @Int.0 }

private fn caller(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(<Random>)
{
  let @Int = Random.random_int(0, 9);
  let @Int = Random.random_int(0, 9);
  same(@Int.1, @Int.0)
}
""", "precondition")

    def test_ensures_after_opaque_let_proves(self) -> None:
        """A postcondition independent of the opaque value proves at
        Tier 1 (pre-fix the truncated body demoted it to E522)."""
        result = _verify("""
private fn seven(@Unit -> @Int)
  requires(true)
  ensures(@Int.result == 7)
  effects(<Random>)
{
  let @Int = Random.random_int(0, 9);
  7
}
""")
        assert not [d for d in result.diagnostics
                    if d.error_code == "E522"]
        ensures = [o for o in result.obligations if o.kind == "ensures"]
        assert ensures and all(o.status == "verified" for o in ensures)

    def test_ensures_depending_on_opaque_value_demotes_not_violates(
        self,
    ) -> None:
        """The taint gate: a postcondition that DEPENDS on the opaque value
        must demote to E522 Tier-3 — a countermodel over the unconstrained
        stand-in says nothing about the value the effect produces, so
        claiming E500 "postcondition violated" would be a false error (the
        corpus regression the gate was built for: eleven conformance
        programs and two examples flipped to false E500s without it).
        Removing the gate turns this E522 into an E500 error."""
        result = _verify("""
private fn passthrough(@Unit -> @Int)
  requires(true)
  ensures(@Int.result == 0)
  effects(<Random>)
{
  let @Int = Random.random_int(0, 9);
  @Int.0
}
""")
        assert not [d for d in result.diagnostics
                    if d.severity == "error"], (
            f"expected no errors, got "
            f"{[(d.error_code, d.description[:60]) for d in result.diagnostics]}"
        )
        e522 = [d for d in result.diagnostics if d.error_code == "E522"]
        assert len(e522) == 1
        ensures = [o for o in result.obligations if o.kind == "ensures"]
        assert ensures and ensures[0].status == "tier3"

    def test_nat_sub_over_opaque_values_is_tier3(self) -> None:
        """A `@Nat - @Nat` underflow obligation whose operands resolve to
        opaque effect values classifies as plain ``tier3`` — not
        ``timeout`` (the cause is opacity, not the solver), and not a
        violated E502 (the stand-ins refute nothing the effect produces).

        The operands are NESTED BLOCKS each returning an opaque-bound
        slot: the nat-sub walker translates a block operand through
        `_translate_block`, so it resolves to the opaque constant and
        `check_valid` returns "opaque", exercising the else-leg's opaque
        routing (verified by line coverage — a plain `let @Nat = ...;`
        operand leaves the walker's own env unresolved and never reaches
        the check; CodeRabbit, PR #1200 round 3).  The inner `@Int`→`@Nat`
        narrowings likewise classify guarded ``tier3``, covering the
        value-site `nat_bind` else-leg."""
        result = _verify("""
private fn f(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(<Random>)
{
  { let @Nat = Random.random_int(0, 9); @Nat.0 } - { let @Nat = Random.random_int(0, 9); @Nat.0 }
}
""")
        subs = [o for o in result.obligations if o.kind == "nat_sub"]
        assert subs and all(o.status == "tier3" for o in subs), [
            (o.kind, o.status) for o in result.obligations
        ]
        binds = [o for o in result.obligations if o.kind == "nat_bind"]
        assert binds and all(o.status == "tier3" for o in binds), [
            (o.kind, o.status) for o in result.obligations
        ]
        assert not [d for d in result.diagnostics
                    if d.error_code in ("E502", "E503")]

    def test_call_violated_after_opaque_destructure(self) -> None:
        """The destructure analogue: a tuple of effect-op results is
        unprojectable, so each component binds a fresh opaque constant and
        the later violating call still fires E501 (pre-fix: silent)."""
        _verify_err("""
private fn needs_pos(@Int -> @Int)
  requires(@Int.0 > 0)
  ensures(true)
  effects(pure)
{ @Int.0 }

private fn caller(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(<Random>)
{
  let Tuple<@Int, @Int> = Tuple(Random.random_int(0, 9), Random.random_int(0, 9));
  needs_pos(@Int.1)
}
""", "precondition")


# =====================================================================
# #882: call-site preconditions over ADT-typed arguments
# =====================================================================

class TestAdtCallSitePrecondition:
    """A callee `requires()` over ADT-typed parameters must generate a
    call-site precondition obligation, exactly like Int parameters (#882).

    Before the fix `_translate_call_with_info` bailed when a constructor-call
    argument's ADT sort had never been materialised in the caller context, so
    the obligation silently vanished: `vera verify` reported ok=true with no
    E501 and no Tier-3 warning, while `vera run` trapped at runtime.
    """

    _REFUTABLE = """
private data P { MkP(Int) }

private fn g(@P, @P -> @Bool)
  requires(@P.1 == @P.0)
  ensures(true)
  effects(pure)
{ true }

public fn main(@Unit -> @Bool)
  requires(true)
  ensures(true)
  effects(pure)
{ g(MkP(1), MkP(2)) }
"""

    _SATISFIABLE = """
private data P { MkP(Int) }

private fn g(@P, @P -> @Bool)
  requires(@P.1 == @P.0)
  ensures(true)
  effects(pure)
{ true }

public fn main(@Unit -> @Bool)
  requires(true)
  ensures(true)
  effects(pure)
{ g(MkP(5), MkP(5)) }
"""

    def test_refutable_adt_arg_fires_e501(self) -> None:
        """`MkP(1)` vs `MkP(2)` violates `requires(@P.1 == @P.0)` — the
        call-site precondition is statically refutable, so it must fire E501
        (the exact class the Int control already caught)."""
        result = _verify(self._REFUTABLE)
        call_pres = [
            o for o in result.obligations
            if o.kind == "call_pre" and o.error_code == "E501"
        ]
        assert len(call_pres) == 1, (
            "expected exactly one refuted call_pre obligation for the ADT "
            f"argument, got {len(call_pres)}: {call_pres}"
        )
        assert call_pres[0].status == "violated"
        _verify_err(self._REFUTABLE, "precondition")

    def test_int_control_fires_e501(self) -> None:
        """Control: the identical program with Int params already fires E501.
        Pins the parity the ADT case must reach."""
        src = """
private fn g(@Int, @Int -> @Bool)
  requires(@Int.1 == @Int.0)
  ensures(true)
  effects(pure)
{ true }

public fn main(@Unit -> @Bool)
  requires(true)
  ensures(true)
  effects(pure)
{ g(1, 2) }
"""
        result = _verify(src)
        call_pres = [
            o for o in result.obligations
            if o.kind == "call_pre" and o.error_code == "E501"
        ]
        assert len(call_pres) == 1
        assert call_pres[0].status == "violated"

    def test_satisfiable_adt_arg_discharges(self) -> None:
        """`MkP(5)` vs `MkP(5)` satisfies the precondition — it must discharge
        (no error).  Paired with the refutable case this proves the obligation
        is actually *checked* against Z3, not merely absent: same machinery,
        opposite verdict on the same shape."""
        _verify_ok(self._SATISFIABLE)

    def test_nested_adt_arg_fires_e501(self) -> None:
        """A nested-ADT argument (`MkOuter(MkInner(1))` vs `...(2)`) is
        statically refutable via recursive field decomposition (#879)."""
        _verify_err("""
private data Inner { MkInner(Int) }
private data Outer { MkOuter(Inner) }

private fn g(@Outer, @Outer -> @Bool)
  requires(@Outer.1 == @Outer.0)
  ensures(true)
  effects(pure)
{ true }

public fn main(@Unit -> @Bool)
  requires(true)
  ensures(true)
  effects(pure)
{ g(MkOuter(MkInner(1)), MkOuter(MkInner(2))) }
""", "precondition")

    def test_float64_field_adt_nan_arg_fires_e501(self) -> None:
        """A Float64-field ADT with NaN arguments: `requires(@W.1 == @W.0)`
        is runtime-false (NaN != NaN) and, post-#879 fpEQ, statically
        refutable — so it must fire E501, not silently pass."""
        _verify_err("""
private data W { MkW(Float64) }

private fn g(@W, @W -> @Bool)
  requires(@W.1 == @W.0)
  ensures(true)
  effects(pure)
{ true }

public fn main(@Unit -> @Bool)
  requires(true)
  ensures(true)
  effects(pure)
{ g(MkW(0.0 / 0.0), MkW(0.0 / 0.0)) }
""", "precondition")

    def test_untranslatable_adt_field_demotes_to_e532(self) -> None:
        """A precondition over a host-handle value (`map_size` on a `Map`)
        can't be modelled in Z3.  The obligation must demote LOUDLY to
        Tier-3 (E532 warning), never silently vanish — DESIGN.md degrades
        loudly (#882).  (The fixture's original shape — `==` on an ADT
        wrapping a Map — is now E243-rejected at check by the #874 Eq
        gate, so the untranslatable-but-legal route is a Map builtin.)

        E532 ("Cannot verify call-site precondition (undecidable)") is the
        dedicated code for this class — distinct from E522, whose registered
        meaning is a *postcondition* demotion (body undecidable)."""
        src = """
private fn g(@Map<String, Int> -> @Bool)
  requires(map_size(@Map<String, Int>.0) >= 0)
  ensures(true)
  effects(pure)
{ true }

public fn main(@Unit -> @Bool)
  requires(true)
  ensures(true)
  effects(pure)
{ g(map_new()) }
"""
        warns = _verify_warn(src, "precondition")
        assert any(w.error_code == "E532" for w in warns), (
            f"expected an E532 Tier-3 demotion warning, got: "
            f"{[(w.error_code, w.description) for w in warns]}"
        )
        result = _verify(src)
        demoted = [
            o for o in result.obligations
            if o.kind == "call_pre" and o.error_code == "E532"
        ]
        assert len(demoted) == 1, (
            f"expected one demoted call_pre obligation, got {demoted}"
        )
        assert demoted[0].status == "tier3"
        # The demotion is loud but not an error — the runtime guard enforces it.
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert errors == []

    def test_untranslatable_precondition_demotes_to_e532(self) -> None:
        """When the callee's *precondition* is outside the decidable fragment
        (`string_length(...) > 0`) the arguments still translate, so the
        call-site obligation exists but can't be discharged — it must demote
        loudly to E532, not vanish (#882).  This exercises the
        precondition-untranslatable arm, distinct from the untranslatable-
        argument arm above."""
        src = """
private fn needs_len(@String -> @String)
  requires(string_length(@String.0) > 0)
  ensures(true)
  effects(pure)
{ @String.0 }

public fn main(@String -> @String)
  requires(true)
  ensures(true)
  effects(pure)
{ needs_len(@String.0) }
"""
        result = _verify(src)
        demoted = [
            o for o in result.obligations
            if o.kind == "call_pre" and o.error_code == "E532"
        ]
        assert len(demoted) == 1, (
            f"expected one call-site E532 demotion, got {demoted}"
        )
        assert demoted[0].status == "tier3"
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert errors == []
        # The loud call-site warning is present (distinct from the callee's
        # own E521 definition-site warning).
        call_warns = [
            d for d in result.diagnostics
            if d.severity == "warning" and d.error_code == "E532"
        ]
        assert len(call_warns) == 1

    def test_trivial_requires_adt_arg_stays_silent(self) -> None:
        """A callee with only `requires(true)` has no obligation — an
        untranslatable ADT argument must NOT spuriously demote (no warning)."""
        src = """
private data M { MkM(Map<String, Int>) }

private fn g(@M, @M -> @Bool)
  requires(true)
  ensures(true)
  effects(pure)
{ true }

public fn main(@Unit -> @Bool)
  requires(true)
  ensures(true)
  effects(pure)
{ g(MkM(map_new()), MkM(map_new())) }
"""
        result = _verify(src)
        demoted = [
            o for o in result.obligations
            if o.kind == "call_pre" and o.error_code == "E532"
        ]
        assert demoted == [], (
            f"trivial requires(true) must not demote, got {demoted}"
        )
        warns = [
            d for d in result.diagnostics
            if d.severity == "warning" and d.error_code == "E532"
        ]
        assert warns == []

    # -- GAP-1: a contracted call INSIDE an ensures clause ---------------
    #
    # The call-pre demotion for a call in an ensures predicate is recorded
    # during step-7 postcondition translation, which runs AFTER the step-6b
    # drain.  Without the step-8b re-drain the obligation vanishes exactly
    # like the pre-#882 statement-position bug.  These tests pin the fix; the
    # mutation-kill is: delete the step-8b `_report_call_demotions` call in
    # `_verify_fn` (or move it before step 7) → the ensures-clause obligation
    # disappears and both assertions below go RED.

    _ENSURES_CALL = """
private fn needs_len(@String -> @Int)
  requires(string_length(@String.0) > 0)
  ensures(true)
  effects(pure)
{ 1 }

public fn caller(@String -> @Int)
  requires(true)
  ensures(needs_len(@String.0) == 1)
  effects(pure)
{ 1 }
"""

    _STMT_CALL = """
private fn needs_len(@String -> @Int)
  requires(string_length(@String.0) > 0)
  ensures(true)
  effects(pure)
{ 1 }

public fn caller(@String -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ needs_len(@String.0) }
"""

    def test_call_inside_ensures_clause_demotes_to_e532(self) -> None:
        """A contracted call whose precondition can't be translated, appearing
        inside an `ensures` predicate, must still record its call-pre Tier-3
        demotion (E532) — it must NOT silently vanish (#882 GAP-1)."""
        result = _verify(self._ENSURES_CALL)
        demoted = [
            o for o in result.obligations
            if o.kind == "call_pre" and o.error_code == "E532"
        ]
        assert len(demoted) == 1, (
            "a call inside an ensures clause must produce exactly one E532 "
            f"call-pre demotion, got {demoted}"
        )
        assert demoted[0].status == "tier3"
        call_warns = [
            d for d in result.diagnostics
            if d.severity == "warning" and d.error_code == "E532"
        ]
        assert len(call_warns) == 1, (
            "expected a loud E532 call-site warning for the ensures-clause "
            f"call, got {[(w.error_code, w.description) for w in call_warns]}"
        )
        # Loud, not an error — the runtime guard enforces the precondition.
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert errors == []

    def test_ensures_and_statement_position_report_identically(self) -> None:
        """Parity: the call-pre demotion count is identical whether the
        contracted call sits in statement position or inside an ensures
        clause.  Before the GAP-1 fix the ensures side reported ZERO and the
        statement side reported ONE — this differential is the regression."""
        stmt = _verify(self._STMT_CALL)
        ens = _verify(self._ENSURES_CALL)
        stmt_demoted = [
            o for o in stmt.obligations
            if o.kind == "call_pre" and o.error_code == "E532"
        ]
        ens_demoted = [
            o for o in ens.obligations
            if o.kind == "call_pre" and o.error_code == "E532"
        ]
        assert len(stmt_demoted) == 1
        assert len(ens_demoted) == len(stmt_demoted), (
            "statement-position and ensures-clause calls must report the same "
            f"number of E532 demotions: stmt={stmt_demoted} ens={ens_demoted}"
        )


# =====================================================================
# A GENERIC callee's call-site precondition (#1236)
# =====================================================================

def _e532_demotions(result: VerifyResult) -> list[ProofObligation]:
    return [
        o for o in result.obligations
        if o.kind == "call_pre" and o.error_code == "E532"
    ]


class TestGenericCalleeCallPreDemotes:
    """A generic callee's precondition demotes loudly, never vanishes (#1236).

    ``SmtContext._translate_call_with_info`` bails on any callee with
    ``forall_vars`` — a contract written over type parameters has no Z3 sort
    to build a summary from.  It bailed *silently*, so unlike every other arm
    of this taxonomy the call-site obligation did not exist: `verify` reported
    all-Tier-1 clean while the run trapped on the callee's own entry guard, a
    false Tier 1.  It now records the same E532 Tier-3 demotion the
    untranslatable-argument arm records.

    The demotion is unconditional on whether the precondition would HOLD —
    "cannot check", not "does not hold" — because discharging it means
    translating the contract at each monomorphized INSTANCE, which is #732's
    machinery rather than this call-summary path.  So the satisfied call
    demotes beside the violating one, which is the conservative direction.
    """

    _GENERIC = """
private forall<T> fn pick(@Array<T>, @Int -> @Int)
  requires(@Int.0 > 10)
  ensures(true)
  effects(pure)
{ @Int.0 }

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ pick([1, 2], %d) }
"""

    def test_violating_generic_precondition_demotes_instead_of_vanishing(
        self,
    ) -> None:
        src = self._GENERIC % 3
        result = _verify(src)
        demoted = _e532_demotions(result)
        assert len(demoted) == 1, (
            "the generic callee's call-site precondition obligation vanished: "
            f"{[(o.kind, o.error_code, o.status) for o in result.obligations]}"
        )
        assert demoted[0].status == "tier3"
        warns = [
            d for d in result.diagnostics
            if d.severity == "warning" and d.error_code == "E532"
        ]
        assert len(warns) == 1, warns
        assert "'pick'" in warns[0].description, warns[0].description
        # Loud, not an error: the callee's entry guard enforces it at run time.
        assert [d for d in result.diagnostics if d.severity == "error"] == []

    def test_the_runtime_traps_where_the_demotion_says_it_will(self) -> None:
        """The oracle for the false Tier 1.

        Without this the demotion above could be pure noise — it is the run
        trapping on `requires(@Int.0 > 10)` that makes the previous
        all-Tier-1-clean verdict a false one rather than a true one.
        """
        result = _compile_ok(self._GENERIC % 3)
        with pytest.raises(WasmTrapError) as exc:
            execute(result, fn_name="main")
        assert exc.value.kind == "contract_violation", exc.value.kind

    def test_the_satisfied_generic_call_demotes_too(self) -> None:
        """The mirror: `42 > 10` holds, and it still demotes (conservative).

        Statically discharging this needs the contract translated at the
        monomorphized instance (#732); until then, claiming Tier 1 here would
        be claiming a check that was never made.
        """
        src = self._GENERIC % 42
        result = _verify(src)
        assert len(_e532_demotions(result)) == 1, _e532_demotions(result)
        assert [d for d in result.diagnostics if d.severity == "error"] == []
        assert _run(src) == 42

    def test_a_generic_call_inside_ensures_demotes_too(self) -> None:
        """The ensures-clause position, drained after postcondition
        translation — the same GAP-1 re-drain the untranslatable arms rely on,
        which a fix recording only during the body pass would miss."""
        result = _verify("""
private forall<T> fn pick(@Array<T>, @Int -> @Int)
  requires(@Int.0 > 10)
  ensures(true)
  effects(pure)
{ @Int.0 }

public fn caller(@Unit -> @Int)
  requires(true)
  ensures(pick([1, 2], 3) == 3)
  effects(pure)
{ 3 }
""")
        assert len(_e532_demotions(result)) == 1, [
            (o.kind, o.error_code, o.line) for o in result.obligations
        ]

    def test_a_call_in_BOTH_positions_is_disclosed_once(self) -> None:
        """The documented qualifier on "both drains", pinned.

        A generic call written in the body AND in the `ensures` records ONE
        demotion, from the body: a body that did not translate leaves no term
        to check the postcondition against, so the clause never reaches
        translation and demotes as E522 instead.  Every other fixture here has
        the call in one position only, so a regression that double-recorded —
        or that moved the single record to the clause — would pass all of them
        while changing what a consumer counts.
        """
        result = _verify("""
private forall<T> fn pick(@Array<T>, @Int -> @Int)
  requires(@Int.0 > 10)
  ensures(true)
  effects(pure)
{ @Int.0 }

public fn caller(@Unit -> @Int)
  requires(true)
  ensures(pick([1, 2], 3) == 3)
  effects(pure)
{ pick([1, 2], 3) }
""")
        demoted = _e532_demotions(result)
        assert len(demoted) == 1, [
            (o.kind, o.error_code, o.line) for o in result.obligations
        ]
        # ... and the clause itself is disclosed as an undecidable
        # postcondition rather than silently proving.
        clause = [
            o for o in result.obligations
            if o.kind == "ensures" and o.error_code == "E522"
        ]
        assert len(clause) == 1, [
            (o.kind, o.status, o.error_code) for o in result.obligations
        ]
        assert clause[0].status == "tier3"
        # From the BODY, which is strictly later than that clause.  Anchored
        # on the clause rather than on `max(caller lines)` (PR #1283 review):
        # the demoted obligation is itself in that max, so `demoted[0].line
        # == max(...)` held BY CONSTRUCTION — and under the very mutant this
        # test's docstring names, the one that moves the record to the
        # clause, the max moved down with it and the equality stayed green
        # while the demotion was attributed to exactly the wrong place.
        assert demoted[0].line > clause[0].line, (
            demoted[0].line, clause[0].line)

    def test_the_non_generic_twin_is_still_checked_statically(self) -> None:
        """Control: drop `forall<T>` and the obligation is discharged, not
        demoted — a violating argument is a hard E501 and a satisfied one is
        Tier-1 clean with no E532 anywhere.  A "fix" that demoted every call
        would pass the tests above and fail here."""
        concrete = """
private fn pick(@Array<Int>, @Int -> @Int)
  requires(@Int.0 > 10)
  ensures(true)
  effects(pure)
{ @Int.0 }

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ pick([1, 2], %d) }
"""
        good = _verify(concrete % 42)
        assert _e532_demotions(good) == [], _e532_demotions(good)
        assert [d for d in good.diagnostics if d.severity == "error"] == []

        bad = _verify(concrete % 3)
        assert [
            d for d in bad.diagnostics
            if d.severity == "error" and d.error_code == "E501"
        ], [(d.error_code, d.description[:70]) for d in bad.diagnostics]

    def test_a_generic_callee_with_trivial_requires_stays_silent(self) -> None:
        """The gate, as on every other arm: `requires(true)` is no obligation,
        so there is nothing to lose and nothing to disclose."""
        result = _verify("""
private forall<T> fn pick(@Array<T>, @Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ @Int.0 }

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ pick([1, 2], 3) }
""")
        assert _e532_demotions(result) == [], _e532_demotions(result)
        assert [
            d for d in result.diagnostics
            if d.severity == "warning" and d.error_code == "E532"
        ] == []


# =====================================================================
# Pipe operator verification
# =====================================================================

class TestPipeVerification:
    """Pipe operator desugars correctly in SMT translation."""

    def test_pipe_verifies(self) -> None:
        """Pipe expression in verified function."""
        _verify_ok("""
private fn inc(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ @Int.0 + 1 }

private fn main(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ @Int.0 |> inc() }
""")


# =====================================================================
# Cross-module contract verification (C7d)
# =====================================================================

class TestCrossModuleVerification:
    """Imported function contracts are verified at call sites."""

    # Reusable module sources
    MATH_MODULE = """\
public fn abs(@Int -> @Int)
  requires(true)
  ensures(@Int.result >= 0)
  effects(pure)
{ if @Int.0 < 0 then { 0 - @Int.0 } else { @Int.0 } }

public fn max(@Int, @Int -> @Int)
  requires(true)
  ensures(@Int.result >= @Int.0)
  ensures(@Int.result >= @Int.1)
  effects(pure)
{ if @Int.0 >= @Int.1 then { @Int.0 } else { @Int.1 } }
"""

    GUARDED_MODULE = """\
public fn positive(@Int -> @Int)
  requires(@Int.0 > 0)
  ensures(@Int.result > 0)
  effects(pure)
{ @Int.0 }

private fn internal(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ @Int.0 }
"""

    @staticmethod
    def _resolved(
        path: tuple[str, ...], source: str,
    ) -> ResolvedModule:
        """Build a ResolvedModule from source text."""
        prog = parse_to_ast(source)
        return ResolvedModule(
            path=path,
            file_path=Path(f"/fake/{'/'.join(path)}.vera"),
            program=prog,
            source=source,
        )

    @staticmethod
    def _verify_mod(
        source: str,
        modules: list[ResolvedModule],
    ) -> VerifyResult:
        """Parse, type-check, and verify with resolved modules."""
        prog = parse_to_ast(source)
        typecheck(prog, source, resolved_modules=modules)
        return verify(prog, source, resolved_modules=modules)

    # -- Postcondition assumption -----------------------------------------

    def test_imported_postcondition_assumed(self) -> None:
        """abs(x) ensures result >= 0, so caller's ensures(@Int.result >= 0) verifies."""
        mod = self._resolved(("math",), self.MATH_MODULE)
        result = self._verify_mod("""\
import math(abs);
private fn wrap(@Int -> @Int)
  requires(true)
  ensures(@Int.result >= 0)
  effects(pure)
{ abs(@Int.0) }
""", [mod])
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert errors == [], [e.description for e in errors]

    def test_local_shadow_uses_local_contract(self) -> None:
        """§8.5.2: a bare call resolves to the LOCAL shadow's contract.

        A non-builtin name (``triple``) isolates module shadowing from the
        verifier's built-in models (abs/min/max).  The local's ensures
        (== 42) lets the caller's ensures(== 42) verify; the imported ensures
        (>= 0) alone would not — so this pins that the verifier reasons with
        the local definition for a bare call, matching codegen (§8.5.2).
        """
        mod = self._resolved(("m",), """\
public fn triple(@Int -> @Int)
  requires(true)
  ensures(@Int.result >= 0)
  effects(pure)
{ if @Int.0 < 0 then { 0 - @Int.0 } else { @Int.0 } }
""")
        result = self._verify_mod("""\
import m(triple);
public fn triple(@Int -> @Int)
  requires(true)
  ensures(@Int.result == 42)
  effects(pure)
{ 42 }
public fn main(@Unit -> @Int)
  requires(true)
  ensures(@Int.result == 42)
  effects(pure)
{ triple(0 - 5) }
""", [mod])
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert errors == [], [e.description for e in errors]

    # -- Precondition violation -------------------------------------------

    def test_imported_precondition_violation(self) -> None:
        """positive(0) violates requires(@Int.0 > 0)."""
        mod = self._resolved(("util",), self.GUARDED_MODULE)
        result = self._verify_mod("""\
import util(positive);
private fn bad(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ positive(0) }
""", [mod])
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert errors, "Expected precondition violation"
        assert any("precondition" in e.description.lower() for e in errors)

    # -- Precondition satisfied by caller's requires ----------------------

    def test_imported_precondition_satisfied(self) -> None:
        """Caller's requires(@Int.0 > 0) implies positive's precondition."""
        mod = self._resolved(("util",), self.GUARDED_MODULE)
        result = self._verify_mod("""\
import util(positive);
private fn good(@Int -> @Int)
  requires(@Int.0 > 0)
  ensures(true)
  effects(pure)
{ positive(@Int.0) }
""", [mod])
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert errors == [], [e.description for e in errors]

    # -- Chained imported calls -------------------------------------------

    def test_chained_imported_calls(self) -> None:
        """abs(max(x, y)) >= 0 verifies via composed postconditions."""
        mod = self._resolved(("math",), self.MATH_MODULE)
        result = self._verify_mod("""\
import math(abs, max);
private fn abs_max(@Int, @Int -> @Int)
  requires(true)
  ensures(@Int.result >= 0)
  effects(pure)
{ abs(max(@Int.0, @Int.1)) }
""", [mod])
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert errors == [], [e.description for e in errors]

    # -- Selective import filter ------------------------------------------

    def test_selective_import_not_imported(self) -> None:
        """Function not in import list falls back to Tier 3."""
        mod = self._resolved(("math",), self.MATH_MODULE)
        result = self._verify_mod("""\
import math(abs);
private fn wrap(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ abs(@Int.0) }
""", [mod])
        # abs is imported, max is not — but we're only calling abs here
        # abs should be Tier 1 verified (postcondition is trivial ensures(true))
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert errors == [], [e.description for e in errors]

    # -- Private function not available -----------------------------------

    def test_private_function_not_registered(self) -> None:
        """Private function from module is not injected into verifier env."""
        mod = self._resolved(("util",), self.GUARDED_MODULE)
        # 'internal' is private — it shouldn't be available as a bare call.
        # The verifier should not have it registered, so any ensures relying
        # on its postcondition would fall to Tier 3.
        result = self._verify_mod("""\
import util(positive);
private fn wrap(@Int -> @Int)
  requires(true)
  ensures(@Int.result > 0)
  effects(pure)
{ positive(1) }
""", [mod])
        # positive is public with ensures(@Int.result > 0) → Tier 1
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert errors == [], [e.description for e in errors]
        # Verify the private function 'internal' is not in the env
        assert result.summary.tier3_runtime == 0

    # -- Tier summary counts ----------------------------------------------

    def test_tier_counts_with_imports(self) -> None:
        """Imported calls promote to Tier 1 instead of Tier 3."""
        mod = self._resolved(("math",), self.MATH_MODULE)
        result = self._verify_mod("""\
import math(abs);
private fn wrap(@Int -> @Int)
  requires(true)
  ensures(@Int.result >= 0)
  effects(pure)
{ abs(@Int.0) }
""", [mod])
        # requires(true) → Tier 1, ensures(@Int.result >= 0) → Tier 1 (via abs postcondition)
        assert result.summary.tier1_verified >= 2

    # -- No regression on single-module -----------------------------------

    def test_single_module_unchanged(self) -> None:
        """Single-module programs verify identically with empty modules list."""
        source = """\
private fn id(@Int -> @Int)
  requires(true)
  ensures(@Int.result == @Int.0)
  effects(pure)
{ @Int.0 }
"""
        result_without = _verify(source)
        result_with = self._verify_mod(source, [])
        assert result_without.summary.tier1_verified == result_with.summary.tier1_verified
        assert result_without.summary.tier3_runtime == result_with.summary.tier3_runtime

    # -- #747 site 4: imported constructor @Nat-field narrowing ------------

    BOXES_MODULE = """\
public data NatBox {
  WrapN(Nat)
}

public data Box<T> {
  Wrap(T)
}
"""

    def test_imported_ctor_concrete_nat_field_obligated(self) -> None:
        """#747 site 4: an imported constructor with a concrete @Nat field
        (`WrapN(Nat)` from another module) narrowing an @Int argument is
        obligated `>= 0`.  The verifier harvests the imported ctor's field
        types into `_module_constructors`, so the narrowing fires (E503)
        under `requires(true)` instead of passing silently."""
        mod = self._resolved(("boxes",), self.BOXES_MODULE)
        result = self._verify_mod("""\
import boxes(WrapN, NatBox);
private fn f(@Int -> @NatBox)
  requires(true)
  ensures(true)
  effects(pure)
{ WrapN(@Int.0) }
""", [mod])
        violated = [o for o in result.obligations
                    if o.kind == "nat_bind" and o.status == "violated"]
        assert len(violated) == 1, [(o.kind, o.status)
                                    for o in result.obligations]
        assert violated[0].error_code == "E503"

    def test_imported_ctor_concrete_nat_field_discharged(self) -> None:
        """The imported concrete-@Nat-field narrowing discharges from a
        precondition that proves the argument non-negative."""
        mod = self._resolved(("boxes",), self.BOXES_MODULE)
        result = self._verify_mod("""\
import boxes(WrapN, NatBox);
private fn f(@Int -> @NatBox)
  requires(@Int.0 >= 0)
  ensures(true)
  effects(pure)
{ WrapN(@Int.0) }
""", [mod])
        # Pin that the obligation actually fired and verified — not merely the
        # absence of a violation (which a no-obligation regression would also
        # satisfy), mirroring the generic discharged companion (CR #756).
        statuses = [o.status for o in result.obligations
                    if o.kind == "nat_bind"]
        assert statuses == ["verified"], statuses
        assert [d for d in result.diagnostics if d.severity == "error"] == []

    def test_imported_ctor_generic_field_nat_obligated(self) -> None:
        """#747 site 4: an imported *generic* constructor field instantiated
        to @Nat at the call site (`Wrap(@Int.0)` building `Box<Nat>`) is
        obligated — the harvested field type is a TypeVar, so the
        instantiated @Nat target comes from the checker's side-table."""
        mod = self._resolved(("boxes",), self.BOXES_MODULE)
        result = self._verify_mod("""\
import boxes(Wrap, Box);
private fn f(@Int -> @Box<Nat>)
  requires(true)
  ensures(true)
  effects(pure)
{ Wrap(@Int.0) }
""", [mod])
        violated = [o for o in result.obligations
                    if o.kind == "nat_bind" and o.status == "violated"]
        assert len(violated) == 1, [(o.kind, o.status)
                                    for o in result.obligations]
        assert violated[0].error_code == "E503"

    def test_imported_ctor_generic_field_nat_discharged(self) -> None:
        """The imported generic-constructor narrowing discharges from a
        precondition — pins that imported generic-field instantiation isn't
        always treated as violated (CodeRabbit, PR #756)."""
        mod = self._resolved(("boxes",), self.BOXES_MODULE)
        result = self._verify_mod("""\
import boxes(Wrap, Box);
private fn f(@Int -> @Box<Nat>)
  requires(@Int.0 >= 0)
  ensures(true)
  effects(pure)
{ Wrap(@Int.0) }
""", [mod])
        # The obligation must be present AND verified — not merely absent
        # (a regression that stopped emitting it would also be "not
        # violated") (CodeRabbit, PR #756).
        verified = [o for o in result.obligations
                    if o.kind == "nat_bind" and o.status == "verified"]
        assert len(verified) == 1, [(o.kind, o.status)
                                    for o in result.obligations]
        assert [d for d in result.diagnostics if d.severity == "error"] == []

    # -- #1000: private module generics reached transitively ---------------

    # Two modules, each with a same-named PRIVATE generic `inner` behind a
    # PUBLIC generic that calls it.  Module `ma`'s `inner` tells the truth
    # (ensures result == 0, body 0); module `mb`'s LIES (ensures result == 9,
    # body 0).  The importer reaches both transitively.
    _MA_TRUTH = (
        "private forall<T> fn inner(@T -> @Int)"
        " requires(true) ensures(@Int.result == 0) effects(pure) { 0 }\n"
        "public forall<T> fn oa(@T -> @Int)"
        " requires(true) ensures(true) effects(pure) { inner(@T.0) }\n"
    )
    _MB_LIE = (
        "private forall<T> fn inner(@T -> @Int)"
        " requires(true) ensures(@Int.result == 9) effects(pure) { 0 }\n"
        "public forall<T> fn ob(@T -> @Int)"
        " requires(true) ensures(true) effects(pure) { inner(@T.0) }\n"
    )
    _MB_TRUTH = (
        "private forall<T> fn inner(@T -> @Int)"
        " requires(true) ensures(@Int.result == 0) effects(pure) { 0 }\n"
        "public forall<T> fn ob(@T -> @Int)"
        " requires(true) ensures(true) effects(pure) { inner(@T.0) }\n"
    )
    _TWO_PRIV_MAIN = (
        "import ma(oa);\n"
        "import mb(ob);\n"
        "public fn main(@Unit -> @Int)"
        " requires(true) ensures(true) effects(pure) { oa(0) + ob(0) }\n"
    )

    def test_lying_private_module_generic_is_E500(self) -> None:
        """#1000c: a LYING PRIVATE module generic reached transitively must be
        an E500 at the importer, not a silent false Tier-1.

        `mb`'s private `inner` has ``ensures(@Int.result == 9)`` over body `0`.
        It is unimportable and NOT in ``env.functions`` — pre-fix the importer
        never harvested it, so its clone ran with a contract neither module
        proved.  Harvesting it under the module-qualified ``mod$mb$inner`` key
        and verifying its instantiations catches the lie.  `ma`'s TRUTHFUL
        namesake must NOT also error — the two must be kept under DISTINCT keys
        (a single bare-name entry would collapse them)."""
        mods = [
            self._resolved(("ma",), self._MA_TRUTH),
            self._resolved(("mb",), self._MB_LIE),
        ]
        result = self._verify_mod(self._TWO_PRIV_MAIN, mods)
        e500s = [d for d in result.diagnostics if d.error_code == "E500"]
        assert len(e500s) == 1, (
            f"exactly one E500 (mb's lying inner) expected, got "
            f"{[(d.error_code, d.description[:60]) for d in result.diagnostics]}"
        )
        assert "inner" in e500s[0].description, e500s[0].description

    def test_truthful_private_module_generics_verify_clean(self) -> None:
        """#1000c control: two modules with TRUTHFUL same-named private generics
        reached transitively must both verify clean under distinct keys — no
        E500 for either.  Pins that the private-generic verification does not
        false-positive (and that keeping distinct keys does not spuriously fail
        a truthful namesake)."""
        mods = [
            self._resolved(("ma",), self._MA_TRUTH),
            self._resolved(("mb",), self._MB_TRUTH),
        ]
        result = self._verify_mod(self._TWO_PRIV_MAIN, mods)
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert errors == [], [
            (d.error_code, d.description[:60]) for d in errors
        ]

    # -- #1029: shadowed / nested private generics reached transitively -----

    def test_lying_private_sibling_of_shadowed_generic_is_E500(self) -> None:
        """#1029 (R4): a LYING PRIVATE sibling generic (`sib`) reached through a
        locally-shadowed public generic (`g::gen`) must be an E500 at the importer.

        `g::gen` is shadowed by a local non-generic `gen`; it is reached via the
        qualified `g::gen(5)` and its body calls the private `sib`, whose
        ``ensures(@Int.result == 999)`` lies over body `11`.  Codegen emits the
        `mod$g$sib<Int>` clone (it traps at run), but pre-fix the verifier built
        its shadowed map from public-shadowed generics only, so `sib` was never
        discovered and its lying contract ran unverified — a false Tier-1.
        Discovering the private sibling and verifying it under `mod$g$sib` catches
        the lie."""
        g_mod = self._resolved(("g",), (
            "private forall<T> fn sib(@T -> @Int)"
            " requires(true) ensures(@Int.result == 999) effects(pure) { 11 }\n"
            "public forall<T> fn gen(@T -> @Int)"
            " requires(true) ensures(true) effects(pure) { sib(@T.0) }\n"
        ))
        result = self._verify_mod(
            "import g;\n"
            "private fn gen(@Int -> @Int)"
            " requires(true) ensures(true) effects(pure) { @Int.0 + 100 }\n"
            "public fn main(@Unit -> @Int)"
            " requires(true) ensures(true) effects(pure) { g::gen(5) }\n",
            [g_mod],
        )
        e500s = [d for d in result.diagnostics if d.error_code == "E500"]
        assert len(e500s) == 1, (
            f"exactly one E500 (the lying private sibling) expected, got "
            f"{[(d.error_code, d.description[:70]) for d in result.diagnostics]}"
        )
        assert "sib" in e500s[0].description, e500s[0].description

    def test_lying_nested_generic_under_private_generic_is_E500(self) -> None:
        """#1029 (R3/R5): a LYING nested `forall` where-helper (`ginner`) under a
        PRIVATE module generic (`priv_outer`) reached through a public entry must
        be an E500 — NOT the uninstantiated-generic E520.

        `pub_entry` (public) calls the private `priv_outer`, whose nested
        `ginner` has ``ensures(@Int.result == 999)`` over body `1`.  Pre-fix the
        three surfaces disagreed on the key: codegen emitted a concrete-INCLUDING
        `mod$lib1$priv_outer$Int$where$ginner`, discovery recorded the
        concrete-FREE `mod$lib1$priv_outer$where$ginner`, and the verify-walk
        rebuilt a BARE `priv_outer$where$ginner` — so the helper fell to the
        uninstantiated E520 path and its lie ran unverified (a false Tier-1).  One
        canonical concrete-free `mod$…`-prefixed key on all three surfaces
        instantiates it and catches the lie."""
        lib_mod = self._resolved(("lib1",), (
            "private forall<T> fn priv_outer(@T -> @Int)"
            " requires(true) ensures(true) effects(pure) { ginner(@T.0) }\n"
            "where {\n"
            "  forall<U> fn ginner(@U -> @Int)"
            "    requires(true) ensures(@Int.result == 999) effects(pure) { 1 }\n"
            "}\n"
            "public forall<T> fn pub_entry(@T -> @Int)"
            " requires(true) ensures(true) effects(pure) { priv_outer(@T.0) }\n"
        ))
        result = self._verify_mod(
            "import lib1(pub_entry);\n"
            "public fn main(@Unit -> @Int)"
            " requires(true) ensures(true) effects(pure) { pub_entry(7) }\n",
            [lib_mod],
        )
        e500s = [d for d in result.diagnostics if d.error_code == "E500"]
        assert len(e500s) == 1, (
            f"exactly one E500 (the lying nested generic) expected, got "
            f"{[(d.error_code, d.description[:70]) for d in result.diagnostics]}"
        )
        assert "ginner" in e500s[0].description, e500s[0].description
        # The uninstantiated-generic Tier-3 fallback must NOT fire: `ginner` IS
        # instantiated at Int, so its contract is checked, not deferred (E520 was
        # the pre-fix false-Tier-1 signature).
        assert not [d for d in result.diagnostics if d.error_code == "E520"], (
            f"no E520 (uninstantiated generic) expected — ginner is "
            f"instantiated, got {[d.error_code for d in result.diagnostics]}"
        )

    def test_lying_nested_generic_two_modules_is_E500(self) -> None:
        """#1029 (R2): two imported modules whose SAME-named non-generic parent
        (`compute`) carries a SAME-named nested `forall` helper (`gid`) must key
        the two helpers DISTINCTLY, so a LYING one is verified independently.

        `ma`'s `gid` tells the truth (``ensures(@T.result == @T.0)``); `mb`'s LIES
        (``ensures(@T.result == 9)`` over body `@T.0`).  Pre-fix both qualified to
        the bare `compute$where$gid` and collapsed first-seen-wins, so only `ma`'s
        truthful helper was verified and `mb`'s lie was a false Tier-1.
        Namespacing the qualification by module path
        (`mod$ma$compute$where$gid` vs `mod$mb$compute$where$gid`) keeps them
        distinct and catches the lie."""
        ma = self._resolved(("ma",), (
            "public fn compute(@Int -> @Int)"
            " requires(true) ensures(true) effects(pure) { gid(@Int.0) }\n"
            "where {\n"
            "  forall<T> fn gid(@T -> @T)"
            "    requires(true) ensures(@T.result == @T.0) effects(pure)"
            " { @T.0 }\n"
            "}\n"
        ))
        mb = self._resolved(("mb",), (
            "public fn compute(@Int -> @Int)"
            " requires(true) ensures(true) effects(pure) { gid(@Int.0) }\n"
            "where {\n"
            "  forall<T> fn gid(@T -> @T)"
            "    requires(true) ensures(@T.result == 9) effects(pure) { @T.0 }\n"
            "}\n"
        ))
        result = self._verify_mod(
            "import ma(compute);\n"
            "import mb(compute);\n"
            "public fn main(@Unit -> @Int)"
            " requires(true) ensures(true) effects(pure)"
            " { ma::compute(1) + mb::compute(1) }\n",
            [ma, mb],
        )
        e500s = [d for d in result.diagnostics if d.error_code == "E500"]
        assert len(e500s) == 1, (
            f"exactly one E500 (mb's lying nested gid) expected, got "
            f"{[(d.error_code, d.description[:70]) for d in result.diagnostics]}"
        )
        assert "gid" in e500s[0].description, e500s[0].description

    def test_shadowed_self_recursive_module_generic_stays_healthy(self) -> None:
        """A SELF-RECURSIVE public module generic, locally shadowed by a
        same-named non-generic, verifies and keeps its recursion on the
        module's own clone (PR #1029 review probe): the local shadow never
        captures the qualified clone's self-call, so verify is green and the
        obligation stream carries the module generic's instances."""
        g = self._resolved(("g",), (
            "public forall<T> fn gen(@T, @Int -> @Int)"
            " requires(@Int.0 >= 0) ensures(true) effects(pure)\n"
            "{ if @Int.0 == 0 then { 0 } else"
            " { gen(@T.0, @Int.0 - 1) + 1 } }\n"
        ))
        result = self._verify_mod(
            "import g;\n"
            "private fn gen(@Int -> @Int)"
            " requires(true) ensures(true) effects(pure) { @Int.0 + 100 }\n"
            "public fn main(@Unit -> @Int)"
            " requires(true) ensures(true) effects(pure)"
            " { g::gen(true, 3) }\n",
            [g],
        )
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert not errors, (
            f"shadowed self-recursive module generic must verify clean, got "
            f"{[(d.error_code, d.description[:60]) for d in errors]}"
        )


# =====================================================================
# User-declared `data Tuple` vs the builtin tuple pseudo-constructor
# (PR #1200 review round; refused at check since #1397)
# =====================================================================

_USER_TUPLE_ADT_PROGRAM = """
private data Tuple<A, B> {
  Tuple(A, B)
}

public fn g(@Int -> @Int)
  requires(true)
  ensures(@Int.result == 2)
  effects(pure)
{
  let @Tuple<Int, Int> = Tuple(5, 3);
  match @Tuple<Int, Int>.0 {
    Tuple(@Int, @Int) -> @Int.1 - @Int.0
  }
}
"""

#: The same program with the declaration removed, so `Tuple` is the BUILTIN
#: variadic carrier: the shape the SMT synthesis door is for.
_BUILTIN_TUPLE_PROGRAM = _USER_TUPLE_ADT_PROGRAM.split("}\n\n", 1)[1]

#: And its isomorphic user-ADT twin, under a name nothing special-cases.
_PAIR_ADT_PROGRAM = _USER_TUPLE_ADT_PROGRAM.replace("Tuple", "Pair")


class TestUserTupleCtorRegistryRouting:
    """The `Tuple` name collision, now settled by reserving the name.

    The SMT layer's synthesis door reverse-maps argument sorts to types (a
    Nat-typed argument recovers as Int from Z3's IntSort), so routing a
    REGISTERED Tuple through it would materialise fresh instantiations of a
    user ADT (`Tuple<Int, Int>`) that the declared-type side never created —
    violating the #882/#918 never-newly-enables posture and desyncing the
    constructor term's sort from the declared-side sort.  The registry guard
    (`expr.name == "Tuple" and "Tuple" not in self._adt_registry`) kept the
    door shut for a user declaration.

    #1397 removes the collision at its source: `Tuple` is reserved in the
    data namespace (E158), so no declaration ever registers under that name
    and the door's registry test can only see the builtin carrier.  The
    guard stays — it is the condition that makes that true rather than
    assumed — and these cells pin the two halves it now separates: the
    declaration is refused, and the BUILTIN carrier still translates through
    the synthesis door with a profile identical to an isomorphic user ADT.
    """

    def test_a_user_tuple_declaration_is_refused_at_check(self) -> None:
        """The registry can never hold a user `Tuple` to route.

        This is the premise every claim below rests on, so it is measured
        rather than assumed: without it the two cells here would be
        asserting things about the builtin carrier while a second Tuple
        could still reach the same door.
        """
        codes = [
            d.error_code
            for d in typecheck(
                parse_to_ast(_USER_TUPLE_ADT_PROGRAM),
                _USER_TUPLE_ADT_PROGRAM,
            )
            if d.severity == "error"
        ]
        assert "E158" in codes, codes

    def test_the_two_doors_keep_their_own_postures(self) -> None:
        """The synthesis door and the registry path, each measured directly.

        The old cell here was an ISOMORPHIC-RENAME differential: a user
        `data Tuple` and its mechanical `data Pair` rename had to produce
        identical obligation profiles, so a name-keyed shortcut in the SMT
        layer could not give the `Tuple` spelling a proof the `Pair`
        spelling did not earn.  Its two sides can no longer both exist —
        #1397 reserves the name — so what remains is to measure each door
        on its own program rather than assert an equality between one that
        compiles and one that does not.

        They answer DIFFERENTLY, on purpose.  The builtin carrier has no
        registry entry and therefore no declared-side sort to desync from,
        so #764's synthesis door translates its constructor from the
        argument sorts and the destructure proves Tier 1.  A registry ADT
        of the same shape takes the registry path, which only reuses cached
        instantiations (#882/#918 never-newly-enables), so its ensures
        honestly demotes.  Pinning both is what would catch the synthesis
        door widening to registry ADTs — the divergence the rename
        differential existed to prevent, now stated as the two postures it
        was really about.
        """
        builtin_profile = [
            (o.fn_name, o.kind, o.status)
            for o in _verify(_BUILTIN_TUPLE_PROGRAM).obligations
        ]
        assert all(status == "verified" for _, _, status in builtin_profile), (
            f"the builtin tuple destructure must still prove Tier 1, got "
            f"{builtin_profile}"
        )
        pair_profile = [
            (o.fn_name, o.kind, o.status)
            for o in _verify(_PAIR_ADT_PROGRAM).obligations
        ]
        assert ("g", "ensures", "tier3") in pair_profile, (
            f"an isomorphic registry ADT must stay on the conservative "
            f"registry path, got {pair_profile}"
        )

    def test_uncached_user_adt_ctor_instantiation_demotes(self) -> None:
        """A ctor call whose argument-pinned instantiation was never cached
        demotes; the SMT layer must not mint the instantiation itself.

        `pick`'s parameter type materialises the user ADT at `<Nat, Nat>`;
        the call argument `Pair(@Nat.0, @Nat.0)` pins `<Int, Int>` (Nat
        reverse-maps to Int), which is uncached — so the constructor is
        untranslatable and `f`'s ensures, which depends on the call result,
        honestly demotes to the runtime tier.  Spelled `Pair` since #1397:
        the shape is what is under test, and the `Tuple` spelling of it is
        no longer a program.  A future improvement may legitimately flip
        this obligation back to verified — but only by REUSING the declared
        `<Nat, Nat>` sort (e.g. recorded-type-hint routing), never by
        minting; the isomorphic-rename differential above still governs.
        """
        result = _verify("""
private data Pair<A, B> {
  Pair(A, B)
}

private fn pick(@Pair<Nat, Nat> -> @Int)
  requires(true)
  ensures(@Int.result >= 0)
  effects(pure)
{
  match @Pair<Nat, Nat>.0 {
    Pair(@Nat, @Nat) -> nat_to_int(@Nat.0)
  }
}

public fn f(@Nat -> @Int)
  requires(true)
  ensures(@Int.result >= 0)
  effects(pure)
{
  pick(Pair(@Nat.0, @Nat.0))
}
""")
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert not errors, (
            f"valid program must not error: "
            f"{[(d.error_code, d.description[:60]) for d in errors]}"
        )
        f_ensures = [
            o for o in result.obligations
            if o.fn_name == "f" and o.kind == "ensures"
        ]
        assert len(f_ensures) == 1
        assert f_ensures[0].status == "tier3", (
            f"f's ensures depends on an uncached ctor instantiation; "
            f"expected honest tier3 demotion, got {f_ensures[0].status!r}"
        )
