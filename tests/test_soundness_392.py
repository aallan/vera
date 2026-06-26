"""Regression tests for the #392 smt.py / verifier soundness audit.

Batch 1 — three confirmed Tier-1/Tier-3 disagreements, fixed together:
  #799 — signed division/modulo must truncate toward zero (Vera `i64.div_s` /
         `i64.rem_s`), not follow Z3's Euclidean `div`/`mod`.
  #800 — a body `assert(P)` must generate a Tier-1 obligation (prove `P`), not
         be silently ignored (spec §6.2.5).
  #801 — divisions appearing in contract predicates must get a `div_zero`
         obligation, mirroring body divisions (#680).

Batch 2 — the assume-half follow-up to #800:
  #804 — a body `assert(P)` / `assume(P)` adds `P` to the assumption context for
         SUBSEQUENT obligations (spec §6.4.1 WP rules `assert(P) | P && WP(rest)`
         and `assume(P) | P ==> WP(rest)`).  Moves obligations tier3 -> verified
         and removes false E503/E500 where a prior assert guards the site.

Written test-first: each FAILS on the pre-fix verifier (demonstrating the bug)
and passes once the fix lands. Parent audit issue: #392.
"""

from __future__ import annotations

from vera.parser import parse_to_ast
from vera.checker import typecheck_with_artifacts
from vera.verifier import VerifyResult, verify


def _verify(source: str) -> VerifyResult:
    ast = parse_to_ast(source)
    _diags, arts = typecheck_with_artifacts(ast, source)
    return verify(
        ast, source,
        expr_types=arts.expr_semantic_types,
        expr_target_types=arts.expr_target_types,
    )


def _verify_ok(source: str) -> None:
    result = _verify(source)
    errors = [d for d in result.diagnostics if d.severity == "error"]
    assert errors == [], f"Expected no errors, got: {[e.description for e in errors]}"


def _verify_err(source: str, match: str) -> list:
    result = _verify(source)
    errors = [d for d in result.diagnostics if d.severity == "error"]
    assert errors, "Expected at least one error, got none"
    matched = [e for e in errors if match.lower() in e.description.lower()]
    assert matched, f"No error matched '{match}'. Errors: {[e.description for e in errors]}"
    return matched


# =====================================================================
# #799 — signed division / modulo truncate toward zero (not Euclidean)
# (-7)/2 = -3 truncated  (Z3 Euclidean would give -4)
# (-7)%2 = -1 truncated  (Z3 Euclidean would give  1)
# x is pinned to -7 via `@Int.0 + 7 == 0` (avoids a @Nat-underflow literal).
# =====================================================================
class TestSignedDivModTruncation799:
    def test_negative_division_truncates_toward_zero(self) -> None:
        _verify_ok("""
public fn h(@Int -> @Int)
  requires(@Int.0 + 7 == 0) ensures(@Int.result + 3 == 0) effects(pure)
{ @Int.0 / 2 }
""")

    def test_euclidean_division_quotient_is_rejected(self) -> None:
        _verify_err("""
public fn h(@Int -> @Int)
  requires(@Int.0 + 7 == 0) ensures(@Int.result + 4 == 0) effects(pure)
{ @Int.0 / 2 }
""", "postcondition")

    def test_negative_modulo_takes_dividend_sign(self) -> None:
        _verify_ok("""
public fn m(@Int -> @Int)
  requires(@Int.0 + 7 == 0) ensures(@Int.result + 1 == 0) effects(pure)
{ @Int.0 % 2 }
""")

    def test_euclidean_modulo_remainder_is_rejected(self) -> None:
        _verify_err("""
public fn m(@Int -> @Int)
  requires(@Int.0 + 7 == 0) ensures(@Int.result == 1) effects(pure)
{ @Int.0 % 2 }
""", "postcondition")

    def test_positive_operands_unchanged(self) -> None:
        # Regression guard: the common positive path verifies unchanged
        # (truncated == Euclidean for non-negative operands).
        _verify_ok("""
public fn h(@Int -> @Int)
  requires(@Int.0 == 7) ensures(@Int.result == 3) effects(pure)
{ @Int.0 / 2 }
""")
        _verify_ok("""
public fn m(@Int -> @Int)
  requires(@Int.0 == 7) ensures(@Int.result == 1) effects(pure)
{ @Int.0 % 2 }
""")

    def test_positive_dividend_negative_divisor(self) -> None:
        # 7 / -2 == -3 (truncated); 7 % -2 == 1 (remainder takes the dividend
        # sign).  Pins the Xor sign branch and the `If(a < 0, ...)` mod branch
        # in the *other* direction from the negative-dividend cases above.
        _verify_ok("""
public fn h(@Int -> @Int)
  requires(@Int.0 + 2 == 0) ensures(@Int.result + 3 == 0) effects(pure)
{ 7 / @Int.0 }
""")
        _verify_ok("""
public fn m(@Int -> @Int)
  requires(@Int.0 + 2 == 0) ensures(@Int.result == 1) effects(pure)
{ 7 % @Int.0 }
""")

    def test_both_operands_negative(self) -> None:
        # -7 / -2 == 3 — same-sign quotient, the Xor-false-via-two-negatives
        # path (Euclidean would give 4).
        _verify_ok("""
public fn h(@Int -> @Int)
  requires(@Int.0 + 2 == 0) ensures(@Int.result == 3) effects(pure)
{ (0 - 7) / @Int.0 }
""")


# =====================================================================
# #800 — body assert(P) generates a Tier-1 obligation (two-check:
# prove P -> verified; else prove not-P -> violated; else -> tier3)
# =====================================================================
class TestAssertObligation800:
    def test_unprovable_assert_falls_to_tier3(self) -> None:
        result = _verify("""
public fn au(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ assert(@Int.0 > 5); @Int.0 }
""")
        asserts = [o for o in result.obligations if o.kind == "assert"]
        assert len(asserts) == 1 and asserts[0].status == "tier3", [
            (o.kind, o.status) for o in result.obligations
        ]

    def test_provable_assert_is_tier1_verified(self) -> None:
        result = _verify("""
public fn ap(@Int -> @Int)
  requires(@Int.0 > 10) ensures(true) effects(pure)
{ assert(@Int.0 > 5); @Int.0 }
""")
        asserts = [o for o in result.obligations if o.kind == "assert"]
        assert len(asserts) == 1 and asserts[0].status == "verified", [
            (o.kind, o.status) for o in result.obligations
        ]

    def test_provably_false_assert_is_violated(self) -> None:
        result = _verify("""
public fn af(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ assert(@Int.0 > @Int.0); @Int.0 }
""")
        asserts = [o for o in result.obligations if o.kind == "assert"]
        assert len(asserts) == 1 and asserts[0].status == "violated", [
            (o.kind, o.status) for o in result.obligations
        ]
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert errors, "provably-false assert should report an error"

    def test_branch_guarded_assert_verifies(self) -> None:
        # An assert provable from the enclosing if-condition (a path condition)
        # discharges at Tier 1 — check_valid picks up smt._path_conditions.
        result = _verify("""
public fn f(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ if @Int.0 > 10 then { assert(@Int.0 > 5); @Int.0 } else { 0 } }
""")
        asserts = [o for o in result.obligations if o.kind == "assert"]
        assert len(asserts) == 1 and asserts[0].status == "verified", [
            (o.kind, o.status) for o in result.obligations
        ]

    def test_untranslatable_assert_predicate_falls_to_tier3(self) -> None:
        # An assert whose predicate the SMT layer cannot translate (here a Map
        # membership, uninterpreted in Z3) hits the early `pred is None` branch
        # of _check_assert_obligation and falls to tier3 (#800).
        result = _verify("""
public fn f(@Map<Int, Int> -> @Int)
  requires(true) ensures(true) effects(pure)
{ assert(map_contains(@Map<Int, Int>.0, 5)); 0 }
""")
        asserts = [o for o in result.obligations if o.kind == "assert"]
        assert len(asserts) == 1 and asserts[0].status == "tier3", [
            (o.kind, o.status) for o in result.obligations
        ]


# =====================================================================
# #801 — divisions in contract predicates get a div_zero obligation
# =====================================================================
class TestContractDivZeroObligation801:
    def test_unguarded_division_in_ensures_reports_e526(self) -> None:
        # A division in a contract predicate whose divisor can be zero is a
        # loud E526 (mirroring body divisions, #680) — no longer silently
        # proved (#801).  `tier3` would require an *opaque* (undecidable)
        # divisor, which a contract (no `let`) cannot introduce.
        result = _verify("""
public fn f(@Int -> @Int)
  requires(true) ensures(@Int.0 / @Int.0 == @Int.0 / @Int.0) effects(pure)
{ @Int.0 }
""")
        divs = [o for o in result.obligations if o.kind == "div_zero"]
        assert len(divs) >= 1, [(o.kind, o.status) for o in result.obligations]
        assert any(d.error_code == "E526" for d in result.diagnostics), [
            d.error_code for d in result.diagnostics
        ]

    def test_guarded_division_in_ensures_verifies(self) -> None:
        result = _verify("""
public fn f(@Int -> @Int)
  requires(@Int.0 != 0) ensures(@Int.0 / @Int.0 == 1) effects(pure)
{ @Int.0 }
""")
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert errors == [], [e.error_code for e in errors]
        divs = [o for o in result.obligations if o.kind == "div_zero"]
        assert len(divs) >= 1 and all(o.status == "verified" for o in divs), [
            (o.kind, o.status) for o in result.obligations
        ]

    def test_unguarded_division_in_requires_reports_e526(self) -> None:
        # The contract walk covers `requires` predicates too (not just ensures).
        result = _verify("""
public fn f(@Int -> @Int)
  requires(10 / @Int.0 > 0) ensures(true) effects(pure)
{ @Int.0 }
""")
        assert any(d.error_code == "E526" for d in result.diagnostics), [
            d.error_code for d in result.diagnostics
        ]

    def test_result_divisor_in_ensures_is_obligated(self) -> None:
        # The `@result`-binding path: a divisor that IS `@result` resolves to
        # the body result for the contract walk and is obligated (#801).
        result = _verify("""
public fn f(@Int -> @Int)
  requires(true) ensures(100 / @Int.result == 100 / @Int.result) effects(pure)
{ @Int.0 }
""")
        divs = [o for o in result.obligations if o.kind == "div_zero"]
        assert len(divs) >= 1, [(o.kind, o.status) for o in result.obligations]

    def test_later_requires_does_not_discharge_earlier_division(self) -> None:
        # CR #803: a requires division relies only on EARLIER requires.  A
        # *later* `@Int.0 != 0` must NOT discharge an earlier `10 / @Int.0` —
        # the runtime precondition guard evaluates requires in order, so the
        # earlier division traps (confirmed via `vera run`) before the later
        # guard is checked.
        result = _verify("""
public fn f(@Int -> @Int)
  requires(10 / @Int.0 > 0)
  requires(@Int.0 != 0)
  effects(pure)
{ @Int.0 }
""")
        assert any(d.error_code == "E526" for d in result.diagnostics), [
            d.error_code for d in result.diagnostics
        ]

    def test_earlier_requires_guards_later_division(self) -> None:
        # The guard-first ordering verifies: requires[1]'s division sees
        # requires[0] (`@Int.0 != 0`) in its prefix.
        _verify_ok("""
public fn f(@Int -> @Int)
  requires(@Int.0 != 0)
  requires(10 / @Int.0 > 0)
  effects(pure)
{ @Int.0 }
""")

    def test_nested_division_in_untranslatable_requires_obligated(self) -> None:
        # CR #803 (outside-diff): a division nested inside an UNTRANSLATABLE
        # requires predicate (Map membership, uninterpreted in Z3) is still
        # obligated — the primitive-op walk runs before the `z3_pre is None`
        # early-continue, mirroring the body walk.
        result = _verify("""
public fn f(@Map<Int, Int>, @Int -> @Int)
  requires(map_contains(@Map<Int, Int>.0, 10 / @Int.0))
  ensures(true)
  effects(pure)
{ @Int.0 }
""")
        assert any(d.error_code == "E526" for d in result.diagnostics), [
            d.error_code for d in result.diagnostics
        ]


# =====================================================================
# #804 — assert/assume facts (the *assume* half of the WP rule).  #800
# added the *prove* half (a body `assert(P)` carries a Tier-1 obligation);
# this adds the *assume* half: after the obligation, `P` joins the context
# for SUBSEQUENT obligations (spec §6.4.1 `assert(P) | P && WP(rest)`,
# `assume(P) | P ==> WP(rest)`).  Sound because the §11.14.1 runtime trap
# guarantees execution only proceeds past the assert/assume in worlds where
# `P` holds — so `P` is assumable downstream even when the assert itself
# only reached tier3.  Two invariants are pinned by guard tests: facts flow
# FORWARD only, and a branch fact stays branch-LOCAL.
# =====================================================================
class TestAssertAssumeFacts804:
    def test_chained_asserts_second_discharged_by_first(self) -> None:
        # The flip of the old #800 pinning test: the first assert (unprovable
        # from requires(true)) stays tier3, yet it discharges the second at
        # Tier 1 (@Int.0 > 10 ==> @Int.0 > 5).
        result = _verify("""
public fn f(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ assert(@Int.0 > 10); assert(@Int.0 > 5); @Int.0 }
""")
        asserts = [o for o in result.obligations if o.kind == "assert"]
        assert [a.status for a in asserts] == ["tier3", "verified"], [
            (o.kind, o.status) for o in result.obligations
        ]

    def test_assume_predicate_discharges_later_assert(self) -> None:
        # assume(P) carries the same downstream fact as assert(P) (spec §6.4.1
        # `assume(P) | P ==> WP(rest)`) but with no obligation of its own — so
        # there is a single assert obligation, discharged by the assumption.
        result = _verify("""
public fn f(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ assume(@Int.0 > 10); assert(@Int.0 > 5); @Int.0 }
""")
        asserts = [o for o in result.obligations if o.kind == "assert"]
        assert len(asserts) == 1 and asserts[0].status == "verified", [
            (o.kind, o.status) for o in result.obligations
        ]

    def test_assert_discharges_nat_narrowing(self) -> None:
        # The issue's first example: a prior `assert(@Int.0 >= 0)` discharges a
        # later `let @Nat = @Int.0` narrowing.  Pre-fix this is a FALSE E503 —
        # Z3 witnesses @Int.0 = -1, unreachable because the assert traps first.
        result = _verify("""
public fn f(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ assert(@Int.0 >= 0); let @Nat = @Int.0; @Int.0 }
""")
        nat_binds = [o for o in result.obligations if o.kind == "nat_bind"]
        assert len(nat_binds) == 1 and nat_binds[0].status == "verified", [
            (o.kind, o.status) for o in result.obligations
        ]
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert errors == [], [e.error_code for e in errors]

    def test_within_branch_assert_discharges_later_assert(self) -> None:
        # Forward discharge composes with path conditions: inside a branch whose
        # condition (@Bool.0) is unrelated to @Int, the first assert still
        # discharges the second.
        result = _verify("""
public fn f(@Bool, @Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ if @Bool.0 then { assert(@Int.0 > 50); assert(@Int.0 > 10); @Int.0 } else { @Int.0 } }
""")
        asserts = [o for o in result.obligations if o.kind == "assert"]
        assert [a.status for a in asserts] == ["tier3", "verified"], [
            (o.kind, o.status) for o in result.obligations
        ]

    def test_branch_assert_does_not_leak_across_branches(self) -> None:
        # Soundness guard (green pre- AND post-fix; a global push would redden
        # it): a then-branch assert(@Int.0 > 50) must NOT discharge the
        # else-branch's identical assert — the fact is branch-local.
        result = _verify("""
public fn f(@Bool, @Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ if @Bool.0 then { assert(@Int.0 > 50); @Int.0 } else { assert(@Int.0 > 50); @Int.0 } }
""")
        asserts = [o for o in result.obligations if o.kind == "assert"]
        assert [a.status for a in asserts] == ["tier3", "tier3"], [
            (o.kind, o.status) for o in result.obligations
        ]

    def test_later_assert_does_not_discharge_earlier(self) -> None:
        # Soundness guard: facts flow FORWARD only.  The first assert(@Int.0 > 5)
        # must stay tier3 — a backward leak from the later (stronger) @Int.0 > 10
        # would wrongly mark it verified (>10 ==> >5) and drop its runtime guard.
        result = _verify("""
public fn f(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ assert(@Int.0 > 5); assert(@Int.0 > 10); @Int.0 }
""")
        asserts = [o for o in result.obligations if o.kind == "assert"]
        assert [a.status for a in asserts] == ["tier3", "tier3"], [
            (o.kind, o.status) for o in result.obligations
        ]

    def test_top_level_assert_discharges_postcondition(self) -> None:
        # A top-level assert holds when the body returns, so it discharges the
        # postcondition.  Pre-fix this is a FALSE E500 — Z3 witnesses @Int.0 = 0
        # (unreachable; the assert traps first).
        result = _verify("""
public fn f(@Int -> @Int)
  requires(true) ensures(@Int.result > 5) effects(pure)
{ assert(@Int.0 > 5); @Int.0 }
""")
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert errors == [], [e.error_code for e in errors]
        ensures_obs = [o for o in result.obligations if o.kind == "ensures"]
        assert ensures_obs and all(o.status == "verified" for o in ensures_obs), [
            (o.kind, o.status) for o in result.obligations
        ]

    def test_top_level_assert_discharges_refined_return(self) -> None:
        # A refined return type is structurally a postcondition (verifier step
        # 7b), so a top-level assert discharges it too.  Pre-fix this is a FALSE
        # E505 — Z3 witnesses @Int.0 = 0 (unreachable; the assert traps first).
        result = _verify("""
type Pos = { @Int | @Int.0 > 0 };

public fn f(@Int -> @Pos)
  requires(true) effects(pure)
{ assert(@Int.0 > 0); @Int.0 }
""")
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert errors == [], [e.error_code for e in errors]
        refine_binds = [o for o in result.obligations if o.kind == "refine_bind"]
        assert refine_binds and all(
            o.status == "verified" for o in refine_binds
        ), [(o.kind, o.status) for o in result.obligations]
