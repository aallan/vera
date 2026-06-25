"""Regression tests for the #392 smt.py / verifier soundness audit — batch 1.

Three confirmed Tier-1/Tier-3 disagreements, fixed together:
  #799 — signed division/modulo must truncate toward zero (Vera `i64.div_s` /
         `i64.rem_s`), not follow Z3's Euclidean `div`/`mod`.
  #800 — a body `assert(P)` must generate a Tier-1 obligation (prove `P`), not
         be silently ignored (spec §6.2.5).
  #801 — divisions appearing in contract predicates must get a `div_zero`
         obligation, mirroring body divisions (#680).

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
