"""Regression tests for #797 — @Float64 contracts via Z3's FloatingPoint sort.

Part of the #392 `smt.py` soundness audit (batch 3).  Before #797 the verifier
modelled `@Float64` as Z3 `Real` (exact, unbounded, no `NaN`/`Inf`), so it proved
postconditions that the IEEE-754 runtime then rejected — a Tier-1/Tier-3
disagreement.  #797 maps `@Float64` to `z3.FPSort(11, 53)` (double) with
round-nearest-ties-to-even, so:

  - an unsound relational contract (`x + 1.0 > x`, false at large `x` / `Inf` /
    `NaN`) is no longer proved at Tier 1 — Z3 finds the IEEE counterexample;
  - reflexive equality (`result == input`) is no longer proved, since `NaN`
    breaks `x == x`;
  - a genuinely-sound contract — one that excludes the offending edge with a
    `requires(!float_is_nan(...))` guard — still verifies at Tier 1 (this also
    exercises the now-sound `float_is_nan` / `float_is_infinite` translation to
    `fpIsNaN` / `fpIsInf`, previously deferred to Tier 3).

Written test-first: each FAILS on the pre-fix (Real-sort) verifier.
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


class TestFloat64FpSoundness797:
    def test_rounding_relation_not_proved(self) -> None:
        # The issue's probe: `result > input` for `input + 1.0` is FALSE at large
        # `x` (ULP >= 2, so `x + 1.0` rounds back to `x`), at `+Inf`, and at
        # `NaN`.  Z3 Real proved it for all inputs (unsound); the FP sort must
        # not — it flips to a counterexample (violated) or Tier 3.
        result = _verify("""
public fn inc(@Float64 -> @Float64)
  requires(true) ensures(@Float64.result > @Float64.0) effects(pure)
{ @Float64.0 + 1.0 }
""")
        ens = [o for o in result.obligations if o.kind == "ensures"]
        assert ens and all(o.status == "violated" for o in ens), [
            (o.kind, o.status) for o in result.obligations
        ]

    def test_reflexive_equality_not_proved(self) -> None:
        # `result == input` for the identity is FALSE at `NaN` (`NaN != NaN`).
        # Real's exact reflexivity proved it (unsound); FP must not.
        result = _verify("""
public fn idf(@Float64 -> @Float64)
  requires(true) ensures(@Float64.result == @Float64.0) effects(pure)
{ @Float64.0 }
""")
        ens = [o for o in result.obligations if o.kind == "ensures"]
        assert ens and all(o.status == "violated" for o in ens), [
            (o.kind, o.status) for o in result.obligations
        ]

    def test_nan_guarded_equality_still_verifies(self) -> None:
        # A genuinely-sound contract: with `!float_is_nan(input)` excluding the
        # only value that breaks reflexivity, `result == input` holds for every
        # remaining double (incl. `+/-Inf`, `+/-0`).  Must verify at Tier 1 —
        # which requires the `requires` guard to translate (`fpIsNaN`), so the
        # requires obligation flips tier3 -> verified too.
        result = _verify("""
public fn idf(@Float64 -> @Float64)
  requires(!float_is_nan(@Float64.0)) ensures(@Float64.result == @Float64.0) effects(pure)
{ @Float64.0 }
""")
        reqs = [o for o in result.obligations if o.kind == "requires"]
        ens = [o for o in result.obligations if o.kind == "ensures"]
        assert reqs and all(o.status == "verified" for o in reqs), [
            (o.kind, o.status) for o in result.obligations
        ]
        assert ens and all(o.status == "verified" for o in ens), [
            (o.kind, o.status) for o in result.obligations
        ]
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert errors == [], [e.error_code for e in errors]

    def test_float_predicate_translation_is_sound_and_complete(self) -> None:
        # `float_is_infinite(result) == float_is_infinite(input)` for the
        # identity is trivially true (same value).  Pre-fix `float_is_infinite`
        # was uninterpreted (Tier 3); the FP sort lets it translate to `fpIsInf`,
        # so the postcondition now verifies at Tier 1.
        result = _verify("""
public fn idf(@Float64 -> @Bool)
  requires(true) ensures(@Bool.result == float_is_infinite(@Float64.0)) effects(pure)
{ float_is_infinite(@Float64.0) }
""")
        ens = [o for o in result.obligations if o.kind == "ensures"]
        assert ens and all(o.status == "verified" for o in ens), [
            (o.kind, o.status) for o in result.obligations
        ]

    def test_special_value_constants_translate(self) -> None:
        # nan()/infinity() are FP constants now (#797), so a predicate over them
        # discharges at Tier 1 — they were uninterpreted under the Real model, so
        # `float_is_nan(nan())` dropped to Tier 3 (and regressed to a false E500
        # once `float_is_nan` alone became translatable).
        for src in (
            "public fn f(@Unit -> @Bool)\n"
            "  requires(true) ensures(@Bool.result) effects(pure)\n"
            "{ float_is_nan(nan()) }",
            "public fn g(@Unit -> @Bool)\n"
            "  requires(true) ensures(@Bool.result) effects(pure)\n"
            "{ float_is_infinite(infinity()) }",
        ):
            result = _verify(src)
            ens = [o for o in result.obligations if o.kind == "ensures"]
            assert ens and all(o.status == "verified" for o in ens), (
                src, [(o.kind, o.status) for o in result.obligations],
            )

    def test_modulo_matches_codegen_fmod_not_fp_rem(self) -> None:
        # #797 audit: Float64 `%` is codegen's truncated remainder
        # (`a - trunc(a/b)*b`, C fmod) — 5.0 % 3.0 == 2.0 — NOT Z3's fp.rem
        # (round-to-nearest remainder) which Python `%` emits and which gives
        # -1.0.  The verifier must prove the codegen value and REFUSE fp.rem's.
        ok = _verify("""
public fn m(@Unit -> @Float64)
  requires(true) ensures(@Float64.result == 2.0) effects(pure)
{ 5.0 % 3.0 }
""")
        ok_ens = [o for o in ok.obligations if o.kind == "ensures"]
        assert ok_ens and all(o.status == "verified" for o in ok_ens), [
            (o.kind, o.status) for o in ok.obligations
        ]
        bad = _verify("""
public fn m(@Unit -> @Float64)
  requires(true) ensures(@Float64.result == 0.0 - 1.0) effects(pure)
{ 5.0 % 3.0 }
""")
        bad_ens = [o for o in bad.obligations if o.kind == "ensures"]
        assert bad_ens and all(o.status != "verified" for o in bad_ens), [
            (o.kind, o.status) for o in bad.obligations
        ]

    def test_mixed_float64_int_comparison_rejected_at_check(self) -> None:
        # #797 regression guard (PR #806 review): `@Float64 < @Int` is a clean
        # E142 type error at CHECK time (Vera has no implicit numeric coercion —
        # the arithmetic (E141) and equality (E142) arms already reject mixed
        # Float64/Int).  Before the fix it type-checked, then raised an uncaught
        # Z3 sort mismatch in the verifier once Float64 became an FP sort (no
        # Int<->FP coercion masked it).
        src = """
private fn cmp(@Float64, @Int -> @Bool)
  requires(true) ensures(true) effects(pure)
{ @Float64.0 < @Int.0 }
"""
        diags, _arts = typecheck_with_artifacts(parse_to_ast(src), src)
        errors = [d for d in diags if d.severity == "error"]
        assert any(e.error_code == "E142" for e in errors), [
            e.error_code for e in errors
        ]

    def test_signed_zero_equality_is_ieee_fpeq(self) -> None:
        # #797 (PR #806 review): `==` is IEEE fpEQ, so `+0.0 == -0.0` is TRUE.
        # `(0.0 - 1.0) * 0.0` is `-0.0`; `-0.0 == 0.0` proves at Tier 1.  This is
        # the discriminator a structural `=` regression would break (under `=`,
        # `+0.0` and `-0.0` have distinct bit patterns and compare unequal) and
        # that the NaN reflexivity test does not cover.
        result = _verify("""
public fn f(@Unit -> @Bool)
  requires(true) ensures(@Bool.result) effects(pure)
{ ((0.0 - 1.0) * 0.0) == 0.0 }
""")
        ens = [o for o in result.obligations if o.kind == "ensures"]
        assert ens and all(o.status == "verified" for o in ens), [
            (o.kind, o.status) for o in result.obligations
        ]

    def test_modulo_edge_cases_match_runtime(self) -> None:
        # #797 (PR #806 review): `%`-by-zero is NaN (codegen `a - trunc(a/0)*0` =
        # `a - Inf*0` = NaN), and a large-magnitude case pins the NAIVE truncated
        # remainder the codegen emits — `5.0 % 0.1` is `0.0` (`trunc(5.0/0.1)` =
        # 50, `5.0 - 50*0.1` = 0.0), NOT bit-exact C fmod (~0.0999).  The earlier
        # `5.0 % 3.0` case can't catch this (there naive and C fmod coincide).
        by_zero = _verify("""
public fn f(@Unit -> @Bool)
  requires(true) ensures(@Bool.result) effects(pure)
{ float_is_nan(5.0 % 0.0) }
""")
        bz = [o for o in by_zero.obligations if o.kind == "ensures"]
        assert bz and all(o.status == "verified" for o in bz), [
            (o.kind, o.status) for o in by_zero.obligations
        ]
        large = _verify("""
public fn f(@Unit -> @Float64)
  requires(true) ensures(@Float64.result == 0.0) effects(pure)
{ 5.0 % 0.1 }
""")
        lg = [o for o in large.obligations if o.kind == "ensures"]
        assert lg and all(o.status == "verified" for o in lg), [
            (o.kind, o.status) for o in large.obligations
        ]
