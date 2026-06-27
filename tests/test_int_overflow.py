"""Regression tests for #798 — @Int/@Nat arithmetic overflow obligations.

Part of the #392 `smt.py` soundness audit.  Before #798 the verifier modelled
`@Int`/`@Nat` as Z3's *unbounded* integers, so `+`/`-`/`*` were treated as total
operations — it proved contracts the i64/u64 runtime then violated under
two's-complement wraparound.  The canonical probe:

    public fn inc(@Int -> @Int)
      requires(true) ensures(@Int.result > @Int.0) effects(pure)
    { @Int.0 + 1 }

`vera verify` proved `result > input` for all inputs, yet `inc(MAX_i64)` traps
(`x + 1` wraps to `MIN_i64 < x`).

Per the #798 decision (overflow is a *trapping* partial operation, consistent
with `@Nat` underflow and signed-div `MIN/-1`), every `+`/`-`/`*` on
`@Int`/`@Nat` now emits an ``int_overflow`` obligation — the analog of
``nat_sub`` / ``div_zero``.  It discharges at Tier 1 when operand bounds prove
the result stays in range, else falls to Tier-3 (a runtime overflow trap guards
it).  The postcondition itself stays Tier-1 sound, because the function now traps
on overflow before it can return a wrapped value.

Written test-first: each FAILS on the pre-fix verifier, where NO ``int_overflow``
obligation is emitted at all (overflow is silently assumed).
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


class TestIntOverflowObligations798:
    def test_int_add_unbounded_emits_undischarged_overflow_obligation(self) -> None:
        # `x + 1` on an unbounded @Int overflows i64 at MAX_i64, so an
        # int_overflow obligation must be emitted and left UNdischarged (Tier-3,
        # runtime-guarded).  Pre-fix: no such obligation — overflow assumed.
        result = _verify("""
public fn inc(@Int -> @Int)
  requires(true) ensures(@Int.result > @Int.0) effects(pure)
{ @Int.0 + 1 }
""")
        ovf = [o for o in result.obligations if o.kind == "int_overflow"]
        # Exactly one arithmetic site → exactly one int_overflow obligation; a
        # walker that double-recorded the site would slip past an "at least one"
        # check, so pin the exact count (CR #809).
        assert len(ovf) == 1, [(o.kind, o.status) for o in result.obligations]
        assert ovf[0].status == "tier3", [(o.kind, o.status) for o in ovf]

    def test_nat_add_unbounded_emits_undischarged_overflow_obligation(self) -> None:
        # Same shape at the u64 ceiling for @Nat.
        result = _verify("""
public fn inc(@Nat -> @Nat)
  requires(true) ensures(@Nat.result > @Nat.0) effects(pure)
{ @Nat.0 + 1 }
""")
        ovf = [o for o in result.obligations if o.kind == "int_overflow"]
        assert len(ovf) == 1, [(o.kind, o.status) for o in result.obligations]
        assert ovf[0].status == "tier3", [(o.kind, o.status) for o in ovf]

    def test_overflow_obligation_discharged_when_operands_bounded(self) -> None:
        # Bounded operands → result provably in i64 range → the overflow
        # obligation discharges at Tier 1 (exercises the discharge path, not just
        # the Tier-3 fallback).  A default that happens to skip emission would
        # leave `ovf` empty and fail here too.
        result = _verify("""
public fn add_small(@Int, @Int -> @Int)
  requires(@Int.0 >= 0 && @Int.0 < 100 && @Int.1 >= 0 && @Int.1 < 100)
  ensures(true) effects(pure)
{ @Int.0 + @Int.1 }
""")
        ovf = [o for o in result.obligations if o.kind == "int_overflow"]
        assert len(ovf) == 1, [(o.kind, o.status) for o in result.obligations]
        assert ovf[0].status == "verified", [(o.kind, o.status) for o in ovf]

    def test_overflow_obligation_violated_when_provably_out_of_range(self) -> None:
        # The loud-error third arm of the two-check, untested until now: when the
        # operands provably force the result out of range, the int_overflow
        # obligation is 'violated' and a compile error (E528) is raised *before*
        # codegen — the analog of index_bounds' E527 and nat_sub's E502.  A
        # regression that silently downgraded this arm to Tier 3 would re-open the
        # #798-class soundness hole AND pass the discharge/tier3 tests above, so
        # it is pinned explicitly here.  @Int at the i64 ceiling.
        result = _verify("""
public fn over(@Int -> @Int)
  requires(@Int.0 >= 9223372036854775807) ensures(true) effects(pure)
{ @Int.0 + 1 }
""")
        ovf = [o for o in result.obligations if o.kind == "int_overflow"]
        assert len(ovf) == 1, [(o.kind, o.status) for o in result.obligations]
        assert ovf[0].status == "violated", ovf[0].status
        assert ovf[0].error_code == "E528", ovf[0].error_code
        assert any(d.error_code == "E528" for d in result.diagnostics), [
            d.error_code for d in result.diagnostics
        ]

    def test_nat_overflow_obligation_violated_at_u64_ceiling(self) -> None:
        # The @Nat (u64) ceiling variant of the E528 path.
        result = _verify("""
public fn over(@Nat -> @Nat)
  requires(@Nat.0 >= 18446744073709551615) ensures(true) effects(pure)
{ @Nat.0 + 1 }
""")
        ovf = [o for o in result.obligations if o.kind == "int_overflow"]
        assert len(ovf) == 1, [(o.kind, o.status) for o in result.obligations]
        assert ovf[0].status == "violated", ovf[0].status
        assert ovf[0].error_code == "E528", ovf[0].error_code

    def test_nat_subtraction_excluded_from_overflow_obligation(self) -> None:
        # The SUB+Nat exclusion checked at the REAL verifier gate (not the
        # differential's re-derived helper, which can't catch an exclusion
        # desync): a @Nat - @Nat site is the nat_sub underflow obligation (E502),
        # never an int_overflow.  Pins the exclusion against a regression that
        # started high-overflow-guarding @Nat subtraction.
        result = _verify("""
public fn sub(@Nat, @Nat -> @Nat)
  requires(@Nat.1 >= @Nat.0) ensures(true) effects(pure)
{ @Nat.1 - @Nat.0 }
""")
        kinds = [o.kind for o in result.obligations]
        assert "int_overflow" not in kinds, [
            (o.kind, o.status) for o in result.obligations
        ]
        assert "nat_sub" in kinds, [
            (o.kind, o.status) for o in result.obligations
        ]
