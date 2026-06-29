"""Regression tests for #813 — @Nat -> @Int widening coercion obligations.

Part of the #392 `smt.py` soundness audit, and the dual of the #552 `nat_bind`
narrowing obligation.  `@Nat` is u64 and `@Int` is i64, and `@Nat <: @Int`, so a
`@Nat` value silently widens to `@Int` at coercion sites (return, call-arg, let,
ctor-field, …).  But a `@Nat` in (i64.MAX, u64.MAX] bit-reinterprets when widened
(u64.MAX -> -1), while the verifier modelled the unbounded non-negative
mathematical value — so it proved postconditions the runtime then violated:

    public fn widen(@Nat -> @Int)
      requires(true) ensures(@Int.result >= 0) effects(pure)
    { @Nat.0 }

`vera verify` proved `result >= 0` (a `@Nat` is non-negative), yet
`widen(u64.MAX)` returns -1 at runtime — a Tier-1/runtime divergence.

Per the #813 decision (mirroring #798 overflow and #552 narrowing): every
`@Nat -> @Int` coercion now emits a ``nat_to_int_coerce`` obligation that the
value is `<= i64.MAX`.  It discharges at Tier 1 when the value is provably in
range, raises E530 when provably out of range, else falls to Tier-3 (a runtime
coercion-range trap guards it).  The postcondition stays Tier-1 *sound* because
the function now traps on an out-of-range widen before it can return a
reinterpreted value.

Written test-first: the first FAILS on the pre-fix verifier, where NO
``nat_to_int_coerce`` obligation is emitted at all (the widen is silently
assumed exact).
"""

from __future__ import annotations

from vera.checker import typecheck_with_artifacts
from vera.parser import parse_to_ast
from vera.verifier import VerifyResult, verify


def _verify(source: str) -> VerifyResult:
    ast = parse_to_ast(source)
    _diags, arts = typecheck_with_artifacts(ast, source)
    return verify(
        ast, source,
        expr_types=arts.expr_semantic_types,
        expr_target_types=arts.expr_target_types,
    )


_KIND = "nat_to_int_coerce"


class TestNatToIntWideningObligations813:
    def test_widen_unbounded_emits_undischarged_coerce_obligation(self) -> None:
        # An unbounded @Nat returned as @Int can exceed i64.MAX (u64.MAX -> -1),
        # so a nat_to_int_coerce obligation must be emitted and left UNdischarged
        # (Tier-3, runtime-guarded).  Pre-fix: no such obligation — widen assumed
        # exact.
        result = _verify("""
public fn widen(@Nat -> @Int)
  requires(true) ensures(@Int.result >= 0) effects(pure)
{ @Nat.0 }
""")
        co = [o for o in result.obligations if o.kind == _KIND]
        assert len(co) == 1, [(o.kind, o.status) for o in result.obligations]
        assert co[0].status == "tier3", [(o.kind, o.status) for o in co]

    def test_coerce_obligation_discharged_when_value_bounded(self) -> None:
        # A @Nat provably <= i64.MAX widens exactly, so the coercion obligation
        # discharges at Tier 1 (exercises the discharge path, not just Tier-3).
        result = _verify("""
public fn widen_small(@Nat -> @Int)
  requires(@Nat.0 < 100) ensures(true) effects(pure)
{ @Nat.0 }
""")
        co = [o for o in result.obligations if o.kind == _KIND]
        assert len(co) == 1, [(o.kind, o.status) for o in result.obligations]
        assert co[0].status == "verified", [(o.kind, o.status) for o in co]

    def test_coerce_obligation_violated_when_provably_out_of_range(self) -> None:
        # The loud-error arm: when the @Nat value provably exceeds i64.MAX, the
        # coercion is 'violated' and E530 is raised *before* codegen — the analog
        # of nat_bind's E503 and int_overflow's E528.  A regression that silently
        # downgraded this to Tier-3 would re-open the soundness hole AND pass the
        # discharge/tier3 tests above, so it is pinned explicitly.  2**63 = the
        # smallest @Nat strictly above i64.MAX (= 2**63 - 1).
        result = _verify("""
public fn over(@Nat -> @Int)
  requires(@Nat.0 >= 9223372036854775808) ensures(true) effects(pure)
{ @Nat.0 }
""")
        co = [o for o in result.obligations if o.kind == _KIND]
        assert len(co) == 1, [(o.kind, o.status) for o in result.obligations]
        assert co[0].status == "violated", co[0].status
        assert co[0].error_code == "E530", co[0].error_code
        assert any(d.error_code == "E530" for d in result.diagnostics), [
            d.error_code for d in result.diagnostics
        ]

    def test_int_to_int_return_emits_no_coerce_obligation(self) -> None:
        # Control: a plain @Int return is not a widening — no coercion obligation
        # (guards against a walker that fires on every return position).
        result = _verify("""
public fn ident(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 }
""")
        assert [o for o in result.obligations if o.kind == _KIND] == []
