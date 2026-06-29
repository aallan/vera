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


class TestNatToIntWideningSites813:
    """The widening obligation fires at every coercion site, not just the
    return position (#813 stage 2b — the dual of #552's binding-site walker)."""

    def test_call_argument_widening(self) -> None:
        # @Nat.0 passed to an @Int formal widens at the call site.  The call
        # result is @Int (takes_int returns @Int), so the only widening is the
        # argument, not the return — exactly one coercion obligation, Tier-3.
        result = _verify("""
public fn takes_int(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 }

public fn caller(@Nat -> @Int)
  requires(true) ensures(true) effects(pure)
{ takes_int(@Nat.0) }
""")
        co = [o for o in result.obligations if o.kind == _KIND]
        assert len(co) == 1, [(o.kind, o.status) for o in result.obligations]
        assert co[0].status == "tier3", [(o.kind, o.status) for o in co]

    def test_let_binding_widening(self) -> None:
        # `let @Int = @Nat.0` widens the @Nat RHS into the @Int slot.  The body
        # then returns @Int.0 (@Int — no return widening), so exactly one
        # coercion obligation at the let site.
        result = _verify("""
public fn f(@Nat -> @Int)
  requires(true) ensures(true) effects(pure)
{ let @Int = @Nat.0; @Int.0 }
""")
        co = [o for o in result.obligations if o.kind == _KIND]
        assert len(co) == 1, [(o.kind, o.status) for o in result.obligations]
        assert co[0].status == "tier3", [(o.kind, o.status) for o in co]

    def test_call_argument_widening_discharged_when_bounded(self) -> None:
        # A bounded @Nat argument discharges the call-site widening at Tier 1.
        result = _verify("""
public fn takes_int(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 }

public fn caller(@Nat -> @Int)
  requires(@Nat.0 < 100) ensures(true) effects(pure)
{ takes_int(@Nat.0) }
""")
        co = [o for o in result.obligations if o.kind == _KIND]
        assert len(co) == 1, [(o.kind, o.status) for o in result.obligations]
        assert co[0].status == "verified", [(o.kind, o.status) for o in co]


class TestNatToIntWideningCallResult813:
    """#813 step 5 — a @Nat-returning *call* result widened to @Int must obligate
    too, matching the codegen guard (codegen resolves the callee robustly via
    ``_infer_fncall_vera_type``).  The verifier's ``_result_is_nat`` FnCall branch
    was conservative (``_resolved_type_of`` only); the checker's semantic
    side-table is sparse for ordinary calls, so the call result classified
    not-@Nat and ``verify`` silently proved a postcondition codegen then guards at
    runtime — a verifier↔codegen divergence the differential test now forbids."""

    def test_nat_returning_call_widened_at_return(self) -> None:
        # widen_call returns a @Nat-typed call result (make_nat -> @Nat) through
        # an @Int return type.  The result is unbounded, so the coercion is
        # Tier-3 (runtime-guarded) — but it MUST be obligated, not silently
        # assumed exact.  Pre-step-5: no obligation (conservative FnCall branch).
        result = _verify("""
public fn make_nat(@Int -> @Nat)
  requires(true) ensures(true) effects(pure)
{ 5 }

public fn widen_call(@Int -> @Int)
  requires(true) ensures(@Int.result >= 0) effects(pure)
{ make_nat(@Int.0) }
""")
        co = [o for o in result.obligations if o.kind == _KIND]
        assert len(co) == 1, [(o.kind, o.status) for o in result.obligations]
        assert co[0].status == "tier3", [(o.kind, o.status) for o in co]


class TestNatToIntWideningConstructorField813:
    """#813 stage 2c — @Nat -> @Int widening into an @Int constructor field,
    found by the completeness audit (workflow wie2dpfln) and confirmed by
    `vera run`: a @Nat stored into an @Int field and later extracted as @Int
    silently reinterprets above i64.MAX (u64.MAX -> -1)."""

    def test_concrete_int_field_tier3_guarded(self) -> None:
        # `WrapInt(Int)` field receiving @Nat.0 — codegen guards the concrete
        # @Int field (layout `int_fields`), so an unbounded @Nat is Tier-3
        # (runtime-guarded), not silently assumed exact.
        result = _verify("""
private data WrapInt { WrapInt(Int) }
public fn ctor_field(@Nat -> @Int)
  requires(true) ensures(true) effects(pure)
{ let @WrapInt = WrapInt(@Nat.0); match @WrapInt.0 { WrapInt(@Int) -> @Int.0 } }
""")
        co = [o for o in result.obligations if o.kind == _KIND]
        assert len(co) == 1, [(o.kind, o.status) for o in result.obligations]
        assert co[0].status == "tier3", [(o.kind, o.status) for o in co]

    def test_concrete_int_field_discharged_when_bounded(self) -> None:
        result = _verify("""
private data WrapInt { WrapInt(Int) }
public fn ctor_field(@Nat -> @Int)
  requires(@Nat.0 < 100) ensures(true) effects(pure)
{ let @WrapInt = WrapInt(@Nat.0); match @WrapInt.0 { WrapInt(@Int) -> @Int.0 } }
""")
        co = [o for o in result.obligations if o.kind == _KIND]
        assert len(co) == 1, [(o.kind, o.status) for o in result.obligations]
        assert co[0].status == "verified", [(o.kind, o.status) for o in co]

    def test_generic_int_field_unguarded_disclosed_E531(self) -> None:
        # `Some(@Nat.0)` into `Option<Int>` — the generic field erases to i64
        # with no per-field mono metadata, so codegen cannot guard it.  The
        # widening is disclosed UNGUARDED (E531) rather than silently assumed
        # exact or claiming a runtime check it never gets (the dual of the
        # generic-@Nat-field E504 narrowing case).
        result = _verify("""
public fn opt_field(@Nat -> @Int)
  requires(true) ensures(true) effects(pure)
{ let @Option<Int> = Some(@Nat.0); match @Option<Int>.0 { Some(@Int) -> @Int.0, None -> 0 } }
""")
        co = [o for o in result.obligations if o.kind == _KIND]
        assert len(co) == 1, [(o.kind, o.status) for o in result.obligations]
        assert co[0].status == "tier3_unguarded", [(o.kind, o.status) for o in co]
        assert co[0].error_code == "E531", co[0].error_code
        assert any(d.error_code == "E531" for d in result.diagnostics), [
            d.error_code for d in result.diagnostics
        ]

    def test_adt_subpattern_nat_field_extracted_as_int_tier3(self) -> None:
        # `match @Box.0 { Box(@Int) -> }` on a `Box(Nat)` extracts the @Nat
        # field into an @Int slot — codegen guards the extraction
        # (`layout.nat_fields`), so the unbounded widening is Tier-3.
        result = _verify("""
private data Box { Box(Nat) }
public fn box_extract(@Nat -> @Int)
  requires(true) ensures(true) effects(pure)
{ let @Box = Box(@Nat.0); match @Box.0 { Box(@Int) -> @Int.0 } }
""")
        co = [o for o in result.obligations if o.kind == _KIND]
        assert len(co) == 1, [(o.kind, o.status) for o in result.obligations]
        assert co[0].status == "tier3", [(o.kind, o.status) for o in co]

    def test_tuple_construction_component_unguarded_disclosed_E531(self) -> None:
        # `Tuple(@Nat.0, ...)` widens a @Nat into an @Int tuple component.
        # Codegen does not component-guard a tuple at construction (the boundary
        # guard is a separate site), so the widening is disclosed UNGUARDED
        # (E531), mirroring the @Nat tuple-component narrowing's E504.
        result = _verify("""
public fn tup_construct(@Nat -> @Int)
  requires(true) ensures(true) effects(pure)
{ let @Tuple<Int, Int> = Tuple(@Nat.0, 0); match @Tuple<Int, Int>.0 { Tuple(@Int, @Int) -> @Int.1 } }
""")
        co = [o for o in result.obligations if o.kind == _KIND]
        assert co, [(o.kind, o.status) for o in result.obligations]
        assert all(o.status == "tier3_unguarded" for o in co), [
            (o.kind, o.status) for o in co
        ]
        assert any(d.error_code == "E531" for d in result.diagnostics), [
            d.error_code for d in result.diagnostics
        ]
