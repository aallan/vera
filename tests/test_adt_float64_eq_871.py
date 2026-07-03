"""Regression tests for #871 — ADT equality with Float64 fields must model
the runtime's per-field ``f64.eq``, not Z3's structural datatype ``=``.

Follow-up to the #797/#392 lineage: #797 mapped a *bare* ``@Float64`` operand
to Z3's FP sort with ``fpEQ`` (IEEE: ``NaN != NaN``, ``+0.0 == -0.0``), but an
FP value nested in a datatype is a datatype term, so ``==``/``!=`` fell to
structural SMT ``=`` — under which ``NaN = NaN`` holds and ``+0.0 = -0.0``
does not, both disagreeing with the ``f64.eq`` the #870 structural-Eq codegen
emits per Float64 field.  The canonical ensures+run differential: ``vera
verify`` proved ADT-NaN reflexivity Tier-1 while ``vera run`` trapped with a
postcondition violation.

The fix decomposes datatype equality per-field (``fpEQ`` for FP fields,
recursing into nested FP-containing datatypes) when the operand sort
transitively contains Float64, and demotes to Tier 3 when the FP-containing
datatype is recursive (no finite expansion).  Non-FP datatype equality keeps
structural ``=`` — it agrees with the runtime there.

Written test-first: each test marked RED below FAILS on the pre-fix verifier.
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


def _ensures(result: VerifyResult) -> list:
    return [o for o in result.obligations if o.kind == "ensures"]


class TestAdtFloat64Eq871:
    def test_nan_field_reflexivity_not_proved(self) -> None:
        # RED: the issue's probe.  `@W.0 == @W.0` with a Float64 field is FALSE
        # at MkW(NaN) under the runtime's per-field f64.eq; structural datatype
        # `=` proved it Tier-1 (NaN = NaN under datatype congruence).  The
        # per-field fpEQ decomposition must surface the NaN counterexample.
        result = _verify("""
private data W {
  MkW(Float64)
}

public fn refl(@W -> @Bool)
  requires(true)
  ensures(@Bool.result == true)
  effects(pure)
{
  @W.0 == @W.0
}
""")
        ens = _ensures(result)
        assert ens and all(o.status == "violated" for o in ens), [
            (o.kind, o.status) for o in result.obligations
        ]

    def test_nan_field_inequality_not_disproved(self) -> None:
        # RED: the NEQ direction.  `@W.0 != @W.0` is TRUE at MkW(NaN) under the
        # runtime (`!(f64.eq)`); structural `=` proved `ensures(result ==
        # false)` Tier-1.  Not(fpEQ) must surface the NaN counterexample.
        result = _verify("""
private data W {
  MkW(Float64)
}

public fn irrefl(@W -> @Bool)
  requires(true)
  ensures(@Bool.result == false)
  effects(pure)
{
  @W.0 != @W.0
}
""")
        ens = _ensures(result)
        assert ens and all(o.status == "violated" for o in ens), [
            (o.kind, o.status) for o in result.obligations
        ]

    def test_signed_zero_field_equality_proved(self) -> None:
        # RED (the other unsound direction): `MkW(-0.0) == MkW(+0.0)` is TRUE
        # at runtime (f64.eq: +0.0 == -0.0) but structural `=` DISPROVED it
        # (distinct FP values), emitting a false E500 against a contract the
        # runtime satisfies.  fpEQ decomposition must prove it Tier-1.  The
        # unused @W param keeps the W sort in scope for the ctor translation.
        result = _verify("""
private data W {
  MkW(Float64)
}

public fn zeq(@W -> @Bool)
  requires(true)
  ensures(@Bool.result == true)
  effects(pure)
{
  MkW((0.0 - 1.0) * 0.0) == MkW(0.0)
}
""")
        ens = _ensures(result)
        assert ens and all(o.status == "verified" for o in ens), [
            (o.kind, o.status) for o in result.obligations
        ]
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert errors == [], [e.error_code for e in errors]

    def test_nested_float_adt_reflexivity_not_proved(self) -> None:
        # RED: the FP field sits one datatype level down (B wraps W wraps
        # Float64).  The contains-FP walk must be transitive and the
        # decomposition must recurse into the nested datatype.
        result = _verify("""
private data W {
  MkW(Float64)
}

private data B {
  MkB(W, Int)
}

public fn refl(@B -> @Bool)
  requires(true)
  ensures(@Bool.result == true)
  effects(pure)
{
  @B.0 == @B.0
}
""")
        ens = _ensures(result)
        assert ens and all(o.status == "violated" for o in ens), [
            (o.kind, o.status) for o in result.obligations
        ]

    def test_recursive_float_adt_demotes_to_tier3(self) -> None:
        # RED: a recursive FP-containing ADT has no finite per-field expansion,
        # and structural `=` falsely proved reflexivity (runtime traps at
        # FCons(NaN, FNil)).  Soundness over completeness (DESIGN.md): the
        # obligation must demote to an honest Tier-3 runtime check — LOUDLY, in
        # the tier summary — not stay a false Tier-1 proof.
        result = _verify("""
private data FList {
  FNil,
  FCons(Float64, FList)
}

public fn refl(@FList -> @Bool)
  requires(true)
  ensures(@Bool.result == true)
  effects(pure)
{
  @FList.0 == @FList.0
}
""")
        ens = _ensures(result)
        assert ens and all(o.status in ("tier3", "timeout") for o in ens), [
            (o.kind, o.status) for o in result.obligations
        ]
        assert result.summary.tier3_runtime >= 1, result.summary

    def test_mixed_constructor_sum_type(self) -> None:
        # PR #879 review: every other FP ADT in this battery has exactly ONE
        # FP-carrying constructor, so the multi-constructor `z3.Or(*arms)`
        # branch of `_datatype_value_eq` — with its per-arm recognizer guards —
        # was otherwise unexercised.  Cross-constructor inequality (distinct
        # tags) must stay a Tier-1 proof: a mis-guarded arm (e.g. a dropped
        # recognizer conjunct) leaves the wrong constructor's accessors
        # unconstrained and loses exactly this proof.  The @M param keeps the
        # M sort in scope for the ctor translation.
        cross = _verify("""
private data M {
  MA(Float64),
  MB(Int)
}

public fn f(@M -> @Bool)
  requires(true)
  ensures(@Bool.result == false)
  effects(pure)
{
  MA(nan()) == MB(0)
}
""")
        cross_ens = _ensures(cross)
        assert cross_ens and all(o.status == "verified" for o in cross_ens), [
            (o.kind, o.status) for o in cross.obligations
        ]
        errors = [d for d in cross.diagnostics if d.severity == "error"]
        assert errors == [], [e.error_code for e in errors]
        # Same-constructor reflexivity with the NaN edge excluded stays Tier-1
        # under the multi-constructor decomposition (no over-demotion for sum
        # types).
        guarded = _verify("""
private data M {
  MA(Float64),
  MB(Int)
}

public fn f(@M, @Float64 -> @Bool)
  requires(!float_is_nan(@Float64.0))
  ensures(@Bool.result == true)
  effects(pure)
{
  MA(@Float64.0) == MA(@Float64.0)
}
""")
        guarded_ens = _ensures(guarded)
        assert guarded_ens and all(
            o.status == "verified" for o in guarded_ens
        ), [(o.kind, o.status) for o in guarded.obligations]

    def test_recursive_float_adt_neq_demotes_to_tier3(self) -> None:
        # PR #879 review: the NEQ arm's recursive-demotion path (`eq is None`
        # -> `return None`) was unpinned — the recursive `==` test above is
        # the only recursive case.  `!=` on a recursive FP-containing ADT must
        # take the same honest, loud Tier-3 demotion, not a false proof via
        # structural `=` (under which `@FList.0 != @FList.0` is provably false
        # while the runtime's per-field f64.eq makes it TRUE at
        # FCons(NaN, FNil)).
        result = _verify("""
private data FList {
  FNil,
  FCons(Float64, FList)
}

public fn irrefl(@FList -> @Bool)
  requires(true)
  ensures(@Bool.result == false)
  effects(pure)
{
  @FList.0 != @FList.0
}
""")
        ens = _ensures(result)
        assert ens and all(o.status in ("tier3", "timeout") for o in ens), [
            (o.kind, o.status) for o in result.obligations
        ]
        assert result.summary.tier3_runtime >= 1, result.summary

    def test_guarded_float_adt_equality_still_tier1(self) -> None:
        # No-over-demotion pin (GREEN on main, guards the fix): with NaN
        # excluded, `MkW(x) == MkW(x)` holds for every remaining double and
        # must stay a Tier-1 proof under the fpEQ decomposition — a blanket
        # "any FP-containing ADT goes Tier 3" fix would break this.
        result = _verify("""
private data W {
  MkW(Float64)
}

public fn f(@W, @Float64 -> @Bool)
  requires(!float_is_nan(@Float64.0))
  ensures(@Bool.result == true)
  effects(pure)
{
  MkW(@Float64.0) == MkW(@Float64.0)
}
""")
        ens = _ensures(result)
        assert ens and all(o.status == "verified" for o in ens), [
            (o.kind, o.status) for o in result.obligations
        ]

    def test_nonfloat_adt_equality_stays_tier1(self) -> None:
        # No-over-demotion pin (GREEN on main, guards the fix): structural `=`
        # agrees with the runtime when no Float64 is inside — both a flat and a
        # recursive non-FP ADT must keep their Tier-1 reflexivity proof.
        for src in (
            """
private data P {
  MkP(Int, Int)
}

public fn refl(@P -> @Bool)
  requires(true)
  ensures(@Bool.result == true)
  effects(pure)
{
  @P.0 == @P.0
}
""",
            """
private data IL {
  INil,
  ICons(Int, IL)
}

public fn refl(@IL -> @Bool)
  requires(true)
  ensures(@Bool.result == true)
  effects(pure)
{
  @IL.0 == @IL.0
}
""",
        ):
            result = _verify(src)
            ens = _ensures(result)
            assert ens and all(o.status == "verified" for o in ens), (
                src, [(o.kind, o.status) for o in result.obligations],
            )
