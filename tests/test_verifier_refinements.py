"""Tests for vera.verifier — refinements (refined param sorts, refinement-predicate translation and verification (#746)).

Split from tests/test_verifier.py (#839). Shared helpers live in tests/verifier_helpers.py.
"""
from __future__ import annotations

import pathlib

from typing import ClassVar

import pytest

from vera import ast as ast_mod
from vera.parser import parse_to_ast

from tests.verifier_helpers import (
    _verify,
    _verify_err,
    _verify_ok,
)


class TestRefinedTypeParamSorts:
    """Refinement types over Bool/String/Float64 use the correct Z3 sort."""

    def test_refined_string_param_string_predicate_tier1(self) -> None:
        """RefinedType(STRING) param uses SeqSort — string predicates resolve to Tier 1.

        Without the RefinedType branch in _is_string_type, the parameter falls through to
        declare_int (IntSort) and the string predicate uses an uninterpreted function, which
        cannot prove it even with the requires assumption (Tier 3).  With the fix the param
        is a SeqSort and Z3's PrefixOf proves the ensures from the requires (Tier 1).  Uses
        string_starts_with (a Tier-1 predicate); string_length now defers to Tier 3 for
        non-literal arguments (#802), so it is no longer the right probe for SeqSort wiring.
        """
        result = _verify("""
type HttpsUrl = { @String | string_starts_with(@String.0, "https://") };

private fn pass_through(@HttpsUrl -> @Bool)
  requires(string_starts_with(@HttpsUrl.0, "https://"))
  ensures(@Bool.result)
  effects(pure)
{
  string_starts_with(@HttpsUrl.0, "https://")
}
""")
        assert result.summary.tier3_runtime == 0

    def test_refined_float64_param_verifies_cleanly(self) -> None:
        """RefinedType(FLOAT64) param uses the FP sort — function verifies without sort errors.

        Without the RefinedType branch in _is_float64_type, the parameter falls through to
        declare_int (IntSort). With the fix, declare_float64 (FP sort, #797) is used, matching the
        behaviour of a plain @Float64 parameter.
        """
        result = _verify("""
type PosFloat = { @Float64 | true };

private fn identity(@PosFloat -> @Float64)
  requires(true)
  ensures(true)
  effects(pure)
{
  @PosFloat.0
}
""")
        assert result.summary.tier3_runtime == 0

    def test_refined_bool_param_verifies_cleanly(self) -> None:
        """RefinedType(BOOL) param uses BoolSort — function verifies without sort errors.

        Without the RefinedType branch in _is_bool_type, the parameter falls through to
        declare_int (IntSort). With the fix, declare_bool (BoolSort) is used so that bool
        contracts referencing the parameter are correctly translated by Z3.
        requires(@Flag.0) and ensures(@Bool.result) both reference the Bool value as a
        boolean expression — this would crash or misverify with IntSort.
        """
        result = _verify("""
type Flag = { @Bool | true };

private fn identity(@Flag -> @Bool)
  requires(@Flag.0)
  ensures(@Bool.result)
  effects(pure)
{
  @Flag.0
}
""")
        assert result.summary.tier3_runtime == 0


class TestRefinementPredicateTranslation:
    """#746 Step 1 — the predicate-translation primitive substitutes the
    refinement binder (`@<base>.0`) with the value being refined, against a
    fresh slot env keyed on the base type-name (not the alias)."""

    @staticmethod
    def _predicate_of(source: str):
        """Extract the first RefinementType's predicate AST from *source*."""
        import vera.ast as A
        mod = parse_to_ast(source)
        found: list = []

        def walk(node: object) -> None:
            if isinstance(node, A.RefinementType):
                found.append(node)
            for f in getattr(node, "__dataclass_fields__", {}):
                v = getattr(node, f)
                if isinstance(v, A.Node):
                    walk(v)
                elif isinstance(v, (list, tuple)):
                    for x in v:
                        if isinstance(x, A.Node):
                            walk(x)

        walk(mod)
        assert found, "no RefinementType in source"
        return found[0].predicate

    def test_substitutes_binder_with_value(self) -> None:
        """`{ @Int | @Int.0 > 0 }` translated with value `v` yields `v > 0`:
        substituting v=5 simplifies True, v=-1 False — proving the binder is
        actually bound (a wrong push-key would leave it unconstrained and
        silently 'verify')."""
        import z3
        from vera.smt import SmtContext
        from vera.types import RefinedType, INT
        from vera.verifier import ContractVerifier

        pred = self._predicate_of("type PosInt = { @Int | @Int.0 > 0 };\n")
        refined = RefinedType(INT, pred)
        smt = SmtContext()
        v = z3.Int("v")
        result = ContractVerifier._translate_refined_predicate(smt, refined, v)
        assert result is not None
        assert z3.is_true(z3.simplify(z3.substitute(result, (v, z3.IntVal(5)))))
        assert z3.is_false(z3.simplify(z3.substitute(result, (v, z3.IntVal(-1)))))

    def test_string_predicate_with_builtin_call(self) -> None:
        """A predicate calling a builtin (`string_starts_with(@String.0, "h")`)
        translates with the binder substituted — same surface as a `requires`
        clause, so `translate_expr` handles it.  (string_length is no longer the
        probe here: it defers to Tier 3 for non-literal args (#802), so a
        string_length refinement translates to None.)"""
        import z3
        from vera.smt import SmtContext
        from vera.types import RefinedType, STRING
        from vera.verifier import ContractVerifier

        pred = self._predicate_of(
            'type HStr = { @String | string_starts_with(@String.0, "h") };\n'
        )
        refined = RefinedType(STRING, pred)
        smt = SmtContext()
        s = z3.Const("s", z3.StringSort())
        result = ContractVerifier._translate_refined_predicate(smt, refined, s)
        assert result is not None
        assert z3.is_true(
            z3.simplify(z3.substitute(result, (s, z3.StringVal("hi"))))
        )
        assert z3.is_false(
            z3.simplify(z3.substitute(result, (s, z3.StringVal("x"))))
        )

    def test_non_primitive_base_is_none(self) -> None:
        """A non-primitive base yields None (caller → Tier 3, never a silent
        pass) — `_base_slot_name` only resolves primitive bases."""
        from vera.types import AdtType, INT, NAT
        from vera.verifier import ContractVerifier

        assert ContractVerifier._base_slot_name(AdtType("Array", (INT,))) is None
        assert ContractVerifier._base_slot_name(INT) == "Int"
        # @Nat is NOT a RefinedType — kept disjoint from the refine_bind path.
        assert ContractVerifier._refined_parts(NAT) is None

    def test_refinement_over_nat_conjoins_base_invariant(self) -> None:
        """A refinement *over* `@Nat` (`{ @Nat | P }`) yields `value >= 0 && P`,
        re-introducing the base intrinsic `>= 0` so P is never the only check
        — substituting v=4 (even, >=0) -> True, v=3 (odd) -> False, v=-2 (even
        but negative) -> False (the `>= 0` conjunct catches it)."""
        import z3
        from vera.smt import SmtContext
        from vera.types import RefinedType, NAT
        from vera.verifier import ContractVerifier

        pred = self._predicate_of("type EN = { @Nat | @Nat.0 % 2 == 0 };\n")
        refined = RefinedType(NAT, pred)
        smt = SmtContext()
        v = z3.Int("v")
        result = ContractVerifier._translate_refined_predicate(smt, refined, v)
        assert result is not None
        assert z3.is_true(z3.simplify(z3.substitute(result, (v, z3.IntVal(4)))))
        assert z3.is_false(z3.simplify(z3.substitute(result, (v, z3.IntVal(3)))))
        # negative-but-even: the base `>= 0` conjunct must reject it
        assert z3.is_false(z3.simplify(z3.substitute(result, (v, z3.IntVal(-2)))))


class TestRefinementPredicateVerification:
    """#746 — refinement-type predicates are statically discharged at binding
    sites and return positions, generalising the @Nat ``>= 0`` machinery to an
    arbitrary translated predicate.

    Covers the soundness risks pinned in the plan: the param-assume <-> call-
    site matched pair (R1), the already-refined-source exemption (R3), the
    return-binder substitution (R5), untranslatable -> Tier-3-not-silent (R7),
    @Nat/refine_bind disjointness (R9), and multi-slot / fn-call predicates
    (R8).
    """

    @staticmethod
    def _refine_obligations(result, status=None):
        obs = [o for o in result.obligations if o.kind == "refine_bind"]
        if status is not None:
            obs = [o for o in obs if o.status == status]
        return obs

    # -- discharge (Tier 1) ------------------------------------------------

    def test_call_argument_literal_discharges(self) -> None:
        """`use(5)` into a `@PosInt` formal discharges `5 > 0` at the call."""
        result = _verify("""
type PosInt = { @Int | @Int.0 > 0 };

private fn use(@PosInt -> @Int)
  requires(true) ensures(true) effects(pure)
{ @PosInt.0 }

private fn caller(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ use(5) }
""")
        assert [d for d in result.diagnostics if d.severity == "error"] == []
        verified = self._refine_obligations(result, "verified")
        assert len(verified) == 1

    def test_call_argument_discharges_from_requires(self) -> None:
        """A `@Int` argument under `requires(@Int.0 > 0)` discharges the
        `@PosInt` formal — the precondition implies the predicate."""
        result = _verify("""
type PosInt = { @Int | @Int.0 > 0 };

private fn use(@PosInt -> @Int)
  requires(true) ensures(true) effects(pure)
{ @PosInt.0 }

private fn caller(@Int -> @Int)
  requires(@Int.0 > 0) ensures(true) effects(pure)
{ use(@Int.0) }
""")
        assert [d for d in result.diagnostics if d.severity == "error"] == []
        assert len(self._refine_obligations(result, "verified")) == 1

    def test_return_position_discharges(self) -> None:
        """`clamp_percent`'s body discharges the `@Percentage` return
        predicate (`>= 0 && <= 100`) from its branch path conditions."""
        result = _verify("""
type Percentage = { @Int | @Int.0 >= 0 && @Int.0 <= 100 };

private fn clamp_percent(@Int -> @Percentage)
  requires(true) ensures(true) effects(pure)
{
  if @Int.0 < 0 then { 0 }
  else { if @Int.0 > 100 then { 100 } else { @Int.0 } }
}
""")
        assert [d for d in result.diagnostics if d.severity == "error"] == []
        assert len(self._refine_obligations(result, "verified")) == 1

    def test_param_assume_enables_body_proof(self) -> None:
        """A refined param's predicate is assumed into the body (R1): the
        ensures `@Bool.result` over `@PosInt.0 > 0` proves only because the
        param is known positive."""
        _verify_ok("""
type PosInt = { @Int | @Int.0 > 0 };

private fn is_pos(@PosInt -> @Bool)
  requires(true) ensures(@Bool.result) effects(pure)
{ @PosInt.0 > 0 }
""")

    def test_multislot_and_predicate_discharges(self) -> None:
        """A multi-conjunct predicate (`>= 0 && <= 100`) discharges at a
        literal call argument (R8)."""
        result = _verify("""
type Percentage = { @Int | @Int.0 >= 0 && @Int.0 <= 100 };

private fn use(@Percentage -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Percentage.0 }

private fn caller(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ use(50) }
""")
        assert [d for d in result.diagnostics if d.severity == "error"] == []
        assert len(self._refine_obligations(result, "verified")) == 1

    def test_string_predicate_discharges(self) -> None:
        """A predicate calling a builtin (`string_starts_with(...)`) discharges
        a matching string literal at a call argument (R8).  (string_length now
        defers to Tier 3 for non-literal args (#802), so it is no longer the
        probe for refinement discharge.)"""
        result = _verify("""
type StartsH = { @String | string_starts_with(@String.0, "h") };

private fn use(@StartsH -> @Int)
  requires(true) ensures(true) effects(pure)
{ 0 }

private fn caller(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ use("hi") }
""")
        assert [d for d in result.diagnostics if d.severity == "error"] == []
        assert len(self._refine_obligations(result, "verified")) == 1

    # -- violation (E505) --------------------------------------------------

    def test_let_violation_reports_e505(self) -> None:
        """`let @PosInt = @Int.0 - 100` cannot prove `> 0` -> E505 with a
        counterexample."""
        matched = _verify_err("""
type PosInt = { @Int | @Int.0 > 0 };

private fn f(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ let @PosInt = @Int.0 - 100; @PosInt.0 }
""", "refinement predicate")
        assert matched[0].error_code == "E505"

    def test_call_violation_reports_e505(self) -> None:
        """An unconstrained `@Int` argument into a `@PosInt` formal -> E505."""
        matched = _verify_err("""
type PosInt = { @Int | @Int.0 > 0 };

private fn use(@PosInt -> @Int)
  requires(true) ensures(true) effects(pure)
{ @PosInt.0 }

private fn caller(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ use(@Int.0) }
""", "refinement predicate")
        assert matched[0].error_code == "E505"

    def test_return_violation_reports_e505(self) -> None:
        """R5: a body that returns an unconstrained value into a refined return
        is CAUGHT — proves the return binder is actually bound (a wrong
        push-key would leave the predicate unconstrained and silently
        verify)."""
        matched = _verify_err("""
type PosInt = { @Int | @Int.0 > 0 };

private fn bad(@Int -> @PosInt)
  requires(true) ensures(true) effects(pure)
{ @Int.0 }
""", "refinement predicate")
        assert matched[0].error_code == "E505"

    def test_literal_return_violation_reports_e505(self) -> None:
        """A literal return `{ 0 }` into `@PosInt` fails `0 > 0` -> E505."""
        matched = _verify_err("""
type PosInt = { @Int | @Int.0 > 0 };

private fn zero(@Unit -> @PosInt)
  requires(true) ensures(true) effects(pure)
{ 0 }
""", "refinement predicate")
        assert matched[0].error_code == "E505"

    # -- R3: already-refined source exemption ------------------------------

    def test_already_refined_source_no_obligation(self) -> None:
        """R3: an already-`@PosInt` value into a `@PosInt` formal raises NO
        obligation (predicate-AST match), so zero refine_bind records and no
        diagnostics."""
        result = _verify("""
type PosInt = { @Int | @Int.0 > 0 };

private fn use(@PosInt -> @Int)
  requires(true) ensures(true) effects(pure)
{ @PosInt.0 }

private fn caller(@PosInt -> @Int)
  requires(true) ensures(true) effects(pure)
{ use(@PosInt.0) }
""")
        assert [d for d in result.diagnostics if d.severity == "error"] == []
        assert self._refine_obligations(result) == []

    def test_distinct_refinements_still_obligated(self) -> None:
        """R3 correctness: a `@Percentage` source into a `@PosInt` formal is
        NOT exempted (distinct predicates) and is refuted — `@Percentage`
        admits 0, which violates `> 0`.  Uses predicate-AST equality, not
        types_equal (which ignores predicates and would wrongly match)."""
        matched = _verify_err("""
type PosInt = { @Int | @Int.0 > 0 };
type Percentage = { @Int | @Int.0 >= 0 && @Int.0 <= 100 };

private fn use(@PosInt -> @Int)
  requires(true) ensures(true) effects(pure)
{ @PosInt.0 }

private fn caller(@Percentage -> @Int)
  requires(true) ensures(true) effects(pure)
{ use(@Percentage.0) }
""", "refinement predicate")
        assert matched[0].error_code == "E505"

    def test_same_predicate_distinct_base_still_obligated(self) -> None:
        """R3 soundness: a source whose predicate matches the target's but whose
        BASE differs is NOT exempted.  `{ @Int | true }` into `{ @Nat | true }`
        must still obligate the `@Nat` base's `>= 0` (an `@Int` can be negative)
        rather than being silently exempted on predicate equality alone — which
        would bypass the `>= 0` check at this unguarded `let` site (CR
        a48cd2c)."""
        result = _verify("""
type AnyInt = { @Int | true };
type AnyNat = { @Nat | true };

public fn coerce(@AnyInt -> @Nat)
  requires(true) ensures(true) effects(pure)
{
  let @AnyNat = @AnyInt.0;
  @AnyNat.0
}
""")
        errs = [d for d in result.diagnostics if d.error_code == "E505"]
        assert errs, "base-mismatch narrowing must obligate, not be R3-exempted"
        # The message surfaces the implicit `@Nat` base invariant rather than
        # rendering only the user predicate `true` / suggesting a no-op
        # `requires(true)` (CR d338946).
        assert "@Nat.0 >= 0" in errs[0].description, (
            f"E505 should surface the implicit >= 0: {errs[0].description}"
        )

    def test_stronger_refinement_source_discharges(self) -> None:
        """A source with a STRONGER refinement (`@Percentage`, `>= 0 && <=
        100`) into a `>= 0` slot is not exempted but DISCHARGES — the implied
        predicate is proven from the source's assumed refinement, so no false
        positive."""
        result = _verify("""
type NonNeg = { @Int | @Int.0 >= 0 };
type Percentage = { @Int | @Int.0 >= 0 && @Int.0 <= 100 };

private fn use(@NonNeg -> @Int)
  requires(true) ensures(true) effects(pure)
{ @NonNeg.0 }

private fn caller(@Percentage -> @Int)
  requires(true) ensures(true) effects(pure)
{ use(@Percentage.0) }
""")
        assert [d for d in result.diagnostics if d.severity == "error"] == []
        assert len(self._refine_obligations(result, "verified")) == 1

    # -- R7: untranslatable -> Tier-3 E506, never silent -------------------

    def test_non_primitive_base_is_tier3_e506(self) -> None:
        """R7: a refinement over a non-primitive (`Array`) base Z3 cannot
        decide is not silently passed — it is a runtime-checked Tier-3 (an
        informational E506; codegen guards the predicate at run time), never a
        silent `tier1_verified`."""
        result = _verify("""
type NonEmptyArray = { @Array<Int> | array_length(@Array<Int>.0) > 0 };

private fn head(@NonEmptyArray -> @Int)
  requires(true) ensures(true) effects(pure)
{ @NonEmptyArray.0[0] }

private fn caller(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ head([42, 1, 2]) }
""")
        # No verifier errors — the narrowing is an informational Tier-3
        # warning, not a failure (guards against an error masquerading as E506).
        assert [d for d in result.diagnostics if d.severity == "error"] == []
        warns = [d for d in result.diagnostics if d.error_code == "E506"]
        assert len(warns) == 1, "expected exactly one E506 Tier-3 warning"
        assert warns[0].severity == "warning"
        # Never counted as statically verified; recorded as runtime-checked.
        assert self._refine_obligations(result, "verified") == []
        assert len(self._refine_obligations(result, "tier3")) == 1
        assert self._refine_obligations(result, "tier3_unguarded") == []

    def test_unmodelled_primitive_base_is_tier3_e506(self) -> None:
        """A refinement over a primitive base the verifier does NOT model
        (`@Byte`, whose `0..255` range has no SMT sort here) is Tier-3 (E506),
        not a wrong Tier-1 / false E505 from translating the predicate without
        the base invariant — only Int/Nat/Bool/Float64/String are modelled, so
        `_base_slot_name` returns None for the rest (CR db24433)."""
        result = _verify("""
type SmallByte = { @Byte | @Byte.0 < 200 };

public fn f(@Byte -> @Byte) requires(true) ensures(true) effects(pure)
{ @Byte.0 }

public fn g(@Unit -> @Byte) requires(true) ensures(true) effects(pure)
{ let @SmallByte = f(5); @SmallByte.0 }
""")
        # No verifier *errors* at all (not just no E505), and exactly one
        # E506 Tier-3 warning on the @Byte narrowing — pinned so the test
        # cannot pass on an unrelated failure or E506 multiplicity drift
        # (CR db24433).
        assert [d for d in result.diagnostics if d.severity == "error"] == []
        warns = [d for d in result.diagnostics if d.error_code == "E506"]
        assert len(warns) == 1
        assert warns[0].severity == "warning"

    def test_unit_refinement_is_unguarded_not_falsely_guarded(self) -> None:
        """A refinement over `@Unit` is recorded `tier3_unguarded` (E506 'not
        runtime-guarded'), NOT `tier3` (guarded): `@Unit` is erased, so codegen
        cannot emit a boundary predicate check, and the verifier must not claim
        a runtime guard it never gets (CR db24433).  A refined `@Unit` return
        is the boundary that would otherwise falsely claim guarding (a
        function-predicate form reaches here; `{ @Unit | false }` is rejected
        at type-check as uninhabited)."""
        result = _verify("""
private fn always_false(@Unit -> @Bool)
  requires(true) ensures(true) effects(pure)
{ false }

type Checked = { @Unit | always_false(()) };

public fn make(@Unit -> @Checked)
  requires(true) ensures(true) effects(pure)
{ () }
""")
        assert [d for d in result.diagnostics if d.severity == "error"] == []
        # Recorded UNguarded (excluded from totals), never a claimed runtime
        # guard codegen does not emit.
        assert len(self._refine_obligations(result, "tier3_unguarded")) == 1
        assert self._refine_obligations(result, "tier3") == []
        # And surfaced as exactly one user-facing E506 warning — assert the
        # public diagnostic, not only the internal obligation state, so the
        # warning can't disappear unnoticed (CR PR-review).
        assert len([d for d in result.diagnostics
                    if d.error_code == "E506" and d.severity == "warning"]) == 1

    def test_refinement_over_aliased_base_verifies(self) -> None:
        """A refinement whose base is an ALIAS — `type Age = Nat; { @Age |
        @Age.0 >= 18 }` — translates and verifies at Tier-1: the predicate's
        binder `@Age.0` is bound even though the resolved primitive is `@Nat`
        (CR e6f17b7).  Previously a false E506 because the binder name was
        erased to `Nat` by resolution and `@Age.0` never resolved."""
        result = _verify("""
type Age = Nat;
type Adult = { @Age | @Age.0 >= 18 };

public fn f(@Int -> @Adult)
  requires(@Int.0 >= 18) ensures(true) effects(pure)
{ @Int.0 }
""")
        assert [d for d in result.diagnostics if d.severity == "error"] == []
        assert len(self._refine_obligations(result, "verified")) == 1
        assert self._refine_obligations(result, "tier3") == []
        assert self._refine_obligations(result, "tier3_unguarded") == []

    def test_refinement_over_adt_base_declared_with_adt_sort(self) -> None:
        """A refinement OVER an ADT base (`{ @Pair | true }`) is declared with
        the ADT sort (`declare_adt` unwraps the refinement), so a match /
        projection in the body translates — not a false Tier-3 / Z3 sort
        failure from declaring the param as Int (CR d338946)."""
        result = _verify("""
private data Pair { Pair(Int, Int) }

type RP = { @Pair | true };

public fn f(@RP -> @Int)
  requires(true) ensures(@Int.result == 0) effects(pure)
{
  match @RP.0 {
    Pair(@Int, @Int) -> @Int.1 - @Int.1
  }
}
""")
        # The postcondition is NON-tautological (`result == 0`) and the body
        # returns `@Int.1 - @Int.1`, so the verifier must model the result
        # THROUGH the match projection of the second Pair component and prove it
        # cancels to 0 — genuinely exercising the ADT-sort declaration rather
        # than passing vacuously (a tautological `result == result`, or a
        # trivial `ensures(true)`, would pass even if the projection path were
        # unconstrained).  No E522 (undecidable body) confirms the refined-ADT
        # base translated rather than falling to a scalar-Int sort (CR PR-review).
        assert [d for d in result.diagnostics if d.severity == "error"] == []
        assert [d for d in result.diagnostics if d.error_code == "E522"] == []

    def test_refined_subpattern_fact_carried_into_arm_body(self) -> None:
        """An `Option<PosInt>` sub-pattern bind carries the field's refinement
        (`> 0`) into the arm body, so a downstream `@Nat` narrowing of the bound
        payload discharges at Tier-1 instead of a false E503 (CR PR-review).
        Jointly exercises the refined-component Z3 sort fix — the bound field
        accessor only exists once `Option<PosInt>` gets a proper datatype sort
        (its `PosInt` field unwrapped to `Int`), so a regression in EITHER the
        arm-fact carry OR the sort unwrap re-breaks this."""
        result = _verify("""
type PosInt = { @Int | @Int.0 > 0 };
public fn takes_nat(@Nat -> @Int)
  requires(true) ensures(true) effects(pure)
{ 0 }
public fn f(@Option<PosInt> -> @Int)
  requires(true) ensures(true) effects(pure)
{
  match @Option<PosInt>.0 {
    Some(@PosInt) -> takes_nat(@PosInt.0),
    None -> 0
  }
}
""")
        assert [d for d in result.diagnostics if d.severity == "error"] == []

    def test_refined_subpattern_genuine_narrowing_still_obligated(self) -> None:
        """SOUNDNESS guard for the arm-fact carry: it uses the field's SOURCE
        type, so a GENUINE narrowing (`Option<Int>` payload bound as `@PosInt`)
        is still OBLIGATED, never silently assumed.  The unprovable `Int ->
        PosInt` sub-pattern narrowing is an E505 — a false Tier-1 here would be
        the exact silent failure the carry must not introduce (CR PR-review)."""
        result = _verify("""
type PosInt = { @Int | @Int.0 > 0 };
public fn takes_nat(@Nat -> @Int)
  requires(true) ensures(true) effects(pure)
{ 0 }
public fn g(@Option<Int> -> @Int)
  requires(true) ensures(true) effects(pure)
{
  match @Option<Int>.0 {
    Some(@PosInt) -> takes_nat(@PosInt.0),
    None -> 0
  }
}
""")
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert errors, "a genuine narrowing must stay obligated, not assumed"
        assert any(d.error_code == "E505" for d in errors)

    def test_nested_subpattern_narrowing_obligated(self) -> None:
        """A NESTED constructor sub-pattern narrowing — `Some(Some(@PosInt))` on
        `Option<Option<Int>>` — is recursed and obligated, so a payload that
        can't be proven `> 0` is an E505 rather than an unguarded false Tier-1
        (CR PR-review: previously the inner narrowing was never recursed)."""
        result = _verify("""
type PosInt = { @Int | @Int.0 > 0 };
public fn needs_pos(@PosInt -> @Int)
  requires(true) ensures(true) effects(pure)
{ @PosInt.0 }
public fn f(@Option<Option<Int>> -> @Int)
  requires(true) ensures(true) effects(pure)
{
  match @Option<Option<Int>>.0 {
    Some(Some(@PosInt)) -> needs_pos(@PosInt.0),
    Some(None) -> 1,
    None -> 2
  }
}
""")
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert [d.error_code for d in errors] == ["E505"], errors

    def test_nested_subpattern_no_false_positive(self) -> None:
        """The nested-recursion must not OVER-obligate: a nested bind that is
        NOT a narrowing — `Some(Some(@PosInt))` on `Option<Option<PosInt>>`
        (the field is already `PosInt`) — verifies clean (CR PR-review)."""
        result = _verify("""
type PosInt = { @Int | @Int.0 > 0 };
public fn needs_pos(@PosInt -> @Int)
  requires(true) ensures(true) effects(pure)
{ @PosInt.0 }
public fn f(@Option<Option<PosInt>> -> @Int)
  requires(true) ensures(true) effects(pure)
{
  match @Option<Option<PosInt>>.0 {
    Some(Some(@PosInt)) -> needs_pos(@PosInt.0),
    Some(None) -> 1,
    None -> 2
  }
}
""")
        assert [d for d in result.diagnostics if d.severity == "error"] == []

    def test_refined_adt_scrutinee_narrowing_obligated(self) -> None:
        """A match on a REFINED ADT scrutinee (`{ @Option<Int> | P }`) unwraps
        the refined base, so a sub-pattern narrowing is still obligated:
        `Some(@PosInt)` on a refined `Option<Int>` is E505 (the payload isn't
        provably `> 0`) rather than a missed false Tier-1 (CR PR-review)."""
        result = _verify("""
type PosInt = { @Int | @Int.0 > 0 };
type ROpt = { @Option<Int> | true };
public fn needs_pos(@PosInt -> @Int)
  requires(true) ensures(true) effects(pure)
{ @PosInt.0 }
public fn f(@ROpt -> @Int)
  requires(true) ensures(true) effects(pure)
{
  match @ROpt.0 {
    Some(@PosInt) -> needs_pos(@PosInt.0),
    None -> 0
  }
}
""")
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert [d.error_code for d in errors] == ["E505"], errors

    def test_refined_adt_scrutinee_no_false_positive(self) -> None:
        """Unwrapping the refined ADT scrutinee must not OVER-obligate: a
        `{ @Option<PosInt> | P }` scrutinee (payload already `PosInt`) verifies
        clean (CR PR-review)."""
        result = _verify("""
type PosInt = { @Int | @Int.0 > 0 };
type ROpt = { @Option<PosInt> | true };
public fn needs_pos(@PosInt -> @Int)
  requires(true) ensures(true) effects(pure)
{ @PosInt.0 }
public fn f(@ROpt -> @Int)
  requires(true) ensures(true) effects(pure)
{
  match @ROpt.0 {
    Some(@PosInt) -> needs_pos(@PosInt.0),
    None -> 0
  }
}
""")
        assert [d for d in result.diagnostics if d.severity == "error"] == []

    def test_refined_tuple_source_facts_seeded(self) -> None:
        """A destructure of a REFINED tuple source (`{ @Tuple<PosInt, Int> | P
        }`) unwraps the refined base so the component source facts are seeded —
        re-narrowing a component (`@PosInt.0` into `@NonNeg`) discharges rather
        than a false E505 (CR PR-review)."""
        result = _verify("""
type PosInt = { @Int | @Int.0 > 0 };
type NonNeg = { @Int | @Int.0 >= 0 };
type RPair = { @Tuple<PosInt, Int> | true };
public fn mk(@Int -> @RPair)
  requires(@Int.0 > 0) ensures(true) effects(pure)
{ Tuple(@Int.0, 3) }
public fn needs_nn(@NonNeg -> @Int)
  requires(true) ensures(true) effects(pure)
{ @NonNeg.0 }
public fn f(@Int -> @Int)
  requires(@Int.0 > 0) ensures(true) effects(pure)
{
  let Tuple<@PosInt, @Int> = mk(@Int.0);
  needs_nn(@PosInt.0)
}
""")
        assert [d for d in result.diagnostics if d.severity == "error"] == []

    def test_refined_subpattern_fact_reaches_call_precondition(self) -> None:
        """The arm-fact carry also reaches call PRECONDITIONS (checked in the
        SMT main pass, not the narrowing walk): `Some(@PosInt)` on
        `Option<PosInt>` then `needs_positive(@PosInt.0)` — whose callee
        `requires(@Int.0 > 0)` — verifies at Tier-1 instead of a false E501,
        because the SMT match translation assumes the bound field's source
        predicate under the arm condition (CR PR-review)."""
        result = _verify("""
type PosInt = { @Int | @Int.0 > 0 };
public fn needs_positive(@Int -> @Int)
  requires(@Int.0 > 0) ensures(true) effects(pure)
{ @Int.0 }
public fn f(@Option<PosInt> -> @Int)
  requires(true) ensures(true) effects(pure)
{
  match @Option<PosInt>.0 {
    Some(@PosInt) -> needs_positive(@PosInt.0),
    None -> 0
  }
}
""")
        assert [d for d in result.diagnostics if d.severity == "error"] == []

    def test_call_precondition_soundness_no_false_discharge(self) -> None:
        """SOUNDNESS for the call-precondition fact carry: an `Option<Int>`
        payload (no refinement) bound as `@Int` does NOT satisfy a callee's
        `requires(@Int.0 > 0)`, so the precondition still raises E501 — the
        source-fact carry must not launder an unproven precondition into a false
        Tier-1 (CR PR-review)."""
        result = _verify("""
public fn needs_positive(@Int -> @Int)
  requires(@Int.0 > 0) ensures(true) effects(pure)
{ @Int.0 }
public fn g(@Option<Int> -> @Int)
  requires(true) ensures(true) effects(pure)
{
  match @Option<Int>.0 {
    Some(@Int) -> needs_positive(@Int.0),
    None -> 0
  }
}
""")
        assert any(d.error_code == "E501"
                   for d in result.diagnostics if d.severity == "error")

    def test_alias_base_refined_return_assumable_by_caller(self) -> None:
        """A callee's ALIAS-base refined return (`{ @Age | @Age.0 >= 18 }`,
        `type Age = Nat`) is assumed by the caller via the predicate's binder
        name, not the resolved `Nat` — so `needs_adult(mk_adult(...))`
        discharges instead of a false E501 (CR PR-review: the SMT `_translate_
        call` analogue of the verifier/codegen binder fix)."""
        result = _verify("""
type Age = Nat;
type Adult = { @Age | @Age.0 >= 18 };
public fn mk_adult(@Nat -> @Adult)
  requires(@Nat.0 >= 18) ensures(true) effects(pure)
{ @Nat.0 }
public fn needs_adult(@Nat -> @Int)
  requires(@Nat.0 >= 18) ensures(true) effects(pure)
{ 0 }
public fn caller(@Nat -> @Int)
  requires(@Nat.0 >= 18) ensures(true) effects(pure)
{ needs_adult(mk_adult(@Nat.0)) }
""")
        assert [d for d in result.diagnostics if d.severity == "error"] == []

    def test_refined_return_from_match_arm_discharges(self) -> None:
        """A refined return whose value is a refined sub-pattern payload from a
        match arm (`Some(@PosInt) -> @PosInt.0` on `Option<PosInt>`, returned as
        `@PosInt`) discharges: the SMT match translation adds a global
        `arm-matched => source-fact` implication so the refined-return goal —
        checked after the arm path conditions pop — can use it (CR PR-review)."""
        result = _verify("""
type PosInt = { @Int | @Int.0 > 0 };
public fn pick(@Option<PosInt> -> @PosInt)
  requires(true) ensures(true) effects(pure)
{
  match @Option<PosInt>.0 {
    Some(@PosInt) -> @PosInt.0,
    None -> 1
  }
}
""")
        assert [d for d in result.diagnostics if d.severity == "error"] == []

    def test_refined_return_from_match_arm_soundness(self) -> None:
        """SOUNDNESS for the refined-return match implication: an `Option<Int>`
        payload (no refinement) returned as `@PosInt` is NOT provably `> 0`, so
        the refined return still raises E505 — the implication is gated on the
        field's SOURCE type, never laundering an unproven value (CR PR-review)."""
        result = _verify("""
type PosInt = { @Int | @Int.0 > 0 };
public fn pick(@Option<Int> -> @PosInt)
  requires(true) ensures(true) effects(pure)
{
  match @Option<Int>.0 {
    Some(@Int) -> @Int.0,
    None -> 1
  }
}
""")
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert [d.error_code for d in errors] == ["E505"], errors

    def test_generic_refined_return_from_match_arm(self) -> None:
        """The generic refined-return fast path also installs the sub-pattern
        fact hook, so a generic fn returning a refined match-arm payload
        discharges (without the hook the arm accessor translates without the
        source fact, false-E505) — CR PR-review."""
        result = _verify("""
type PosInt = { @Int | @Int.0 > 0 };
public forall<T> fn pick(@Option<PosInt> -> @PosInt)
  requires(true) ensures(true) effects(pure)
{
  match @Option<PosInt>.0 {
    Some(@PosInt) -> @PosInt.0,
    None -> 1
  }
}
""")
        assert [d for d in result.diagnostics if d.severity == "error"] == []

    def test_generic_refined_return_from_match_arm_soundness(self) -> None:
        """SOUNDNESS for the generic fast path: an `Option<Int>` payload (no
        refinement) returned as `@PosInt` must still E505 — the generic match
        implication must not launder an unrefined payload that the non-generic
        soundness test also rejects (CR PR-review)."""
        result = _verify("""
type PosInt = { @Int | @Int.0 > 0 };
public forall<T> fn pick(@Option<Int> -> @PosInt)
  requires(true) ensures(true) effects(pure)
{
  match @Option<Int>.0 {
    Some(@Int) -> @Int.0,
    None -> 1
  }
}
""")
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert [d.error_code for d in errors] == ["E505"], errors

    # -- R9: @Nat / refine_bind disjointness -------------------------------

    def test_bare_nat_yields_nat_bind_not_refine_bind(self) -> None:
        """R9: a bare `@Nat` narrowing yields exactly one `nat_bind`
        obligation and NO `refine_bind` (the two paths stay disjoint)."""
        result = _verify("""
private fn f(@Int -> @Int)
  requires(@Int.0 >= 0) ensures(true) effects(pure)
{ let @Nat = @Int.0; @Nat.0 }
""")
        assert [d for d in result.diagnostics if d.severity == "error"] == []
        assert self._refine_obligations(result) == []
        assert any(o.kind == "nat_bind" for o in result.obligations)

    def test_refinement_over_nat_discharges_full_predicate(self) -> None:
        """A refinement *over* `@Nat` (`{ @Nat | P }`) is a refine_bind and
        discharges BOTH the base `>= 0` and the predicate P — the refined-first
        gate keeps P from being silently dropped by the nat path."""
        # Even-Nat literal 4 satisfies `>= 0 && 4 % 2 == 0`: discharges.
        result = _verify("""
type EvenNat = { @Nat | @Nat.0 % 2 == 0 };

private fn use(@EvenNat -> @Int)
  requires(true) ensures(true) effects(pure)
{ @EvenNat.0 }

private fn caller(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ use(4) }
""")
        assert [d for d in result.diagnostics if d.severity == "error"] == []
        assert len(self._refine_obligations(result, "verified")) == 1
        # And NOT also a nat_bind for the same site: the refined-first gate must
        # keep the paths disjoint, so a double-emission regression (refine_bind
        # AND nat_bind) is caught (CR PR-review).
        assert not [o for o in result.obligations
                    if o.kind == "nat_bind" and o.status == "verified"]

    def test_refinement_over_nat_predicate_violation_caught(self) -> None:
        """`{ @Nat | even }` narrowing an odd literal (`3`) is refuted on the
        predicate even though `3 >= 0` holds — proving P is not dropped."""
        matched = _verify_err("""
type EvenNat = { @Nat | @Nat.0 % 2 == 0 };

private fn use(@EvenNat -> @Int)
  requires(true) ensures(true) effects(pure)
{ @EvenNat.0 }

private fn caller(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ use(3) }
""", "refinement predicate")
        assert matched[0].error_code == "E505"

    # -- other binding sites ----------------------------------------------

    def test_constructor_field_discharges_and_violates(self) -> None:
        """A refined constructor field obligates its argument."""
        ok = _verify("""
type PosInt = { @Int | @Int.0 > 0 };
private data Box { Mk(PosInt) }

private fn build(@Unit -> @Box)
  requires(true) ensures(true) effects(pure)
{ Mk(7) }
""")
        assert [d for d in ok.diagnostics if d.severity == "error"] == []
        assert len(self._refine_obligations(ok, "verified")) == 1

        bad = _verify("""
type PosInt = { @Int | @Int.0 > 0 };
private data Box { Mk(PosInt) }

private fn build(@Int -> @Box)
  requires(true) ensures(true) effects(pure)
{ Mk(@Int.0) }
""")
        errs = [d for d in bad.diagnostics if d.error_code == "E505"]
        assert errs, "expected E505 on the unconstrained constructor field"

    def test_tuple_component_construction_discharges_and_violates(self) -> None:
        """A refined TUPLE component obligates its construction argument, just
        like an ADT constructor field.  `Tuple` is a built-in carrier (not
        user-registered), so the component target types are recovered from the
        construction site's expected type — PR-review soundness fix: an
        unobligated refined tuple component was a false Tier-1 / silent
        negative (verify-clean, but the value violated the predicate at run
        time)."""
        ok = _verify("""
type PosInt = { @Int | @Int.0 > 0 };

private fn build(@Unit -> @Tuple<PosInt, Int>)
  requires(true) ensures(true) effects(pure)
{ Tuple(7, 3) }
""")
        assert [d for d in ok.diagnostics if d.severity == "error"] == []
        assert len(self._refine_obligations(ok, "verified")) == 1

        bad = _verify("""
type PosInt = { @Int | @Int.0 > 0 };

private fn build(@Int -> @Tuple<PosInt, Int>)
  requires(true) ensures(true) effects(pure)
{ Tuple(@Int.0, 3) }
""")
        errs = [d for d in bad.diagnostics if d.error_code == "E505"]
        assert errs, "expected E505 on the unconstrained tuple component"

    def test_tuple_component_not_laundered_to_false_tier1(self) -> None:
        """A refined tuple component built from an unconstrained source is NOT
        laundered into a clean Tier-1 by the destructure source-fact seed: the
        construction site obligates it (E505), so the seed only ever assumes a
        component the producer actually established (PR-review regression —
        previously `vera verify` reported Tier-1 while `vera run` trapped at
        the violating value)."""
        result = _verify("""
type PosInt = { @Int | @Int.0 > 0 };

private fn make_bad(@Int -> @Tuple<PosInt, PosInt>)
  requires(true) ensures(true) effects(pure)
{ Tuple(7, @Int.0) }

private fn consume(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let Tuple<@PosInt, @PosInt> = make_bad(@Int.0);
  @PosInt.0 + @PosInt.1
}
""")
        # Component 0 is a valid literal (7) and only component 1 is
        # unconstrained, so the E505 proves the SECOND component is obligated
        # at construction — not just component 0 (CR PR-review: isolate it).
        errs = [d for d in result.diagnostics if d.error_code == "E505"]
        assert errs, "the second tuple component must obligate at construction"

    def test_let_binding_discharges(self) -> None:
        """The let site's *discharge* direction (the violation is covered by
        `test_let_violation_reports_e505`): `let @PosInt = @Int.0` under
        `requires(@Int.0 > 0)` proves at Tier 1."""
        result = _verify("""
type PosInt = { @Int | @Int.0 > 0 };

private fn f(@Int -> @Int)
  requires(@Int.0 > 0) ensures(true) effects(pure)
{ let @PosInt = @Int.0; @PosInt.0 }
""")
        assert [d for d in result.diagnostics if d.severity == "error"] == []
        assert len(self._refine_obligations(result, "verified")) == 1

    def test_effect_operation_argument_discharges_and_violates(self) -> None:
        """A refined effect-operation formal obligates its argument (the #747
        instantiated-`param_types` path), at both discharge and violation."""
        ok = _verify("""
type PosInt = { @Int | @Int.0 > 0 };

effect Counter { op bump(PosInt -> Unit); }

private fn run(@Unit -> @Unit)
  requires(true) ensures(true) effects(<Counter>)
{ Counter.bump(5) }
""")
        assert [d for d in ok.diagnostics if d.severity == "error"] == []
        assert len(self._refine_obligations(ok, "verified")) == 1

        bad = _verify("""
type PosInt = { @Int | @Int.0 > 0 };

effect Counter { op bump(PosInt -> Unit); }

private fn run(@Int -> @Unit)
  requires(true) ensures(true) effects(<Counter>)
{ Counter.bump(@Int.0) }
""")
        errs = [d for d in bad.diagnostics if d.error_code == "E505"]
        assert errs, "expected E505 on the unconstrained effect-op argument"

    def test_match_binding_discharges_and_violates(self) -> None:
        """A top-level `match` binding into a refined pattern obligates the
        scrutinee, at both discharge and violation."""
        ok = _verify("""
type PosInt = { @Int | @Int.0 > 0 };

private fn f(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ match 5 { @PosInt -> @PosInt.0 } }
""")
        assert [d for d in ok.diagnostics if d.severity == "error"] == []
        assert len(self._refine_obligations(ok, "verified")) == 1

        bad = _verify("""
type PosInt = { @Int | @Int.0 > 0 };

private fn f(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ match @Int.0 { @PosInt -> @PosInt.0 } }
""")
        errs = [d for d in bad.diagnostics if d.error_code == "E505"]
        assert errs, "expected E505 on the unconstrained match binding"

    def test_tuple_destructure_discharges_and_violates(self) -> None:
        """A refined tuple-destructure component obligates its sub-expression,
        at both discharge and violation."""
        ok = _verify("""
type PosInt = { @Int | @Int.0 > 0 };

private fn f(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ let Tuple<@PosInt, @Int> = Tuple(7, 3); @PosInt.0 }
""")
        assert [d for d in ok.diagnostics if d.severity == "error"] == []
        assert len(self._refine_obligations(ok, "verified")) == 1

        bad = _verify("""
type PosInt = { @Int | @Int.0 > 0 };

private fn f(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ let Tuple<@PosInt, @Int> = Tuple(@Int.0, 3); @PosInt.0 }
""")
        errs = [d for d in bad.diagnostics if d.error_code == "E505"]
        assert errs, "expected E505 on the unconstrained tuple component"

    # -- desugared / projection / generic-instantiation sites --------------

    def test_pipe_argument_discharges_and_violates(self) -> None:
        """A piped argument into a refined formal is obligated via the
        side-table-recovered target (`left |> use()` desugars to `use(left)`):
        a positive literal discharges, an unconstrained `@Int` is E505."""
        ok = _verify("""
type PosInt = { @Int | @Int.0 > 0 };

private fn use(@PosInt -> @Int)
  requires(true) ensures(true) effects(pure)
{ @PosInt.0 }

private fn caller(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ 5 |> use() }
""")
        assert [d for d in ok.diagnostics if d.severity == "error"] == []
        assert len(self._refine_obligations(ok, "verified")) == 1

        bad = _verify("""
type PosInt = { @Int | @Int.0 > 0 };

private fn use(@PosInt -> @Int)
  requires(true) ensures(true) effects(pure)
{ @PosInt.0 }

private fn caller(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 |> use() }
""")
        errs = [d for d in bad.diagnostics if d.error_code == "E505"]
        assert errs, "expected E505 on the piped refined narrowing"

    def test_adt_subpattern_obligates_and_exempts(self) -> None:
        """A refined ADT sub-pattern bind obligates the projected field: an
        `Option<Int>` source is E505 (the `Int` payload may be <= 0), while an
        `Option<PosInt>` source is R3-exempt (no obligation)."""
        bad = _verify("""
type PosInt = { @Int | @Int.0 > 0 };

private fn use_opt(@Option<Int> -> @Int)
  requires(true) ensures(true) effects(pure)
{ match @Option<Int>.0 { Some(@PosInt) -> @PosInt.0, None -> 1 } }
""")
        errs = [d for d in bad.diagnostics if d.error_code == "E505"]
        assert errs, "expected E505 on the @Int->@PosInt sub-pattern bind"

        exempt = _verify("""
type PosInt = { @Int | @Int.0 > 0 };

private fn use_opt(@Option<PosInt> -> @Int)
  requires(true) ensures(true) effects(pure)
{ match @Option<PosInt>.0 { Some(@PosInt) -> @PosInt.0, None -> 1 } }
""")
        assert [d for d in exempt.diagnostics if d.severity == "error"] == []
        assert self._refine_obligations(exempt) == []

    def test_nonliteral_destructure_obligates_and_exempts(self) -> None:
        """A refined component of a non-literal tuple destructure obligates the
        projected source: a `Tuple<Int, Int>` source is E505, while a
        `Tuple<PosInt, Int>` source is R3-exempt (no obligation)."""
        bad = _verify("""
type PosInt = { @Int | @Int.0 > 0 };

private fn mk(@Int -> @Tuple<Int, Int>)
  requires(true) ensures(true) effects(pure)
{ Tuple(0 - 5, 3) }

private fn use_it(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ let Tuple<@PosInt, @Int> = mk(1); @PosInt.0 }
""")
        errs = [d for d in bad.diagnostics if d.error_code == "E505"]
        assert errs, "expected E505 on the non-literal destructure component"

        exempt = _verify("""
type PosInt = { @Int | @Int.0 > 0 };

private fn mk(@PosInt -> @Tuple<PosInt, Int>)
  requires(true) ensures(true) effects(pure)
{ Tuple(@PosInt.0, 3) }

private fn use_it(@PosInt -> @Int)
  requires(true) ensures(true) effects(pure)
{ let Tuple<@PosInt, @Int> = mk(@PosInt.0); @PosInt.0 }
""")
        assert [d for d in exempt.diagnostics if d.severity == "error"] == []
        assert self._refine_obligations(exempt) == []

    def test_destructure_bound_slot_refinement_retained(self) -> None:
        """#746: a destructured slot's *source* component refinement is retained
        as a block assumption, so a later re-narrowing of that slot discharges
        at Tier 1.

        `let Tuple<@PosInt, @Int> = @Tuple<PosInt, Int>.0` binds `@PosInt` whose
        source component type is `PosInt` (`> 0`); the subsequent
        `let @NonNeg = @PosInt.0` (`>= 0`) proves only because the source `> 0`
        fact was seeded over the bound slot.  Before the fix this was a false
        E505 (the slot lost its refinement at the rebind)."""
        result = _verify("""
type PosInt = { @Int | @Int.0 > 0 };
type NonNeg = { @Int | @Int.0 >= 0 };

public fn f(@Tuple<PosInt, Int> -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let Tuple<@PosInt, @Int> = @Tuple<PosInt, Int>.0;
  let @NonNeg = @PosInt.0;
  @NonNeg.0
}
""")
        assert [d for d in result.diagnostics if d.severity == "error"] == []
        # The re-narrowing obligation (@NonNeg) is discharged at Tier 1; the
        # destructure component (@PosInt from a PosInt source) is R3-exempt, so
        # exactly one refine_bind obligation is recorded and verified.
        assert len(self._refine_obligations(result, "verified")) == 1

    def test_destructure_retained_fact_not_overassumed(self) -> None:
        """#746 soundness: the retained fact is the *source* component type, not
        the (possibly-unproven) target sub-pattern.  A bare `Int` source
        destructured as `Tuple<@PosInt, @Int>` obligates the `@PosInt`
        narrowing (E505), and a later `let @NonNeg = @PosInt.0` is NOT silently
        accepted via a bogus fact — the `@PosInt` slot carries no `> 0` premise
        (its source is bare `Int`), so the re-narrowing also (correctly) fails
        rather than being papered over."""
        result = _verify("""
type PosInt = { @Int | @Int.0 > 0 };
type NonNeg = { @Int | @Int.0 >= 0 };

private fn mk(@Int -> @Tuple<Int, Int>)
  requires(true) ensures(true) effects(pure)
{ Tuple(0 - 5, 3) }

public fn f(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let Tuple<@PosInt, @Int> = mk(1);
  let @NonNeg = @PosInt.0;
  @NonNeg.0
}
""")
        errs = [d for d in result.diagnostics if d.error_code == "E505"]
        # The original @PosInt destructure narrowing E505s; the fix must not
        # have papered it (or the dependent re-narrow) over with a bogus fact.
        assert errs, "expected E505 — a bare-Int source must still obligate"

    def test_let_bound_slot_refinement_retained_and_sound(self) -> None:
        """#746: a let-bound slot whose RHS is a refined-return call retains the
        refinement, and a bare-return source still obligates a re-narrow.

        `let @PosInt = mk()` where `mk` returns `@PosInt`: the call's
        translated result already carries the refined-return predicate (the
        producing function discharged it), so the later `let @NonNeg =
        @PosInt.0` discharges at Tier 1 without leaking the (possibly-unproven)
        target type.  When `mk` returns bare `@Int`, the `@PosInt` narrowing
        E505s and the dependent re-narrow is not silently accepted — guards
        against a let rebind that wrongly assumes the resolved source type over
        a value that does not provably carry it."""
        ok = _verify("""
type PosInt = { @Int | @Int.0 > 0 };
type NonNeg = { @Int | @Int.0 >= 0 };

private fn mk(@Int -> @PosInt)
  requires(true) ensures(true) effects(pure)
{ 5 }

public fn f(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @PosInt = mk(1);
  let @NonNeg = @PosInt.0;
  @NonNeg.0
}
""")
        assert [d for d in ok.diagnostics if d.severity == "error"] == []

        bad = _verify("""
type PosInt = { @Int | @Int.0 > 0 };
type NonNeg = { @Int | @Int.0 >= 0 };

private fn mk(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ 5 }

public fn f(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @PosInt = mk(1);
  let @NonNeg = @PosInt.0;
  @NonNeg.0
}
""")
        errs = [d for d in bad.diagnostics if d.error_code == "E505"]
        assert errs, "expected E505 — a bare-Int let source must still obligate"

    def test_literal_destructure_source_not_overassumed(self) -> None:
        """#746 soundness: a *literal* destructure source is excluded from
        fact-seeding, because the checker types it optimistically.

        `Tuple(0 - 5, 0 - 5)` is typed `Tuple<Nat, Nat>`, but its component
        VALUES are negative — that `Int -> Nat` narrowing is deferred to
        verification, so the `Nat` component type is an unproven claim, not a
        sound premise.  Were it seeded over the bound slot, `>= 0` over `-5`
        would assert a falsehood and vacuously discharge the *later*
        `takes_nat(@Int.0)` obligation.  Asserts that obligation still fires
        ('may be negative'), i.e. the literal source poisoned nothing.  (This
        is the same hazard the #748 stale-binding tests pin, re-checked under
        the fact-retention path.)"""
        result = _verify("""
private fn takes_nat(@Nat -> @Nat)
  requires(true) ensures(true) effects(pure)
{ @Nat.0 }

private fn f(@Int -> @Nat)
  requires(@Int.0 >= 0) ensures(true) effects(pure)
{
  let Tuple<@Int, @Int> = Tuple(0 - 5, 0 - 5);
  takes_nat(@Int.0)
}
""")
        errs = [d for d in result.diagnostics if d.severity == "error"]
        assert any("may be negative" in e.description for e in errs), (
            "literal-source seeding must NOT vacuously discharge the later "
            f"@Nat narrowing; got: {[e.description for e in errs]}"
        )

    def test_destructure_retained_fact_no_cross_statement_bleed(self) -> None:
        """#746: the seeded fact is scoped to its own slot — it does not wrongly
        constrain an unrelated later binding.

        `@PosInt`'s seeded `> 0` (from the `PosInt` source component) must not
        leak onto a *separate* `let @PosInt2 = @Int.0` whose value is genuinely
        unconstrained: that second narrowing must still E505 rather than ride
        the first slot's fact."""
        result = _verify("""
type PosInt = { @Int | @Int.0 > 0 };

public fn f(@Tuple<PosInt, Int>, @Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let Tuple<@PosInt, @Int> = @Tuple<PosInt, Int>.0;
  let @PosInt = @Int.0;
  @PosInt.0
}
""")
        # The first @PosInt (from a PosInt source) is R3-exempt; the second
        # narrows an unconstrained @Int param into @PosInt and must E505 — the
        # first slot's seeded `> 0` fact does not bleed onto the second.
        errs = [d for d in result.diagnostics if d.error_code == "E505"]
        assert errs, (
            "the second, independent @PosInt narrowing must still obligate"
        )

    def test_projected_field_uses_source_refinement_fact(self) -> None:
        """A projected ADT field's own declared type is a sound premise for the
        target predicate (#746, CR a48cd2c): a `@Nat` field bound into
        `{ @Nat | true }` verifies — without the source fact Z3 would invent a
        negative payload the field type forbids (a false E505)."""
        ok = _verify("""
type Trivial = { @Nat | true };

private data Box {
  Box(Nat)
}

public fn unbox(@Box -> @Nat)
  requires(true) ensures(true) effects(pure)
{
  match @Box.0 {
    Box(@Trivial) -> @Trivial.0
  }
}
""")
        assert [d for d in ok.diagnostics if d.severity == "error"] == []

        # Not over-assumed: a stronger target the `>= 0` source fact does NOT
        # imply is still E505 (the projection from a `@Nat` field can be 0..5).
        bad = _verify("""
type GtFive = { @Nat | @Nat.0 > 5 };

private data Box {
  Box(Nat)
}

public fn unbox(@Box -> @Nat)
  requires(true) ensures(true) effects(pure)
{
  match @Box.0 {
    Box(@GtFive) -> @GtFive.0
  }
}
""")
        errs = [d for d in bad.diagnostics if d.error_code == "E505"]
        assert len(errs) == 1, "expected one E505 on the violating projection"

    def test_generic_concrete_refined_return_discharged(self) -> None:
        """A *concrete* refined return on a generic function is discharged
        statically (its obligation is independent of the type parameter), even
        though the generic body otherwise skips SMT: `forall<T> fn bad(@T ->
        @PosInt) { 0 }` is an E505, and `{ 5 }` verifies."""
        bad = _verify("""
type PosInt = { @Int | @Int.0 > 0 };

public forall<T> fn bad(@T -> @PosInt)
  requires(true) ensures(true) effects(pure)
{ 0 }
""")
        errs = [d for d in bad.diagnostics if d.error_code == "E505"]
        assert len(errs) == 1, "expected exactly one E505"
        # No other diagnostics — guards against a spurious extra error.
        assert [d for d in bad.diagnostics
                if d.error_code != "E505"] == []

        ok = _verify("""
type PosInt = { @Int | @Int.0 > 0 };

public forall<T> fn good(@T -> @PosInt)
  requires(true) ensures(true) effects(pure)
{ 5 }
""")
        assert [d for d in ok.diagnostics if d.severity == "error"] == []
        assert len(self._refine_obligations(ok, "verified")) == 1

    def test_generic_refined_return_uses_param_predicate(self) -> None:
        """The generic return check seeds the function's assumptions: a return
        justified by a refined param (or a `requires`) is NOT a false E505."""
        # @PosInt param justifies the @PosInt return.
        _verify_ok("""
type PosInt = { @Int | @Int.0 > 0 };

public forall<T> fn keep(@PosInt, @T -> @PosInt)
  requires(true) ensures(true) effects(pure)
{ @PosInt.0 }
""")
        # A `requires` implying the predicate also discharges it.
        _verify_ok("""
type PosInt = { @Int | @Int.0 > 0 };

public forall<T> fn fromreq(@Int, @T -> @PosInt)
  requires(@Int.0 > 0) ensures(true) effects(pure)
{ @Int.0 }
""")

    def test_generic_refined_return_float64_uses_real_sort(self) -> None:
        """The generic return check must model a concrete `@Float64` param
        with the Real sort, not Int — otherwise a real-sensitive predicate
        like `!= 0.5` is vacuously 'verified' over integers while a runtime
        0.5 violates it (soundness; CR re-review of 100f938)."""
        # An unconstrained @Float64 param returned into a `!= 0.5` refinement
        # MUST be E505: the counterexample 0.5 is reachable only under Real.
        errs = _verify_err("""
type NotHalf = { @Float64 | @Float64.0 != 0.5 };

public forall<T> fn echo_f(@Float64, @T -> @NotHalf)
  requires(true) ensures(true) effects(pure)
{ @Float64.0 }
""", "may violate the refinement predicate")
        assert any(e.error_code == "E505" for e in errs)


class TestZeroSizeCallArgumentKeepsTheSummary:
    """A zero-size call argument does not weaken the call summary (#1214).

    Two spellings of one call, semantically identical: `mk(1)` proved a
    violating refined destructure of the result (a loud E505), while `mk(())`
    — the same function with a `@Unit` parameter — demoted the SAME obligation
    to an unguarded Tier-3 E506.  ``@Unit`` has no Z3 sort, so
    ``translate_expr`` returned None for the argument and the call translator
    read that None as "this call cannot be modelled at all", dropping the whole
    summary.  A zero-size type has exactly one value, so an argument in that
    position tells the summary nothing the signature did not already say; it
    can never be a reason to know LESS.

    The differential is the pin: the two spellings must produce the same
    obligation, the same status and the same code.  Asserting the Unit
    spelling's E505 alone would leave a "fix" that broke the Int spelling
    green.
    """

    #: ``PARAM`` / ``ARG`` are substituted by :meth:`_src` — a Vera refinement
    #: is written with braces, so ``str.format`` is not usable here.
    _SRC = """\
type PosInt = { @Int | @Int.0 > 0 };

private fn mk(@PARAM -> @Tuple<Int, Int>)
  requires(true)
  ensures(true)
  effects(pure)
{
  Tuple(0 - 5, 3)
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let Tuple<@PosInt, @Int> = mk(ARG);
  @Int.0
}
"""

    def _src(self, param: str, arg: str) -> str:
        return self._SRC.replace("@PARAM", f"@{param}").replace("ARG", arg)

    def _run(self, param: str, arg: str) -> object:
        return _verify(self._src(param, arg))

    def test_both_spellings_prove_the_same_violation(self) -> None:
        as_int = self._run("Int", "1")
        as_unit = self._run("Unit", "()")

        def shape(result: object) -> list[tuple[str, str, str]]:
            return [
                (o.kind, o.status, o.error_code)
                for o in result.obligations  # type: ignore[attr-defined]
                if o.kind == "refine_bind"
            ]

        assert shape(as_int) == [("refine_bind", "violated", "E505")], \
            shape(as_int)
        assert shape(as_unit) == shape(as_int), (
            "the zero-size spelling demoted an obligation the informative "
            f"spelling proves: {shape(as_unit)} vs {shape(as_int)}"
        )

    def test_both_spellings_report_the_same_diagnostic(self) -> None:
        for param, arg in (("Int", "1"), ("Unit", "()")):
            result = self._run(param, arg)
            codes = [
                (d.severity, d.error_code) for d in result.diagnostics
            ]
            assert ("error", "E505") in codes, (param, codes)
            assert ("warning", "E506") not in codes, (param, codes)

    def test_the_tier_counts_agree(self) -> None:
        """The summaries are equal too, so nothing was traded for the E505."""
        as_int = self._run("Int", "1").summary
        as_unit = self._run("Unit", "()").summary
        assert as_unit == as_int, (as_unit, as_int)

    #: A zero-size formal BESIDE an informative one.  ``@Nat`` rather than a
    #: second ``@Int`` so the precondition's ``@Nat.0`` names one parameter
    #: under both spellings — with two ``@Int`` formals it would name the
    #: most recent, and the fixture would be measuring De Bruijn rather than
    #: the mask.
    _NEED = """\
private fn need(@PARAM, @Nat -> @Int)
  requires(@Nat.0 > 100)
  ensures(true)
  effects(pure)
{
  nat_to_int(@Nat.0)
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  need(FIRST, ARG)
}
"""

    def _need_src(self, param: str, first: str, arg: str) -> str:
        return (self._NEED
                .replace("@PARAM", f"@{param}")
                .replace("FIRST", first)
                .replace("ARG", arg))

    #: A zero-size argument that is ITSELF a call carrying a real
    #: precondition.  ``INNER`` / ``PARAM`` / ``FIRST`` are substituted by
    #: :meth:`_nested_src`.
    _NESTED = """\
private fn inner(@Int -> @INNER)
  requires(@Int.0 > 100)
  ensures(true)
  effects(pure)
{
  FIRST
}

private fn outer(@PARAM, @Nat -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  nat_to_int(@Nat.0)
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  outer(inner(ARG), 7)
}
"""

    def _nested_src(self, inner: str, first: str, arg: str) -> str:
        return (self._NESTED
                .replace("@INNER", f"@{inner}")
                .replace("@PARAM", f"@{inner}")
                .replace("FIRST", first)
                .replace("ARG", arg))

    def test_an_erased_argument_keeps_its_own_nested_obligation(self) -> None:
        """A zero-size argument's expression is still WALKED (#1214).

        Only its RESULT is discarded.  The walk is what records a nested
        call's own precondition obligation, so dropping the argument before
        translating it — rather than after — would make `outer(inner(5), 7)`
        lose `inner`'s violated precondition entirely: a silent static-coverage
        gap of exactly the kind #882 closed, reopened through the zero-size
        door.

        Asserted as a differential against the informative spelling, so
        "records something" is not enough — it has to record the SAME thing.
        """
        erased = _verify(self._nested_src("Unit", "()", "5"))
        informative = _verify(self._nested_src("Bool", "true", "5"))

        def shape(result: object) -> list[tuple[str, str]]:
            return [
                (o.kind, o.status)
                for o in result.obligations  # type: ignore[attr-defined]
            ]

        nested = [
            o for o in erased.obligations
            if o.kind == "call_pre" and o.status == "violated"
        ]
        assert len(nested) == 1, shape(erased)
        assert nested[0].fn_name == "main", nested[0]
        assert shape(erased) == shape(informative), (
            f"the erased spelling lost or gained an obligation: "
            f"{shape(erased)} vs {shape(informative)}"
        )
        assert erased.summary == informative.summary, (
            erased.summary, informative.summary,
        )
        assert any(
            d.error_code == "E501" and "inner" in d.description
            for d in erased.diagnostics
        ), [d.description[:80] for d in erased.diagnostics]

    def test_a_satisfied_nested_obligation_discharges_under_both(self) -> None:
        """The same shape with an argument the nested precondition allows: no
        error under either spelling, so the test above is measuring the
        obligation and not a call that always fails."""
        for inner, first in (("Unit", "()"), ("Bool", "true")):
            _verify_ok(self._nested_src(inner, first, "500"))

    #: ``Future<Unit>`` is the SECOND zero-size type: `Future<T>` is
    #: representation-transparent (#841), so it erases exactly as bare `Unit`
    #: does and `erases_to_unit` recurses through it.  Nothing else reaches
    #: that recursion through the call-summary mask — the existing
    #: `Future<Unit>` fixtures are checker-side (E183/E206) — so without these
    #: two the arm is unexercised on this path.
    _FUTURE = """\
private fn need(@PARAM, @Nat -> @Int)
  requires(@Nat.0 > 100)
  ensures(true)
  effects(pure)
{
  nat_to_int(@Nat.0)
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(<Async>)
{
  need(async(()), ARG)
}
"""

    def _future_src(self, param: str, arg: str, prelude: str = "") -> str:
        return prelude + (self._FUTURE
                          .replace("@PARAM", f"@{param}")
                          .replace("ARG", arg))

    def test_a_future_unit_argument_is_zero_size_too(self) -> None:
        """Direct `@Future<Unit>`: the formal is masked, so the informative
        `@Nat` formal still pairs with the second argument and its precondition
        is CHECKED.  Unmasked, `async(())` fails to translate and the whole
        call — precondition included — is dropped."""
        errs = _verify_err(
            self._future_src("Future<Unit>", "5"),
            "may violate the callee's precondition",
        )
        assert any(e.error_code == "E501" for e in errs), errs
        _verify_ok(self._future_src("Future<Unit>", "500"))

    def test_an_aliased_future_unit_argument_is_zero_size_too(self) -> None:
        """... and through an alias, since the mask resolves the formal in the
        callee's namespace rather than matching its spelling."""
        prelude = "type Done = Future<Unit>;\n\n"
        errs = _verify_err(
            self._future_src("Done", "5", prelude),
            "may violate the callee's precondition",
        )
        assert any(e.error_code == "E501" for e in errs), errs
        _verify_ok(self._future_src("Done", "500", prelude))

    def test_the_call_precondition_is_checked_under_both_spellings(
        self,
    ) -> None:
        """The opposite verdict as well, so the differential is not "both
        loud" — and the mask is checked for alignment while it is here.

        A satisfying argument must DISCHARGE in both spellings: a summary that
        dropped every call would satisfy the violation tests above by refusing
        to model anything.  And the informative formal sits SECOND, after the
        zero-size one, so the argument list and the callee's parameter stack
        must drop the same position — a mask applied to one and not the other
        pairs argument *i* with formal *i+1*, and the obligation would then be
        checked against the wrong argument (or fail to translate at all).
        """
        for param, first in (("Bool", "true"), ("Unit", "()")):
            errs = _verify_err(
                self._need_src(param, first, "5"),
                "may violate the callee's precondition",
            )
            assert any(e.error_code == "E501" for e in errs), (param, errs)
            _verify_ok(self._need_src(param, first, "500"))


class TestTheTier3DisclosureNamesItsActualCause:
    """An E506 must say why it demoted, and be right about it (#1251).

    Both E506 emitters carried one fixed rationale — "The refinement predicate
    is outside Z3's decidable fragment (a non-primitive base such as Array, an
    undecidable construct, or a solver timeout)" — for four different causes.
    On `handle[State<Small>](@Small = 200)` with
    ``type Small = { @Byte | @Byte.0 < 10 }`` that sentence is simply false:
    ``200 < 10`` is decidable and decidably FALSE.  What actually happened is
    that the verifier does not model ``Byte`` as a refinement base, so the
    predicate was never given a value to reason about.

    Spec §0.3 requires a diagnostic to explain itself truthfully; a rationale
    that names the wrong cause sends a reader to rewrite a predicate that was
    never the problem.

    The fixture here is the SYMBOLIC twin of that repro — the init reads a
    ``@Byte`` parameter rather than a literal.  The literal one is now decided
    outright (#1251(b), :class:`TestAConcreteRefinedNarrowingIsDecided`), so
    the symbolic narrowing is what still demotes, and it is the case whose
    rationale has to name the unmodelled base: it is exactly the shape codegen
    guards at the boundary and the verifier must not turn into a rejection.
    """

    _STATE_INIT = """\
type Small = { @Byte | @Byte.0 < 10 };

public fn use(@Byte -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Small>](@Small = @Byte.0) {
    get(@Unit) -> { resume(@Small.0) },
    put(@Small) -> { resume(()) }
  } in {
    byte_to_int(get(()))
  }
}
"""

    @staticmethod
    def _e506(result: object) -> list:
        return [
            d for d in result.diagnostics  # type: ignore[attr-defined]
            if d.error_code == "E506"
        ]

    def test_an_unmodelled_base_is_not_blamed_on_undecidability(self) -> None:
        """The issue's repro: the rationale names the BASE, not the fragment."""
        result = _verify(self._STATE_INIT)
        warns = self._e506(result)
        assert len(warns) == 1, [d.description[:90] for d in result.diagnostics]
        assert warns[0].severity == "warning", warns[0].severity
        rationale = warns[0].rationale
        assert "Byte" in rationale, rationale
        assert "does not model" in rationale, rationale
        assert "outside Z3's decidable fragment" not in rationale, rationale

    def test_the_predicate_case_still_says_the_predicate(self) -> None:
        """The control: a base the verifier DOES model, with a predicate the
        SMT layer defers on, must still be attributed to the predicate — a
        rationale that blamed the base for everything would be as wrong in the
        other direction.

        `string_length` over a non-literal is deliberately untranslatable
        (#802), and `String` is a modelled base, so this separates the two.
        """
        result = _verify("""
type NonEmpty = { @String | string_length(@String.0) > 0 };

private fn shout(@String -> @String)
  requires(true)
  ensures(true)
  effects(pure)
{
  string_concat(@String.0, "!")
}

public fn use(@String -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @NonEmpty = shout(@String.0);
  0
}
""")
        warns = self._e506(result)
        assert len(warns) == 1, [d.description[:90] for d in result.diagnostics]
        assert warns[0].severity == "warning", warns[0].severity
        rationale = warns[0].rationale
        assert "predicate is outside" in rationale, rationale
        assert "does not model" not in rationale, rationale

    def test_the_symbolic_demotion_survives_the_concrete_gate(self) -> None:
        """A symbolic narrowing keeps its obligation, status and code.

        The measured constraint on #1251(b): conjoining or assuming the base
        invariant for a SYMBOLIC ``@Byte`` turns every boundary narrowing into
        a false E505, so the concrete gate must leave this untouched.
        """
        result = _verify(self._STATE_INIT)
        binds = [o for o in result.obligations if o.kind == "refine_bind"]
        assert len(binds) == 1, binds
        assert binds[0].status == "tier3_unguarded", binds[0]
        assert binds[0].error_code == "E506", binds[0]
        assert not [
            d for d in result.diagnostics if d.severity == "error"
        ], [d.description[:90] for d in result.diagnostics]


class TestAConcreteRefinedNarrowingIsDecided:
    """#1251(b): a LITERAL narrowing over an unmodelled base is decided.

    ``handle[State<Small>](@Small = 200)`` with
    ``type Small = { @Byte | @Byte.0 < 10 }`` ran to completion returning 200 —
    a value the cell's refinement forbids — because ``Byte`` is not a base the
    verifier models, so ``200 < 10`` was never asked.  Level (a) made the
    disclosure name that cause; level (b) asks the question.

    The gate is the value, not the base: a literal is substituted into the
    predicate and FOLDED, so a provable violation is an E505 carrying the
    concrete value and a provable satisfaction is Tier 1, while anything the
    fold does not settle — every symbolic narrowing, and a predicate whose
    operands the SMT layer models opaquely — keeps today's runtime-guarded
    disclosure.  Widening the base itself instead was measured to break
    ``ch02_byte_refinement``'s four boundary narrowings into false rejections.
    """

    @staticmethod
    def _src(init: str, *, cell: str = "Small", extra: str = "") -> str:
        """A State handler whose cell is a refinement over ``@Byte``."""
        return f"""\
type Small = {{ @Byte | @Byte.0 < 10 }};
{extra}
public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{{
  handle[State<{cell}>](@{cell} = {init}) {{
    get(@Unit) -> {{ resume(@{cell}.0) }},
    put(@{cell}) -> {{ resume(()) }}
  }} in {{
    byte_to_int(get(()))
  }}
}}
"""

    def test_the_issue_repro_is_rejected_and_names_the_value(self) -> None:
        """The headline: `@Small = 200` is an error, and says which value."""
        errs = _verify_err(self._src("200"), "violates the refinement")
        assert any(e.error_code == "E505" for e in errs), [
            (e.error_code, e.description[:80]) for e in errs
        ]
        assert any("200" in e.description for e in errs), [
            e.description[:120] for e in errs
        ]
        result = _verify(self._src("200"))
        binds = [o for o in result.obligations if o.kind == "refine_bind"]
        assert len(binds) == 1, binds
        assert binds[0].status == "violated", binds[0]
        assert binds[0].error_code == "E505", binds[0]
        # ... and it is a decision, not a demotion dressed up as one.
        assert not [
            d for d in result.diagnostics if d.error_code == "E506"
        ], [d.description[:90] for d in result.diagnostics]

    def test_a_satisfying_literal_proves_at_tier_1(self) -> None:
        """The passing twin, so the gate is not "reject every literal".

        5 is a value the refinement admits, and the site has no codegen guard,
        so proving it is the whole point: a gate that only ever rejected would
        satisfy the test above while leaving every valid program disclosed.
        """
        _verify_ok(self._src("5"))
        result = _verify(self._src("5"))
        binds = [o for o in result.obligations if o.kind == "refine_bind"]
        assert len(binds) == 1, binds
        assert binds[0].status == "verified", binds[0]
        assert not [
            d for d in result.diagnostics if d.error_code in ("E505", "E506")
        ], [d.description[:90] for d in result.diagnostics]

    def test_the_alias_spelling_is_decided_too(self) -> None:
        """`type Cell = Small` reaches the same obligation, so it decides too.

        The cell type is resolved through the alias chain before the predicate
        is instantiated; a gate keyed on the syntactic spelling would let the
        aliased cell keep running with a forbidden value.
        """
        src = self._src("200", cell="Cell", extra="\ntype Cell = Small;\n")
        errs = _verify_err(src, "violates the refinement")
        assert any(e.error_code == "E505" for e in errs), [
            (e.error_code, e.description[:80]) for e in errs
        ]
        binds = [o for o in _verify(src).obligations if o.kind == "refine_bind"]
        assert [o.status for o in binds] == ["violated"], binds

    def test_a_predicate_the_fold_cannot_settle_stays_disclosed(self) -> None:
        """The gate DECIDES by folding; it does not widen the base.

        `SmallVia`'s predicate routes the byte through a function call, which
        the SMT layer models by the callee's contract rather than by
        evaluation, so `ident(5) < 10` does not fold even though 5 is a
        literal.  Undecided is undecided: the runtime-guarded disclosure
        stands rather than a guessed verdict in either direction.
        """
        result = _verify("""
type SmallVia = { @Byte | ident(@Byte.0) < 10 };

private fn ident(@Byte -> @Byte)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Byte.0
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<SmallVia>](@SmallVia = 5) {
    get(@Unit) -> { resume(@SmallVia.0) },
    put(@SmallVia) -> { resume(()) }
  } in {
    byte_to_int(get(()))
  }
}
""")
        binds = [o for o in result.obligations if o.kind == "refine_bind"]
        assert [o.status for o in binds] == ["tier3_unguarded"], binds
        assert not [
            d for d in result.diagnostics if d.severity == "error"
        ], [d.description[:90] for d in result.diagnostics]

    _GUARDED = """\
type Small = {{ @Byte | @Byte.0 < 10 }};

public fn f(@Int -> @Int)
  requires(@Int.0 > 0)
  ensures(true)
  effects(pure)
{{
  if @Int.0 {cmp} 0 then {{
    let @Small = 200;
    0
  }} else {{
    1
  }}
}}
"""

    def test_a_narrowing_the_path_condition_excludes_discharges(self) -> None:
        """An unreachable narrowing is discharged vacuously, not rejected.

        The obligation is conditional — "IF control reaches this site, P holds
        of the value" — and `check_valid` discharges it by folding the path
        conditions, so a branch the premises exclude discharges whatever the
        value is.  A MODELLED base has always behaved that way; folding the
        predicate alone answered the unconditional question instead, and made
        `200` under `if @Int.0 < 0` with `requires(@Int.0 > 0)` a rejection
        the base-modelled twin accepts.  A false rejection on dead code is
        exactly the false-rejection class the concrete gate was scoped to
        avoid, arriving through the path conditions rather than the base.
        """
        result = _verify(self._GUARDED.format(cmp="<"))
        assert not [
            d for d in result.diagnostics if d.severity == "error"
        ], [d.description[:90] for d in result.diagnostics]
        binds = [o for o in result.obligations if o.kind == "refine_bind"]
        assert [o.status for o in binds] == ["verified"], binds

    def test_a_narrowing_the_path_condition_admits_is_still_rejected(
        self,
    ) -> None:
        """The control that keeps the vacuity from swallowing real violations:
        the same program with the branch REACHABLE is still an E505."""
        errs = _verify_err(
            self._GUARDED.format(cmp=">"), "violates the refinement")
        assert any(e.error_code == "E505" for e in errs), [
            (e.error_code, e.description[:80]) for e in errs
        ]

    def test_the_modelled_base_twin_is_the_oracle(self) -> None:
        """Both verdicts above are what a base the verifier DOES model gives
        for the same shape, which is the standard being met rather than a
        preference: an unmodelled base must not be stricter than a modelled
        one about which paths exist."""
        modelled = """\
type Pos = { @Int | @Int.0 > 0 };

public fn f(@Int -> @Int)
  requires(@Int.0 > 0)
  ensures(true)
  effects(pure)
{
  if @Int.0 %s 0 then {
    let @Pos = 0 - 5;
    0
  } else {
    1
  }
}
"""
        dead = _verify(modelled % "<")
        assert not [
            d for d in dead.diagnostics if d.severity == "error"
        ], [d.description[:90] for d in dead.diagnostics]
        assert [o.status for o in dead.obligations
                if o.kind == "refine_bind"] == ["verified"], dead.obligations
        live = _verify_err(modelled % ">", "refinement predicate")
        assert any(e.error_code == "E505" for e in live), live

    def test_the_byte_refinement_conformance_program_is_unmoved(self) -> None:
        """The canary, pinned whole: verdict, counts AND per-obligation status.

        ``ch02_byte_refinement`` is the program the naive fix breaks — four
        boundary narrowings that codegen runtime-guards and the verifier must
        keep disclosing.  Counts alone would not catch a swap (a rejection
        here plus a new proof there nets to the same totals), so the statuses
        are pinned in order.
        """
        path = (pathlib.Path(__file__).parent / "conformance"
                / "ch02_byte_refinement.vera")
        result = _verify(path.read_text(encoding="utf-8"))
        assert not [
            d for d in result.diagnostics if d.severity == "error"
        ], [d.description[:90] for d in result.diagnostics]
        binds = [o for o in result.obligations if o.kind == "refine_bind"]
        assert [o.status for o in binds] == ["tier3"] * 4, binds
        assert {o.error_code for o in binds} == {"E506"}, binds
        assert result.summary.tier1_verified == 10, result.summary
        assert result.summary.tier3_runtime == 4, result.summary


class TestTheConcretenessGateCoversEverySortALiteralArrivesIn:
    """`_is_z3_literal` must accept every sort a base's literal reaches it in.

    The gate's whole safety argument is "symbolic terms are excluded", which
    is only half of a correctness claim: a sort it fails to recognise makes it
    silently decline a value it should decide, and there is no diagnostic for
    that — the site just keeps its Tier-3 disclosure and nobody learns why.
    So the inventory is enumerated per base rather than asserted in the
    abstract.

    It is also the evidence for what is NOT in the list.  `is_rational_value`
    was carried on the assumption that `@Float64` is a Real; it declares as an
    FP sort, so the arm was unreachable.  Removing an unreachable branch on
    "no test covers it" is backwards, so the pin is the distinguishing fact
    instead: no base's literal is a rational.  Should a sort change make one,
    this goes red at the base that changed and the arm goes back.
    """

    _LITERALS: ClassVar[dict[str, tuple[object, str]]] = {
        "Int": (ast_mod.IntLit(7), "int"),
        "Float64": (ast_mod.FloatLit(1.5), "fp"),
        "Bool": (ast_mod.BoolLit(True), "bool"),
        "String": (ast_mod.StringLit("x"), "string"),
    }

    @staticmethod
    def _classify(term: object) -> set[str]:
        import z3

        simplified = z3.simplify(term)
        return {
            name for name, holds in (
                ("int", z3.is_int_value(simplified)),
                ("rational", z3.is_rational_value(simplified)),
                ("bool", z3.is_true(simplified) or z3.is_false(simplified)),
                ("string", z3.is_string_value(simplified)),
                ("fp", z3.is_fp_value(simplified)),
            ) if holds
        }

    @pytest.mark.parametrize("base", sorted(_LITERALS))
    def test_each_bases_literal_is_recognised_and_is_not_a_rational(
        self, base: str,
    ) -> None:
        from vera.smt import SlotEnv, SmtContext
        from vera.verifier import ContractVerifier

        node, expected = self._LITERALS[base]
        term = SmtContext().translate_expr(node, SlotEnv())
        assert term is not None, base
        kinds = self._classify(term)
        assert expected in kinds, (base, kinds)
        assert "rational" not in kinds, (base, kinds)
        assert ContractVerifier._is_z3_literal(term), (base, kinds)

    def test_a_symbolic_term_is_not_a_literal(self) -> None:
        """The other half: the gate must REJECT what it exists to exclude.

        Without this the inventory above is satisfied by a predicate that
        returns True for everything, which would route every symbolic
        narrowing into the decided path — the false-rejection class the gate
        was built to avoid.
        """
        from vera.smt import SmtContext
        from vera.verifier import ContractVerifier

        smt = SmtContext()
        for var in (smt.declare_int("@Int.0"), smt.declare_bool("@Bool.0"),
                    smt.declare_string("@String.0"),
                    smt.declare_float64("@Float64.0")):
            assert not ContractVerifier._is_z3_literal(var), var


class TestANonVerdictIsAttributedToTheRightOutcome:
    """``check_valid`` has FOUR outcomes; two of them demote (#1251).

    ``unknown`` is the solver declining to decide.  ``opaque`` is the #1199
    verdict — it decided promptly and SAT, but every countermodel ran over an
    effect-operation stand-in, so it refutes nothing the effect actually
    produces.  Three demotion sites reported both as "the solver timed out on
    the predicate", which is the same misattribution #1251 is about one level
    down: it names an event that did not happen and sends the reader to raise
    a timeout that was never hit.

    All three are latent — no whole program is known that reaches them — so
    they are pinned where they can be reached: at the derivation, at the
    branch (driven directly), and structurally, so a fourth site cannot
    reintroduce a hardcoded solver reason.
    """

    def test_the_two_outcomes_get_different_reasons(self) -> None:
        from vera.verifier import ContractVerifier

        opaque = ContractVerifier._undecided_reason("opaque")
        unknown = ContractVerifier._undecided_reason("unknown")
        assert opaque != unknown, opaque
        assert "opaque" in opaque and "stand-in" in opaque, opaque
        assert "no decision" in unknown, unknown
        # Neither may claim a timeout: `unknown` covers a timeout but is not
        # only a timeout, and `opaque` is not one at all.
        assert "timed out" not in opaque, opaque
        assert "timed out" not in unknown, unknown

    def test_the_branch_reports_opaque_as_opaque(
        self, monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        """Driven directly: force the #1199 verdict and read the disclosure.

        The reviewer could not construct a program that reaches these branches,
        so the outcome is injected at ``check_valid`` — the one place all three
        sites take it from. Without the split this emits the timeout text for a
        run in which the solver never timed out.
        """
        from vera.smt import SmtContext, SmtResult

        monkeypatch.setattr(
            SmtContext, "check_valid",
            lambda self, goal, assumptions: SmtResult(status="opaque"),
        )
        result = _verify("""
type PosInt = { @Int | @Int.0 > 0 };

public fn mk(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @PosInt = @Int.0;
  @PosInt.0
}
""")
        warns = [d for d in result.diagnostics if d.error_code == "E506"]
        assert len(warns) == 1, [d.description[:90] for d in result.diagnostics]
        assert warns[0].severity == "warning", warns[0].severity
        rationale = warns[0].rationale
        assert "stand-in" in rationale, rationale
        assert "timed out" not in rationale, rationale
        # ... and it is still a demotion, not a claimed refutation.
        assert not [
            d for d in result.diagnostics if d.error_code == "E505"
        ], [d.description[:90] for d in result.diagnostics]

    _RECORDERS = (
        "_record_refined_bind_tier3",
        # The E531/E504 families, swept onto the same derivation (#1251).
        # Both carried a fixed "untranslatable or the solver timed out" for
        # every demotion, so they are exactly what this pin exists to catch.
        "_record_int_widen_tier3",
        "_record_nat_bind_tier3",
    )

    _UNREACHABLE_QUESTION = """\
type Small = {{ @Byte | @Byte.0 < 10 }};

private fn narrow(@Small -> @Byte)
  requires(true)
  ensures(true)
  effects(pure)
{{
  @Small.0
}}

public fn f(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{{
  {body}
}}
"""

    @pytest.mark.parametrize(
        ("body", "status"),
        [
            # A `let` narrowing, guarded in the body since #765...
            ("let @Small = 200;\n  0", "tier3"),
            # ... and a call argument, which the callee's entry guard covers.
            # Both must demote, and neither may keep the rejection the
            # reachability question failed to justify.  They now land on the
            # same leg, so the pair tests two ROUTES to the demotion rather
            # than two guard verdicts; the guarded/unguarded split itself is
            # held by the constructor-field and effect-op-argument cells.
            ("byte_to_int(narrow(200))", "tier3"),
        ],
    )
    def test_an_unsettled_reachability_question_discloses(
        self, monkeypatch: pytest.MonkeyPatch, body: str, status: str,
    ) -> None:
        """A failing literal whose REACHABILITY the solver cannot settle.

        The three-way's third leg.  When the predicate folds false, the site
        is rejected only if the solver exhibits a state satisfying the
        premises; where it returns no verdict on that question, a definite
        E505 would claim a refutation nothing backs, so the narrowing
        discloses instead.

        The leg is reachable from a whole program — the review drove it with
        premises heavy enough to time the reachability query out — but only
        expensively, so the outcome is injected at the ONE query this path
        makes.  Only the reachability goal is intercepted: `check_valid` is
        left alone for every other obligation, so the program around the
        narrowing still verifies normally and the assertion is about this
        branch rather than about a verifier with no solver.
        """
        import z3

        from vera.smt import SmtContext, SmtResult

        original = SmtContext.check_valid

        def _no_verdict_on_reachability(self, goal, assumptions):
            if z3.is_false(goal):
                return SmtResult(status="unknown")
            return original(self, goal, assumptions)

        monkeypatch.setattr(SmtContext, "check_valid",
                            _no_verdict_on_reachability)
        result = _verify(self._UNREACHABLE_QUESTION.format(body=body))
        binds = [o for o in result.obligations if o.kind == "refine_bind"]
        assert [o.status for o in binds] == [status], binds
        assert not [
            d for d in result.diagnostics if d.error_code == "E505"
        ], [d.description[:90] for d in result.diagnostics]
        warns = [d for d in result.diagnostics if d.error_code == "E506"]
        assert len(warns) == 1, [
            (d.error_code, d.description[:70]) for d in result.diagnostics
        ]
        rationale = warns[0].rationale
        # It names the value, so the reader knows the predicate WAS decided...
        assert "200" in rationale, rationale
        # ... names what was not — and does so as a question about reaching
        # the site, not about the obligation, which is the one thing that did
        # get an answer here.
        assert "can be reached" in rationale, rationale
        assert "no decision on that question" in rationale, rationale
        # ... and claims no timeout, the misattribution this issue is about.
        assert "timed out" not in rationale, rationale

    def test_no_demotion_site_hardcodes_a_solver_reason(self) -> None:
        """Structural: a solver-outcome reason must come from the derivation.

        Every ``reason=`` handed to one of the Tier-3 recorders as a fixed
        string describes something the verifier knows without asking the
        solver — an unmodelled base, an untranslatable value, an opaque
        scrutinee.  Fixed text that talks about the solver is by construction
        a branch that had ``result.status`` in hand and threw it away, which
        is how three sites came to claim a timeout for the opaque verdict.

        "Fixed" has to mean every way of writing a fixed string, or the pin
        forbids one spelling of the defect and waves the others through.  Two
        measured escape hatches closed: an f-string parses as ``JoinedStr``
        and a shared module constant parses as ``Name``, and an earlier
        version read both as "derived, therefore fine".  Anything this cannot
        classify fails too, so a novel spelling is a red test rather than a
        silent gap.
        """
        import ast as py_ast

        tree, module_strings = _verifier_ast()
        offenders: list[tuple[int, str]] = []
        for node in py_ast.walk(tree):
            if not isinstance(node, py_ast.Call):
                continue
            fn = node.func
            if not (isinstance(fn, py_ast.Attribute)
                    and fn.attr in self._RECORDERS):
                continue
            for kw in node.keywords:
                if kw.arg != "reason":
                    continue
                if isinstance(kw.value, py_ast.Call):
                    continue  # derived from a helper — the correct shape
                text = _fixed_text(kw.value, module_strings)
                if text is None:
                    offenders.append((
                        node.lineno,
                        f"unclassifiable {type(kw.value).__name__} — pass a "
                        f"helper call or an inline literal",
                    ))
                elif "solver" in text or "timed out" in text:
                    offenders.append((node.lineno, text[:80]))
        assert not offenders, (
            "a solver-outcome reason is fixed at the call site rather than "
            f"derived from `result.status`: {offenders}"
        )

    def test_every_possibly_unguarded_demotion_supplies_a_reason(self) -> None:
        """Structural: the leg that emits a disclosure must state a cause.

        The E504 and E531 families take ``reason`` as an optional keyword —
        the GUARDED leg records an obligation and emits nothing, so text there
        would be dead — and the recorders raise when an unguarded demotion
        arrives without one.  That raise only fires on the paths a test
        happens to walk, so the same invariant is pinned over the source: any
        call that is not literally ``guarded=True`` can reach the disclosure
        and must carry a reason.

        Without it the two families drift straight back to where #1251 found
        them — a disclosure whose stated cause was chosen once, by whoever
        wrote the reporter, for every branch that reaches it.
        """
        import ast as py_ast

        tree, _ = _verifier_ast()
        offenders: list[tuple[int, str]] = []
        seen: set[str] = set()
        for node in py_ast.walk(tree):
            if not isinstance(node, py_ast.Call):
                continue
            fn = node.func
            if not (isinstance(fn, py_ast.Attribute)
                    and fn.attr in self._RECORDERS):
                continue
            seen.add(fn.attr)
            kwargs = {kw.arg: kw.value for kw in node.keywords}
            guarded = kwargs.get("guarded")
            always_guarded = (
                isinstance(guarded, py_ast.Constant) and guarded.value is True
            )
            if always_guarded:
                continue
            reason = kwargs.get("reason")
            if reason is None:
                offenders.append((node.lineno, f"{fn.attr}: no reason"))
            elif _string_constant(reason) == "":
                # An EMPTY literal satisfies "a reason was passed" while
                # saying nothing — the same defect one spelling over, and it
                # renders a broken sentence rather than a wrong one.
                offenders.append((node.lineno, f"{fn.attr}: empty reason"))
        # A renamed recorder would make both structural pins vacuous — they
        # would walk the file, match nothing and pass — so the roster is
        # checked against the source it claims to be about.
        assert seen == set(self._RECORDERS), sorted(set(self._RECORDERS) - seen)
        assert not offenders, (
            "a demotion that can reach the unguarded disclosure passes no "
            f"`reason`, so the disclosure would state a cause it does not "
            f"know: {offenders}"
        )


def _verifier_ast() -> tuple[object, dict[str, str]]:
    """``vera.verifier``'s parsed source, plus its module-level string consts.

    The path comes from the IMPORTED module rather than a relative one, so the
    walk cannot depend on the working directory — nor, in a layout with more
    than one checkout, inspect a different file than the tests import.
    """
    import ast as py_ast
    import inspect

    import vera.verifier

    path = inspect.getsourcefile(vera.verifier)
    assert path is not None, vera.verifier
    tree = py_ast.parse(
        pathlib.Path(path).read_text(encoding="utf-8"))
    consts: dict[str, str] = {}
    for node in tree.body:
        if not isinstance(node, py_ast.Assign):
            continue
        value = _string_constant(node.value)
        if value is None:
            continue
        for target in node.targets:
            if isinstance(target, py_ast.Name):
                consts[target.id] = value
    return tree, consts


def _string_constant(node: object) -> str | None:
    """*node*'s value when it is a plain string literal, else None.

    Implicit concatenation ("a" "b") is already one ``Constant`` by parse
    time, so it needs no handling of its own.
    """
    import ast as py_ast

    if isinstance(node, py_ast.Constant) and isinstance(node.value, str):
        return node.value
    return None


def _fixed_text(node: object, module_strings: dict[str, str]) -> str | None:
    """The text *node* contributes at the call site, or None if unclassifiable.

    Covers the three ways a reason can be fixed rather than derived: a literal,
    an f-string (whose literal parts are the fixed half — the interpolations
    are not, and a solver word in the fixed half is the defect either way), and
    a reference to a module-level string constant.
    """
    import ast as py_ast

    literal = _string_constant(node)
    if literal is not None:
        return literal
    if isinstance(node, py_ast.JoinedStr):
        parts = [
            v.value for v in node.values
            if isinstance(v, py_ast.Constant) and isinstance(v.value, str)
        ]
        return "".join(parts)
    if isinstance(node, py_ast.Name):
        return module_strings.get(node.id)
    return None
