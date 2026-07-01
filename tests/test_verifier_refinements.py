"""Tests for vera.verifier — refinements (refined param sorts, refinement-predicate translation and verification (#746)).

Split from tests/test_verifier.py (#839). Shared helpers live in tests/verifier_helpers.py.
"""
from __future__ import annotations

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

private fn clamp(@Int -> @Percentage)
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

type Checked = { @Unit | always_false(@Unit.0) };

public fn make(@Unit -> @Checked)
  requires(true) ensures(true) effects(pure)
{ @Unit.0 }
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

private fn mk(@Unit -> @Tuple<Int, Int>)
  requires(true) ensures(true) effects(pure)
{ Tuple(0 - 5, 3) }

private fn use_it(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ let Tuple<@PosInt, @Int> = mk(@Unit.0); @PosInt.0 }
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

private fn mk(@Unit -> @Tuple<Int, Int>)
  requires(true) ensures(true) effects(pure)
{ Tuple(0 - 5, 3) }

public fn f(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let Tuple<@PosInt, @Int> = mk(@Unit.0);
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

private fn mk(@Unit -> @PosInt)
  requires(true) ensures(true) effects(pure)
{ 5 }

public fn f(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @PosInt = mk(@Unit.0);
  let @NonNeg = @PosInt.0;
  @NonNeg.0
}
""")
        assert [d for d in ok.diagnostics if d.severity == "error"] == []

        bad = _verify("""
type PosInt = { @Int | @Int.0 > 0 };
type NonNeg = { @Int | @Int.0 >= 0 };

private fn mk(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ 5 }

public fn f(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @PosInt = mk(@Unit.0);
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
