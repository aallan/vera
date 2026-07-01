"""Tests for vera.verifier — contracts (example corpus, trivial/ensures/if-else/let/multi contracts, counterexamples, tier classification, arithmetic, summaries, diverge, edge cases, string-length/predicate verification).

Split from tests/test_verifier.py (#839). Shared helpers live in tests/verifier_helpers.py.
"""
from __future__ import annotations

import pytest

from vera.parser import parse_to_ast
from vera.checker import typecheck
from vera.verifier import verify

from tests.verifier_helpers import (
    ALL_EXAMPLES,
    EXAMPLES_DIR,
    _verify,
    _verify_err,
    _verify_ok,
)


# =====================================================================
# Example round-trip tests
# =====================================================================

class TestExampleVerification:
    """All example .vera files should verify without errors."""

    @pytest.mark.parametrize("filename", ALL_EXAMPLES)
    def test_example_verifies(self, filename: str) -> None:
        source = (EXAMPLES_DIR / filename).read_text(encoding="utf-8")
        ast = parse_to_ast(source, file=filename)
        type_diags = typecheck(ast, source, file=filename)
        type_errors = [d for d in type_diags if d.severity == "error"]
        assert type_errors == [], f"Type errors: {[e.description for e in type_errors]}"

        result = verify(ast, source, file=filename)
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert errors == [], f"Verify errors: {[e.description for e in errors]}"


# =====================================================================
# Trivial contracts
# =====================================================================

class TestTrivialContracts:
    """requires(true) and ensures(true) are trivially Tier 1."""

    def test_requires_true_ensures_true(self) -> None:
        _verify_ok("""
private fn f(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ @Int.0 }
""")

    def test_trivial_counted_as_tier1(self) -> None:
        result = _verify("""
private fn f(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ @Int.0 }
""")
        assert result.summary.tier1_verified == 2
        assert result.summary.tier3_runtime == 0


# =====================================================================
# Ensures verification — postconditions
# =====================================================================

class TestEnsuresVerification:
    """Postcondition VCs are generated and checked against the body."""

    def test_identity_postcondition(self) -> None:
        _verify_ok("""
private fn id(@Int -> @Int)
  requires(true)
  ensures(@Int.result == @Int.0)
  effects(pure)
{ @Int.0 }
""")

    def test_addition_postcondition(self) -> None:
        _verify_ok("""
private fn add(@Int, @Int -> @Int)
  requires(true)
  ensures(@Int.result == @Int.0 + @Int.1)
  effects(pure)
{ @Int.0 + @Int.1 }
""")

    def test_subtraction_postcondition(self) -> None:
        _verify_ok("""
private fn sub(@Int, @Int -> @Int)
  requires(true)
  ensures(@Int.result == @Int.0 - @Int.1)
  effects(pure)
{ @Int.0 - @Int.1 }
""")

    def test_negation_postcondition(self) -> None:
        _verify_ok("""
private fn neg(@Int -> @Int)
  requires(true)
  ensures(@Int.result == 0 - @Int.0)
  effects(pure)
{ 0 - @Int.0 }
""")

    def test_safe_divide_postcondition(self) -> None:
        _verify_ok("""
private fn safe_divide(@Int, @Int -> @Int)
  requires(@Int.1 != 0)
  ensures(@Int.result == @Int.0 / @Int.1)
  effects(pure)
{ @Int.0 / @Int.1 }
""")

    def test_constant_function(self) -> None:
        _verify_ok("""
private fn zero(@Int -> @Int)
  requires(true)
  ensures(@Int.result == 0)
  effects(pure)
{ 0 }
""")

    def test_boolean_postcondition(self) -> None:
        _verify_ok("""
private fn is_positive(@Int -> @Bool)
  requires(@Int.0 > 0)
  ensures(@Bool.result == true)
  effects(pure)
{ @Int.0 > 0 }
""")


# =====================================================================
# If-then-else
# =====================================================================

class TestIfThenElse:
    """If-then-else bodies are verified correctly."""

    def test_absolute_value(self) -> None:
        _verify_ok("""
private fn absolute_value(@Int -> @Int)
  requires(true)
  ensures(@Int.result >= 0)
  effects(pure)
{
  if @Int.0 >= 0 then { @Int.0 } else { 0 - @Int.0 }
}
""")

    def test_max(self) -> None:
        _verify_ok("""
private fn max(@Int, @Int -> @Int)
  requires(true)
  ensures(@Int.result >= @Int.0)
  ensures(@Int.result >= @Int.1)
  effects(pure)
{
  if @Int.0 >= @Int.1 then { @Int.0 } else { @Int.1 }
}
""")

    def test_min(self) -> None:
        _verify_ok("""
private fn min(@Int, @Int -> @Int)
  requires(true)
  ensures(@Int.result <= @Int.0)
  ensures(@Int.result <= @Int.1)
  effects(pure)
{
  if @Int.0 <= @Int.1 then { @Int.0 } else { @Int.1 }
}
""")

    def test_clamp(self) -> None:
        _verify_ok("""
private fn clamp(@Int, @Int, @Int -> @Int)
  requires(@Int.1 <= @Int.2)
  ensures(@Int.result >= @Int.1)
  ensures(@Int.result <= @Int.2)
  effects(pure)
{
  if @Int.0 < @Int.1 then { @Int.1 }
  else { if @Int.0 > @Int.2 then { @Int.2 } else { @Int.0 } }
}
""")

    def test_nested_if(self) -> None:
        _verify_ok("""
private fn sign(@Int -> @Int)
  requires(true)
  ensures(@Int.result >= -1)
  ensures(@Int.result <= 1)
  effects(pure)
{
  if @Int.0 > 0 then { 1 }
  else { if @Int.0 < 0 then { 0 - 1 } else { 0 } }
}
""")


# =====================================================================
# Let bindings
# =====================================================================

class TestLetBindings:
    """Let bindings are handled via substitution."""

    def test_let_identity(self) -> None:
        _verify_ok("""
private fn double(@Int -> @Int)
  requires(true)
  ensures(@Int.result == @Int.0 + @Int.0)
  effects(pure)
{
  let @Int = @Int.0 + @Int.0;
  @Int.0
}
""")

    def test_chained_lets(self) -> None:
        _verify_ok("""
private fn triple(@Int -> @Int)
  requires(true)
  ensures(@Int.result == @Int.0 + @Int.0 + @Int.0)
  effects(pure)
{
  let @Int = @Int.0 + @Int.0;
  let @Int = @Int.0 + @Int.1;
  @Int.0
}
""")


# =====================================================================
# Multiple contracts
# =====================================================================

class TestMultipleContracts:
    """Multiple requires/ensures clauses are AND'd."""

    def test_multiple_ensures(self) -> None:
        _verify_ok("""
private fn bounded(@Int -> @Int)
  requires(@Int.0 >= 0)
  requires(@Int.0 <= 100)
  ensures(@Int.result >= 0)
  ensures(@Int.result <= 100)
  effects(pure)
{ @Int.0 }
""")

    def test_multiple_requires_strengthen(self) -> None:
        _verify_ok("""
private fn positive_div(@Int, @Int -> @Int)
  requires(@Int.0 > 0)
  requires(@Int.1 > 0)
  ensures(@Int.result >= 0)
  effects(pure)
{ @Int.0 / @Int.1 }
""")


# =====================================================================
# Counterexamples
# =====================================================================

class TestCounterexamples:
    """When a contract is violated, a counterexample is reported."""

    def test_false_postcondition(self) -> None:
        """ensures(@Int.result > @Int.0) fails when result == input."""
        _verify_err("""
private fn bad(@Int -> @Int)
  requires(true)
  ensures(@Int.result > @Int.0)
  effects(pure)
{ @Int.0 }
""", "postcondition does not hold")

    def test_false_always(self) -> None:
        """ensures(false) always fails."""
        _verify_err("""
private fn always_fail(@Int -> @Int)
  requires(true)
  ensures(false)
  effects(pure)
{ @Int.0 }
""", "postcondition does not hold")

    def test_counterexample_has_values(self) -> None:
        """Counterexample includes concrete slot values."""
        result = _verify("""
private fn bad(@Int -> @Int)
  requires(true)
  ensures(@Int.result > 0)
  effects(pure)
{ @Int.0 }
""")
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert len(errors) >= 1
        # The description should mention slot values from the counterexample
        desc = errors[0].description
        assert "@Int.0" in desc or "Counterexample" in desc

    def test_violation_has_fix_suggestion(self) -> None:
        """E500 fix names ALL THREE repair classes (#675).

        Pre-#675 the fix text named only two repair classes
        (strengthen `requires(...)`, weaken `ensures(...)`),
        implicitly biasing the user away from the most common
        repair: fixing the implementation to satisfy the
        existing contract.  When E500 catches a typo in the
        function body, "fix the implementation" is what the
        user actually wants to do.

        Post-#675 the fix text lists all three repair classes
        neutrally: fix the implementation, strengthen the
        precondition, or weaken the postcondition.  This test
        pins all three so a regression that drops one would
        fail.
        """
        result = _verify("""
private fn bad(@Int -> @Int)
  requires(true)
  ensures(@Int.result > @Int.0)
  effects(pure)
{ @Int.0 }
""")
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert len(errors) >= 1
        fix = errors[0].fix
        assert fix != ""
        fix_lower = fix.lower()
        # #675: all three repair classes must be named.
        assert "implementation" in fix_lower, (
            f"E500 fix should mention fixing the implementation "
            f"(the most common repair when E500 catches a typo "
            f"in the function body). Got: {fix!r}"
        )
        assert "requires" in fix_lower, (
            f"E500 fix should mention strengthening "
            f"requires(...). Got: {fix!r}"
        )
        assert "ensures" in fix_lower or "postcondition" in fix_lower, (
            f"E500 fix should mention weakening/changing "
            f"ensures(...). Got: {fix!r}"
        )

    def test_violation_has_spec_ref(self) -> None:
        """Error diagnostic includes a spec reference."""
        result = _verify("""
private fn bad(@Int -> @Int)
  requires(true)
  ensures(@Int.result > @Int.0)
  effects(pure)
{ @Int.0 }
""")
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert len(errors) >= 1
        assert "Chapter 6" in errors[0].spec_ref

    def test_precondition_saves_from_violation(self) -> None:
        """Adding a precondition can make a failing postcondition valid."""
        # Without precondition: fails
        _verify_err("""
private fn bad(@Int -> @Int)
  requires(true)
  ensures(@Int.result > 0)
  effects(pure)
{ @Int.0 }
""", "postcondition does not hold")

        # With precondition: passes
        _verify_ok("""
private fn good(@Int -> @Int)
  requires(@Int.0 > 0)
  ensures(@Int.result > 0)
  effects(pure)
{ @Int.0 }
""")


# =====================================================================
# Tier classification and fallback
# =====================================================================

class TestTierClassification:
    """Contracts are classified into Tier 1 vs Tier 3."""

    def test_linear_arithmetic_is_tier1(self) -> None:
        result = _verify("""
private fn f(@Int, @Int -> @Int)
  requires(@Int.1 != 0)
  ensures(@Int.result == @Int.0 + @Int.1)
  effects(pure)
{ @Int.0 + @Int.1 }
""")
        assert result.summary.tier1_verified == 2
        # #798: `@Int.0 + @Int.1` (in the body AND the ensures) each carry an
        # int_overflow obligation; unbounded @Int operands → tier3 (may overflow
        # i64, runtime-guarded).
        assert result.summary.tier3_runtime == 2

    def test_generic_function_is_tier3(self) -> None:
        result = _verify("""
private forall<T>
fn id(@T -> @T)
  requires(true)
  ensures(@T.result == @T.0)
  effects(pure)
{ @T.0 }
""")
        assert result.summary.tier3_runtime >= 1

    def test_match_body_is_tier3(self) -> None:
        """Functions with match in the body fall to Tier 3."""
        result = _verify("""
private data Bool2 { True2, False2 }

private fn invert(@Bool2 -> @Bool2)
  requires(true)
  ensures(true)
  effects(pure)
{
  match @Bool2.0 {
    True2 -> False2,
    False2 -> True2
  }
}
""")
        # ensures(true) is trivial → Tier 1
        # No non-trivial ensures, so no Tier 3 from body translation
        assert result.summary.tier1_verified >= 2

    def test_recursive_call_decreases_verified(self) -> None:
        """Recursive functions with simple Nat decreases are Tier 1."""
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
        # ensures(@Nat.result >= 1) — Tier 1 via modular verification
        # decreases(@Nat.0) — Tier 1 via termination verification
        # @Nat.0 - 1 underflow obligation (#520) — Tier 1 via path condition
        # #798: @Nat.0 * factorial(...) multiply emits an int_overflow
        # obligation; operands are unbounded so it falls to Tier 3.
        assert result.summary.tier1_verified == 4
        assert result.summary.tier3_runtime == 1


# =====================================================================
# Arithmetic contracts
# =====================================================================

class TestArithmetic:
    """Arithmetic contract verification."""

    def test_nat_non_negative(self) -> None:
        _verify_ok("""
private fn nat_id(@Nat -> @Nat)
  requires(true)
  ensures(@Nat.result >= 0)
  effects(pure)
{ @Nat.0 }
""")

    def test_nat_constraint_used(self) -> None:
        """Nat parameters are constrained >= 0 in Z3."""
        _verify_ok("""
private fn nat_plus_one(@Nat -> @Int)
  requires(true)
  ensures(@Int.result > 0)
  effects(pure)
{ @Nat.0 + 1 }
""")

    def test_int_to_nat_negative_caught(self) -> None:
        """Int body returning -1 as Nat: verifier must catch the violation.

        The type checker permits Int <: Nat (rule 3b), deferring the
        non-negativity check to the verifier.  Returning a literal -1
        contradicts the Nat >= 0 constraint, so verification must fail.
        """
        _verify_err("""
private fn bad(@Unit -> @Nat)
  requires(true)
  ensures(@Nat.result >= 0)
  effects(pure)
{ -1 }
""", "postcondition")

    def test_int_to_nat_positive_ok(self) -> None:
        """Int expression returned as Nat: verifier passes when >= 0."""
        _verify_ok("""
private fn good(@Nat -> @Nat)
  requires(true)
  ensures(@Nat.result >= 0)
  effects(pure)
{ @Nat.0 + 1 }
""")

    def test_int_to_nat_conditional(self) -> None:
        """Int body with conditional: verifier checks all paths >= 0."""
        _verify_ok("""
private fn abs_nat(@Int -> @Nat)
  requires(true)
  ensures(@Nat.result >= 0)
  effects(pure)
{
  if @Int.0 >= 0 then { @Int.0 }
  else { 0 - @Int.0 }
}
""")

    def test_modular_arithmetic(self) -> None:
        _verify_ok("""
private fn remainder(@Int, @Int -> @Int)
  requires(@Int.1 > 0)
  ensures(true)
  effects(pure)
{ @Int.0 % @Int.1 }
""")


# =====================================================================
# Summary
# =====================================================================

class TestSummary:
    """Verification summary is correctly computed."""

    def test_all_trivial(self) -> None:
        result = _verify("""
private fn f(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ @Int.0 }
""")
        assert result.summary.tier1_verified == 2
        assert result.summary.total == 2
        assert result.summary.tier3_runtime == 0

    def test_mixed_tiers(self) -> None:
        result = _verify("""
private fn f(@Nat -> @Nat)
  requires(true)
  ensures(@Nat.result >= 0)
  decreases(@Nat.0)
  effects(pure)
{
  if @Nat.0 == 0 then { 0 }
  else { @Nat.0 + f(@Nat.0 - 1) }
}
""")
        # requires(true) → Tier 1 trivial
        # ensures — Tier 1 via modular verification
        # decreases — Tier 1 via termination verification
        # @Nat.0 - 1 underflow obligation (#520) — Tier 1 via path condition
        # #798: @Nat.0 + f(...) add emits an int_overflow obligation; operands
        # are unbounded so it falls to Tier 3.
        assert result.summary.total == 5
        assert result.summary.tier1_verified == 4
        assert result.summary.tier3_runtime == 1

    def test_multiple_functions_accumulate(self) -> None:
        result = _verify("""
private fn f(@Int -> @Int)
  requires(true)
  ensures(@Int.result == @Int.0)
  effects(pure)
{ @Int.0 }

private fn g(@Int -> @Int)
  requires(true)
  ensures(@Int.result == @Int.0 + 1)
  effects(pure)
{ @Int.0 + 1 }
""")
        # f: requires(true) trivial + ensures verified = 2 Tier 1
        # g: requires(true) trivial + ensures verified = 2 Tier 1
        # #798: g's `@Int.0 + 1` appears twice — once in the body and once in
        # ensures(@Int.result == @Int.0 + 1) — each emitting an int_overflow
        # obligation; operands are unbounded so both fall to Tier 3.
        assert result.summary.tier1_verified == 4
        assert result.summary.total == 6
        assert result.summary.tier3_runtime == 2


# =====================================================================
# Diverge built-in effect (Chapter 7, §7.7.3)
# =====================================================================

class TestDivergeEffect:
    """Diverge is a recognised marker effect with no operations."""

    def test_diverge_verifies(self) -> None:
        """A function with effects(<Diverge>) should verify cleanly."""
        _verify_ok("""
private fn loop(@Unit -> @Int)
  requires(true) ensures(true) effects(<Diverge>)
{ 0 }
""")

    def test_diverge_with_io_verifies(self) -> None:
        """Diverge composes with other effects for verification."""
        _verify_ok("""
private fn serve(@Unit -> @Unit)
  requires(true) ensures(true) effects(<Diverge, IO>)
{
  IO.print("running");
  ()
}
""")


# =====================================================================
# Edge cases
# =====================================================================

class TestEdgeCases:
    """Edge cases and boundary conditions."""

    def test_empty_body_unit(self) -> None:
        """Unit-returning function with trivial contracts."""
        _verify_ok("""
private fn noop(@Unit -> @Unit)
  requires(true)
  ensures(true)
  effects(pure)
{ () }
""")

    def test_deeply_nested_if(self) -> None:
        _verify_ok("""
private fn deep(@Int -> @Int)
  requires(true)
  ensures(@Int.result >= 0)
  ensures(@Int.result <= 3)
  effects(pure)
{
  if @Int.0 > 0 then {
    if @Int.0 > 10 then { 3 }
    else { if @Int.0 > 5 then { 2 } else { 1 } }
  } else { 0 }
}
""")

    def test_implies_in_contract(self) -> None:
        """The ==> operator works in contracts."""
        _verify_ok("""
private fn f(@Int -> @Int)
  requires(true)
  ensures(@Int.0 > 0 ==> @Int.result > 0)
  effects(pure)
{ @Int.0 }
""")

    def test_boolean_logic_in_contract(self) -> None:
        _verify_ok("""
private fn f(@Int -> @Int)
  requires(@Int.0 > 0 && @Int.0 < 100)
  ensures(@Int.result > 0 || @Int.result == 0)
  effects(pure)
{ @Int.0 }
""")


class TestStringLengthVerification:
    """string_length defers to Tier 3 for non-literal arguments (#802).

    Z3's ``Length`` over ``z3.String`` counts Unicode code points, but Vera's
    runtime ``string_length`` counts UTF-8 bytes — so modeling a non-literal
    ``string_length`` with ``z3.Length`` proved false contracts for non-ASCII
    input.  The only sound Tier-1 model is the exact byte length of a string
    *literal*; everything else defers to a runtime-guarded Tier-3 obligation.
    (Comprehensive coverage: tests/test_string_length_soundness.py.)
    """

    def test_string_length_slot_in_ensures_defers_to_tier3(self) -> None:
        """ensures over a slot-arg string_length can't be Tier-1 proved (the
        byte count is unknown to Z3); it defers to a runtime-guarded Tier-3
        obligation rather than the old unsound z3.Length proof."""
        result = _verify("""
private fn get_length(@String -> @Int)
  requires(true)
  ensures(@Int.result >= 0)
  effects(pure)
{
  string_length(@String.0)
}
""")
        assert result.summary.tier3_runtime >= 1

    def test_string_length_literal_byte_length_tier1(self) -> None:
        """string_length of a literal is modeled at its exact UTF-8 byte length
        and verifies at Tier 1 (ASCII: 2 bytes for "hi")."""
        result = _verify("""
private fn two(@Unit -> @Int)
  requires(true)
  ensures(@Int.result == 2)
  effects(pure)
{
  string_length("hi")
}
""")
        assert result.summary.tier1_verified >= 1
        assert result.summary.tier3_runtime == 0

    def test_string_length_slot_comparison_defers(self) -> None:
        """A slot-arg string_length in an ensures comparison defers to Tier 3
        (was an unsound Tier-1 z3.Length proof)."""
        result = _verify("""
private fn longer_than(@String, @Int -> @Bool)
  requires(@Int.0 >= 0)
  ensures(string_length(@String.0) >= 0)
  effects(pure)
{
  string_length(@String.0) > @Int.0
}
""")
        assert result.summary.tier3_runtime >= 1


class TestStringPredicateVerification:
    """string_contains/starts_with/ends_with use Z3 native string theory (Tier 1)."""

    def test_string_contains_tier1(self) -> None:
        """requires(string_contains(@String.0, ...)) verifies Tier 1."""
        result = _verify("""
private fn has_prefix(@String -> @Bool)
  requires(string_contains(@String.0, "http"))
  ensures(true)
  effects(pure)
{
  string_starts_with(@String.0, "http")
}
""")
        assert result.summary.tier3_runtime == 0

    def test_string_starts_with_tier1(self) -> None:
        """requires(string_starts_with(...)) verifies Tier 1."""
        result = _verify("""
private fn require_https(@String -> @Bool)
  requires(string_starts_with(@String.0, "https://"))
  ensures(true)
  effects(pure)
{
  string_length(@String.0) > 8
}
""")
        assert result.summary.tier3_runtime == 0

    def test_string_ends_with_tier1(self) -> None:
        """requires(string_ends_with(...)) verifies Tier 1."""
        result = _verify("""
private fn require_json(@String -> @Bool)
  requires(string_ends_with(@String.0, ".json"))
  ensures(true)
  effects(pure)
{
  string_length(@String.0) > 5
}
""")
        assert result.summary.tier3_runtime == 0

    def test_float_is_nan_translates_at_tier1(self) -> None:
        """#797: float_is_nan now translates to fpIsNaN (Float64 is an FP sort),
        so a contract guarded by it verifies at Tier 1 instead of dropping to
        Tier 3 — excluding NaN restores reflexivity, so `result == input` holds."""
        result = _verify("""
private fn idf(@Float64 -> @Float64)
  requires(!float_is_nan(@Float64.0))
  ensures(@Float64.result == @Float64.0)
  effects(pure)
{
  @Float64.0
}
""")
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert errors == [], [e.error_code for e in errors]
        # The guarded postcondition itself must stay Tier 1 — tier1_verified >= 1
        # alone is satisfied by the requires(!nan) obligation even if the
        # ensures(result == input) regressed to Tier 3.
        ens = [o for o in result.obligations if o.kind == "ensures"]
        assert ens and all(o.status == "verified" for o in ens), [
            (o.kind, o.status) for o in result.obligations
        ]
        assert result.summary.tier3_runtime == 0

    def test_float_is_infinite_translates_at_tier1(self) -> None:
        """#797: float_is_infinite now translates to fpIsInf, so a contract over
        it verifies at Tier 1 (was Tier 3 under the Real model, where Inf was
        unrepresentable)."""
        result = _verify("""
private fn finite_only(@Float64 -> @Bool)
  requires(true)
  ensures(@Bool.result == float_is_infinite(@Float64.0))
  effects(pure)
{
  float_is_infinite(@Float64.0)
}
""")
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert errors == [], [e.error_code for e in errors]
        # Pin the postcondition's tier: tier1_verified >= 1 alone could be met
        # by the requires(true) obligation even if the ensures dropped to Tier 3.
        ens = [o for o in result.obligations if o.kind == "ensures"]
        assert ens and all(o.status == "verified" for o in ens), [
            (o.kind, o.status) for o in result.obligations
        ]
        assert result.summary.tier3_runtime == 0
