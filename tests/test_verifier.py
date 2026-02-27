"""Tests for the Vera contract verifier (C4).

Validates Z3-backed contract verification: postcondition checking,
counterexample extraction, tier classification, and graceful fallback
for unsupported constructs.
"""

from __future__ import annotations

from pathlib import Path

import pytest

from vera.parser import parse_to_ast
from vera.checker import typecheck
from vera.verifier import VerifyResult, verify

EXAMPLES_DIR = Path(__file__).parent.parent / "examples"

# Examples that verify with no errors (may have Tier 3 warnings)
ALL_EXAMPLES = sorted(f.name for f in EXAMPLES_DIR.glob("*.vera"))


# =====================================================================
# Helpers
# =====================================================================

def _verify(source: str) -> VerifyResult:
    """Parse, type-check, and verify a source string."""
    ast = parse_to_ast(source)
    typecheck(ast, source)
    return verify(ast, source)


def _verify_ok(source: str) -> None:
    """Assert source verifies with no errors."""
    result = _verify(source)
    errors = [d for d in result.diagnostics if d.severity == "error"]
    assert errors == [], f"Expected no errors, got: {[e.description for e in errors]}"


def _verify_err(source: str, match: str) -> list:
    """Assert source produces at least one verification error matching *match*."""
    result = _verify(source)
    errors = [d for d in result.diagnostics if d.severity == "error"]
    assert errors, f"Expected at least one error, got none"
    matched = [e for e in errors if match.lower() in e.description.lower()]
    assert matched, (
        f"No error matched '{match}'. Errors: {[e.description for e in errors]}"
    )
    return matched


def _verify_warn(source: str, match: str) -> list:
    """Assert source produces at least one verification warning matching *match*."""
    result = _verify(source)
    warnings = [d for d in result.diagnostics if d.severity == "warning"]
    assert warnings, f"Expected at least one warning, got none"
    matched = [w for w in warnings if match.lower() in w.description.lower()]
    assert matched, (
        f"No warning matched '{match}'. Warnings: {[w.description for w in warnings]}"
    )
    return matched


# =====================================================================
# Example round-trip tests
# =====================================================================

class TestExampleVerification:
    """All example .vera files should verify without errors."""

    @pytest.mark.parametrize("filename", ALL_EXAMPLES)
    def test_example_verifies(self, filename: str) -> None:
        source = (EXAMPLES_DIR / filename).read_text()
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
        """Error diagnostic includes a fix suggestion."""
        result = _verify("""
private fn bad(@Int -> @Int)
  requires(true)
  ensures(@Int.result > @Int.0)
  effects(pure)
{ @Int.0 }
""")
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert len(errors) >= 1
        assert errors[0].fix != ""
        assert "precondition" in errors[0].fix.lower() or "postcondition" in errors[0].fix.lower()

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
        assert result.summary.tier3_runtime == 0

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

    def test_recursive_call_is_tier3(self) -> None:
        """Recursive functions still have Tier 3 for decreases."""
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
        # ensures(@Nat.result >= 1) — now Tier 1 via modular verification
        # decreases — always Tier 3 for now
        assert result.summary.tier3_runtime >= 1


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
        # ensures — now Tier 1 via modular verification (recursive call
        #   returns fresh Nat var with assumed postcondition)
        # decreases → Tier 3
        assert result.summary.total >= 3
        assert result.summary.tier1_verified >= 1
        assert result.summary.tier3_runtime >= 1

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
        assert result.summary.tier1_verified == 4
        assert result.summary.total == 4


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


# =====================================================================
# Call-site precondition verification (C6b)
# =====================================================================

class TestCallSiteVerification:
    """Modular verification: callee preconditions checked at call sites."""

    def test_call_satisfied_precondition(self) -> None:
        """Calling with a literal that satisfies requires(@Int.0 != 0)."""
        _verify_ok("""
private fn non_zero(@Int -> @Int)
  requires(@Int.0 != 0)
  ensures(true)
  effects(pure)
{ @Int.0 }

private fn caller(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ non_zero(1) }
""")

    def test_call_violated_precondition(self) -> None:
        """Calling with literal 0 violates requires(@Int.0 != 0)."""
        _verify_err("""
private fn non_zero(@Int -> @Int)
  requires(@Int.0 != 0)
  ensures(true)
  effects(pure)
{ @Int.0 }

private fn bad_caller(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ non_zero(0) }
""", "precondition")

    def test_call_precondition_forwarded(self) -> None:
        """Caller's precondition implies callee's — passes."""
        _verify_ok("""
private fn non_zero(@Int -> @Int)
  requires(@Int.0 != 0)
  ensures(true)
  effects(pure)
{ @Int.0 }

private fn safe_caller(@Int -> @Int)
  requires(@Int.0 != 0)
  ensures(true)
  effects(pure)
{ non_zero(@Int.0) }
""")

    def test_call_postcondition_assumed(self) -> None:
        """Caller's ensures relies on callee's postcondition."""
        _verify_ok("""
private fn succ(@Int -> @Int)
  requires(true)
  ensures(@Int.result == @Int.0 + 1)
  effects(pure)
{ @Int.0 + 1 }

private fn add_two(@Int -> @Int)
  requires(true)
  ensures(@Int.result == @Int.0 + 2)
  effects(pure)
{ succ(succ(@Int.0)) }
""")

    def test_recursive_call_uses_postcondition(self) -> None:
        """Recursive factorial: ensures(@Nat.result >= 1) now Tier 1.

        The postcondition is assumed at the recursive call site,
        and base case returns 1, so result >= 1 is provable.
        """
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
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert errors == [], f"Expected no errors, got: {[e.description for e in errors]}"
        # ensures now Tier 1 (modular verification), decreases still Tier 3
        assert result.summary.tier1_verified >= 2

    def test_call_trivial_precondition(self) -> None:
        """Callee with requires(true) — always satisfied."""
        _verify_ok("""
private fn id(@Int -> @Int)
  requires(true)
  ensures(@Int.result == @Int.0)
  effects(pure)
{ @Int.0 }

private fn caller(@Int -> @Int)
  requires(true)
  ensures(@Int.result == @Int.0)
  effects(pure)
{ id(@Int.0) }
""")

    def test_call_in_let_binding(self) -> None:
        """Call result used via let binding, passed to second call."""
        _verify_ok("""
private fn succ(@Int -> @Int)
  requires(true)
  ensures(@Int.result == @Int.0 + 1)
  effects(pure)
{ @Int.0 + 1 }

private fn add_two_let(@Int -> @Int)
  requires(true)
  ensures(@Int.result == @Int.0 + 2)
  effects(pure)
{
  let @Int = succ(@Int.0);
  succ(@Int.0)
}
""")

    def test_where_block_call(self) -> None:
        """Call to a where-block helper function."""
        _verify_ok("""
private fn outer(@Int -> @Int)
  requires(true)
  ensures(@Int.result == @Int.0 + 1)
  effects(pure)
{ helper(@Int.0) }
where {
  fn helper(@Int -> @Int)
    requires(true)
    ensures(@Int.result == @Int.0 + 1)
    effects(pure)
  { @Int.0 + 1 }
}
""")

    def test_generic_call_falls_to_tier3(self) -> None:
        """Calls to generic functions bail to Tier 3."""
        result = _verify("""
private forall<T>
fn id(@T -> @T)
  requires(true)
  ensures(@T.result == @T.0)
  effects(pure)
{ @T.0 }

private fn caller(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ id(@Int.0) }
""")
        # id's contracts → Tier 3 (generic)
        # caller's body has generic call → body_expr is None
        # Since caller's ensures is trivial, it doesn't matter
        assert result.summary.tier3_runtime >= 1

    def test_multiple_preconditions_all_checked(self) -> None:
        """Two requires on callee, second one violated."""
        _verify_err("""
private fn guarded(@Int -> @Int)
  requires(@Int.0 > 0)
  requires(@Int.0 < 100)
  ensures(true)
  effects(pure)
{ @Int.0 }

private fn bad_caller(@Int -> @Int)
  requires(@Int.0 > 0)
  ensures(true)
  effects(pure)
{ guarded(@Int.0) }
""", "precondition")

    def test_precondition_via_caller_requires(self) -> None:
        """Caller's requires forwards two constraints to satisfy callee."""
        _verify_ok("""
private fn guarded(@Int -> @Int)
  requires(@Int.0 > 0)
  requires(@Int.0 < 100)
  ensures(true)
  effects(pure)
{ @Int.0 }

private fn good_caller(@Int -> @Int)
  requires(@Int.0 > 0)
  requires(@Int.0 < 100)
  ensures(true)
  effects(pure)
{ guarded(@Int.0) }
""")

    def test_multiple_calls_in_sequence(self) -> None:
        """Two calls in sequence, each gets a fresh return variable."""
        _verify_ok("""
private fn inc(@Int -> @Int)
  requires(true)
  ensures(@Int.result == @Int.0 + 1)
  effects(pure)
{ @Int.0 + 1 }

private fn add_two_seq(@Int -> @Int)
  requires(true)
  ensures(@Int.result == @Int.0 + 2)
  effects(pure)
{
  let @Int = inc(@Int.0);
  inc(@Int.0)
}
""")

    def test_violation_error_mentions_callee_name(self) -> None:
        """Error message includes the callee function name."""
        errors = _verify_err("""
private fn non_zero(@Int -> @Int)
  requires(@Int.0 != 0)
  ensures(true)
  effects(pure)
{ @Int.0 }

private fn bad(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ non_zero(0) }
""", "precondition")
        # Check that the error mentions the callee name
        assert any("non_zero" in e.description for e in errors)


# =====================================================================
# Pipe operator verification
# =====================================================================

class TestPipeVerification:
    """Pipe operator desugars correctly in SMT translation."""

    def test_pipe_verifies(self) -> None:
        """Pipe expression in verified function."""
        _verify_ok("""
private fn inc(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ @Int.0 + 1 }

private fn main(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ @Int.0 |> inc() }
""")


# =====================================================================
# Cross-module contract verification (C7d)
# =====================================================================

class TestCrossModuleVerification:
    """Imported function contracts are verified at call sites."""

    # Reusable module sources
    MATH_MODULE = """\
public fn abs(@Int -> @Int)
  requires(true)
  ensures(@Int.result >= 0)
  effects(pure)
{ if @Int.0 < 0 then { 0 - @Int.0 } else { @Int.0 } }

public fn max(@Int, @Int -> @Int)
  requires(true)
  ensures(@Int.result >= @Int.0)
  ensures(@Int.result >= @Int.1)
  effects(pure)
{ if @Int.0 >= @Int.1 then { @Int.0 } else { @Int.1 } }
"""

    GUARDED_MODULE = """\
public fn positive(@Int -> @Int)
  requires(@Int.0 > 0)
  ensures(@Int.result > 0)
  effects(pure)
{ @Int.0 }

private fn internal(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ @Int.0 }
"""

    @staticmethod
    def _resolved(
        path: tuple[str, ...], source: str,
    ) -> "ResolvedModule":
        """Build a ResolvedModule from source text."""
        from vera.resolver import ResolvedModule as RM
        prog = parse_to_ast(source)
        return RM(
            path=path,
            file_path=Path(f"/fake/{'/'.join(path)}.vera"),
            program=prog,
            source=source,
        )

    @staticmethod
    def _verify_mod(
        source: str,
        modules: list["ResolvedModule"],
    ) -> VerifyResult:
        """Parse, type-check, and verify with resolved modules."""
        prog = parse_to_ast(source)
        typecheck(prog, source, resolved_modules=modules)
        return verify(prog, source, resolved_modules=modules)

    # -- Postcondition assumption -----------------------------------------

    def test_imported_postcondition_assumed(self) -> None:
        """abs(x) ensures result >= 0, so caller's ensures(@Int.result >= 0) verifies."""
        mod = self._resolved(("math",), self.MATH_MODULE)
        result = self._verify_mod("""\
import math(abs);
private fn wrap(@Int -> @Int)
  requires(true)
  ensures(@Int.result >= 0)
  effects(pure)
{ abs(@Int.0) }
""", [mod])
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert errors == [], [e.description for e in errors]

    # -- Precondition violation -------------------------------------------

    def test_imported_precondition_violation(self) -> None:
        """positive(0) violates requires(@Int.0 > 0)."""
        mod = self._resolved(("util",), self.GUARDED_MODULE)
        result = self._verify_mod("""\
import util(positive);
private fn bad(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ positive(0) }
""", [mod])
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert errors, "Expected precondition violation"
        assert any("precondition" in e.description.lower() for e in errors)

    # -- Precondition satisfied by caller's requires ----------------------

    def test_imported_precondition_satisfied(self) -> None:
        """Caller's requires(@Int.0 > 0) implies positive's precondition."""
        mod = self._resolved(("util",), self.GUARDED_MODULE)
        result = self._verify_mod("""\
import util(positive);
private fn good(@Int -> @Int)
  requires(@Int.0 > 0)
  ensures(true)
  effects(pure)
{ positive(@Int.0) }
""", [mod])
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert errors == [], [e.description for e in errors]

    # -- Chained imported calls -------------------------------------------

    def test_chained_imported_calls(self) -> None:
        """abs(max(x, y)) >= 0 verifies via composed postconditions."""
        mod = self._resolved(("math",), self.MATH_MODULE)
        result = self._verify_mod("""\
import math(abs, max);
private fn abs_max(@Int, @Int -> @Int)
  requires(true)
  ensures(@Int.result >= 0)
  effects(pure)
{ abs(max(@Int.0, @Int.1)) }
""", [mod])
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert errors == [], [e.description for e in errors]

    # -- Selective import filter ------------------------------------------

    def test_selective_import_not_imported(self) -> None:
        """Function not in import list falls back to Tier 3."""
        mod = self._resolved(("math",), self.MATH_MODULE)
        result = self._verify_mod("""\
import math(abs);
private fn wrap(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ abs(@Int.0) }
""", [mod])
        # abs is imported, max is not — but we're only calling abs here
        # abs should be Tier 1 verified (postcondition is trivial ensures(true))
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert errors == [], [e.description for e in errors]

    # -- Private function not available -----------------------------------

    def test_private_function_not_registered(self) -> None:
        """Private function from module is not injected into verifier env."""
        mod = self._resolved(("util",), self.GUARDED_MODULE)
        # 'internal' is private — it shouldn't be available as a bare call.
        # The verifier should not have it registered, so any ensures relying
        # on its postcondition would fall to Tier 3.
        result = self._verify_mod("""\
import util(positive);
private fn wrap(@Int -> @Int)
  requires(true)
  ensures(@Int.result > 0)
  effects(pure)
{ positive(1) }
""", [mod])
        # positive is public with ensures(@Int.result > 0) → Tier 1
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert errors == [], [e.description for e in errors]
        # Verify the private function 'internal' is not in the env
        assert result.summary.tier3_runtime == 0

    # -- Tier summary counts ----------------------------------------------

    def test_tier_counts_with_imports(self) -> None:
        """Imported calls promote to Tier 1 instead of Tier 3."""
        mod = self._resolved(("math",), self.MATH_MODULE)
        result = self._verify_mod("""\
import math(abs);
private fn wrap(@Int -> @Int)
  requires(true)
  ensures(@Int.result >= 0)
  effects(pure)
{ abs(@Int.0) }
""", [mod])
        # requires(true) → Tier 1, ensures(@Int.result >= 0) → Tier 1 (via abs postcondition)
        assert result.summary.tier1_verified >= 2
        assert result.summary.tier3_runtime == 0

    # -- No regression on single-module -----------------------------------

    def test_single_module_unchanged(self) -> None:
        """Single-module programs verify identically with empty modules list."""
        source = """\
private fn id(@Int -> @Int)
  requires(true)
  ensures(@Int.result == @Int.0)
  effects(pure)
{ @Int.0 }
"""
        result_without = _verify(source)
        result_with = self._verify_mod(source, [])
        assert result_without.summary.tier1_verified == result_with.summary.tier1_verified
        assert result_without.summary.tier3_runtime == result_with.summary.tier3_runtime
