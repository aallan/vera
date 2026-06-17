"""Tests for the Vera contract verifier (C4).

Validates Z3-backed contract verification: postcondition checking,
counterexample extraction, tier classification, and graceful fallback
for unsupported constructs.
"""

from __future__ import annotations

from pathlib import Path

import pytest

from vera.parser import parse_to_ast
from vera.checker import typecheck, typecheck_with_artifacts
from vera.resolver import ResolvedModule
from vera.verifier import VerifyResult, verify

EXAMPLES_DIR = Path(__file__).parent.parent / "examples"

# Examples that verify with no errors (may have Tier 3 warnings)
ALL_EXAMPLES = sorted(f.name for f in EXAMPLES_DIR.glob("*.vera"))


# =====================================================================
# Helpers
# =====================================================================

def _verify(source: str) -> VerifyResult:
    """Parse, type-check, and verify a source string.

    Mirrors the CLI verify path (``cmd_verify``): collects the #747
    semantic-type side-tables during type-check and threads them into
    ``verify()``, so the projection / generic-instantiation @Nat
    narrowing obligations fire here exactly as for ``vera verify``.
    """
    ast = parse_to_ast(source)
    _diags, arts = typecheck_with_artifacts(ast, source)
    return verify(
        ast, source,
        expr_types=arts.expr_semantic_types,
        expr_target_types=arts.expr_target_types,
    )


def _verify_ok(source: str) -> None:
    """Assert source verifies with no errors."""
    result = _verify(source)
    errors = [d for d in result.diagnostics if d.severity == "error"]
    assert errors == [], f"Expected no errors, got: {[e.description for e in errors]}"


def _verify_err(source: str, match: str) -> list:
    """Assert source produces at least one verification error matching *match*."""
    result = _verify(source)
    errors = [d for d in result.diagnostics if d.severity == "error"]
    assert errors, "Expected at least one error, got none"
    matched = [e for e in errors if match.lower() in e.description.lower()]
    assert matched, (
        f"No error matched '{match}'. Errors: {[e.description for e in errors]}"
    )
    return matched


def _verify_warn(source: str, match: str) -> list:
    """Assert source produces at least one verification warning matching *match*."""
    result = _verify(source)
    warnings = [d for d in result.diagnostics if d.severity == "warning"]
    assert warnings, "Expected at least one warning, got none"
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
        assert result.summary.tier1_verified == 4
        assert result.summary.tier3_runtime == 0


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
# @Nat subtraction underflow obligation (#520)
# =====================================================================

class TestNatSubtractionObligation520:
    """`@Nat - @Nat` carries a Tier-1 proof obligation `lhs >= rhs`.

    Per spec/04 §4.4 and spec/11 §11.2.1, a subtraction site whose
    result type is `@Nat` AND at least one operand has `@Nat`
    *provenance* (a slot reference, a function call returning `@Nat`,
    or a sub-expression containing one) must prove that the left
    operand is at least as large as the right. The verifier
    discharges the obligation from preconditions (`requires`) and
    path conditions (`if` / `match` branches). When Z3 cannot
    discharge it, verification fails with a counterexample so the
    author can add a `requires` clause; the codegen separately emits
    a runtime guard at the same set of sites.

    Path-A scope (#520): pure-literal subtractions like `0 - 1`
    (the canonical "I want -1 as a literal" idiom widely used in
    `Err(_) -> 0 - 1` and `throw(0 - 1)` positions) are intentionally
    exempt — neither operand has `@Nat` provenance, so the
    obligation does not fire. `test_pure_literal_subtraction_not_flagged`
    pins that exception. Catching `let @Nat = 0 - 1` (binding-site
    narrowing) is the broader generalisation tracked as #552.

    `@Int - @Int` and `@Nat - @Int → @Int` carry no obligation —
    `Int` is allowed to be negative, so underflow is not a violation.
    """

    def test_requires_clause_discharges_obligation(self) -> None:
        """Explicit `requires(@Nat.0 >= @Nat.1)` discharges the obligation."""
        _verify_ok("""
private fn safe_sub(@Nat, @Nat -> @Nat)
  requires(@Nat.0 >= @Nat.1)
  ensures(@Nat.result <= @Nat.0)
  effects(pure)
{ @Nat.0 - @Nat.1 }
""")

    def test_if_guard_discharges_obligation(self) -> None:
        """Path condition `@Nat.0 != 0` (else branch of `if @Nat.0 == 0`)
        implies `@Nat.0 >= 1`, which discharges `@Nat.0 - 1 >= 0`.

        This is the canonical recursion shape used throughout the
        examples and conformance suite (factorial, fib, mutual
        recursion). After this fix lands they must continue to verify
        without source changes.
        """
        _verify_ok("""
private fn dec(@Nat -> @Nat)
  requires(true)
  ensures(true)
  decreases(@Nat.0)
  effects(pure)
{
  if @Nat.0 == 0 then {
    0
  } else {
    @Nat.0 - 1
  }
}
""")

    def test_subtract_zero_discharges_trivially(self) -> None:
        """`@Nat.0 - 0` is always safe — RHS is the literal 0."""
        _verify_ok("""
private fn id_via_sub(@Nat -> @Nat)
  requires(true)
  ensures(@Nat.result == @Nat.0)
  effects(pure)
{ @Nat.0 - 0 }
""")

    def test_self_subtract_discharges(self) -> None:
        """`@Nat.0 - @Nat.0` is always 0 — Z3 knows lhs == rhs."""
        _verify_ok("""
private fn self_sub(@Nat -> @Nat)
  requires(true)
  ensures(@Nat.result == 0)
  effects(pure)
{ @Nat.0 - @Nat.0 }
""")

    def test_unguarded_subtract_fails(self) -> None:
        """Bare `@Nat.0 - @Nat.1` without a `requires` fails verification.

        Counterexample: @Nat.0 = 0, @Nat.1 = 1 produces -1, which is
        not a valid @Nat. The verifier must reject.
        """
        _verify_err("""
private fn unsafe_sub(@Nat, @Nat -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{ @Nat.0 - @Nat.1 }
""", "underflow")

    def test_int_subtract_not_obligated(self) -> None:
        """`@Int - @Int → @Int` carries no underflow obligation.

        @Int is signed; negative results are well-defined. The
        obligation should fire only when the *result type* is @Nat.
        """
        _verify_ok("""
private fn int_sub(@Int, @Int -> @Int)
  requires(true)
  ensures(@Int.result == @Int.0 - @Int.1)
  effects(pure)
{ @Int.0 - @Int.1 }
""")

    def test_nat_minus_int_not_obligated(self) -> None:
        """`@Nat - @Int → @Int` carries no obligation.

        Per checker.py:264 the type rule promotes to the more general
        type when operands differ. `@Nat - @Int` becomes `@Int`
        because @Nat <: @Int, so the result is allowed to be negative.
        Author opted into Int semantics by mixing types.
        """
        _verify_ok("""
private fn mixed_sub(@Nat, @Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ @Nat.0 - @Int.0 }
""")

    def test_partial_requires_does_not_discharge(self) -> None:
        """`requires(@Nat.0 > 0)` alone does not discharge `@Nat.0 - @Nat.1`.

        The precondition rules out @Nat.0 == 0 but says nothing about
        @Nat.1 vs @Nat.0. Counterexample: @Nat.0 = 1, @Nat.1 = 5.
        """
        _verify_err("""
private fn partial_req(@Nat, @Nat -> @Nat)
  requires(@Nat.0 > 0)
  ensures(true)
  effects(pure)
{ @Nat.0 - @Nat.1 }
""", "underflow")

    def test_pure_literal_subtraction_not_flagged(self) -> None:
        """`0 - 1` (pure-literal "I want -1" idiom) is intentionally
        not flagged at Path A (#520) scope.

        The checker classifies non-negative literals as `@Nat`, so the
        subtraction is technically `@Nat - @Nat`. But the corpus uses
        this idiom widely in `Err(_) -> 0 - 1` and `throw(0 - 1)`
        positions where the result is consumed at `@Int` and upcast
        cleanly. Flagging would force a corpus-wide migration to
        negative literals (`-1`).

        The verifier therefore requires at least one operand to have
        Nat *provenance* (slot ref or function return), not just
        non-negative-literal classification. Pure-literal underflow
        consumed at a `@Nat` position (e.g. `let @Nat = 0 - 1`) would
        still escape — that is Path B (#552) territory.
        """
        _verify_ok("""
private fn negative_sentinel(@Unit -> @Int)
  requires(true)
  ensures(@Int.result < 0)
  effects(pure)
{ 0 - 1 }
""")


class TestNatBindingObligation552:
    """`@Int` narrowing into a `@Nat` slot carries a Tier-1 `value >= 0`
    obligation at every binding site (#552, generalising #520).

    Fires when the target slot is `@Nat` AND the bound value is not
    already statically `@Nat` — the single condition that keeps #552
    disjoint from #520's `@Nat - @Nat` subtraction obligation (a
    `@Nat - @Nat` value is already `@Nat`, so it is not a narrowing).
    Discharged from preconditions and path conditions; an undischarged
    narrowing fails with E503 and a counterexample.

    Projection sites whose *source* type the verifier cannot resolve
    statically — ADT sub-pattern binds (`Some(@Nat.0)`) and non-literal
    tuple destructures — are left to the Tier-3 codegen runtime guard.
    """

    # ---- Site 1: let bindings -------------------------------------
    def test_let_narrow_unguarded_fails(self) -> None:
        _verify_err("""
private fn f(@Int -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Nat = @Int.0;
  @Nat.0
}
""", "may be negative")

    def test_let_narrow_requires_discharges(self) -> None:
        _verify_ok("""
private fn f(@Int -> @Nat)
  requires(@Int.0 >= 0)
  ensures(true)
  effects(pure)
{
  let @Nat = @Int.0;
  @Nat.0
}
""")

    def test_let_narrow_if_guard_discharges(self) -> None:
        """Path condition `@Int.0 >= 0` discharges the let narrowing.

        Asserts the obligation actually *fired and verified* on the
        constrained path, not merely that no error surfaced — a regression
        that dropped the obligation would otherwise pass silently (#748
        review)."""
        result = _verify("""
private fn f(@Int -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  if @Int.0 >= 0 then {
    let @Nat = @Int.0;
    @Nat.0
  } else {
    0
  }
}
""")
        assert [d for d in result.diagnostics if d.severity == "error"] == []
        assert [o.status for o in result.obligations
                if o.kind == "nat_bind"] == ["verified"]

    def test_let_already_nat_not_flagged(self) -> None:
        """`let @Nat = @Nat.0` is Nat->Nat — no narrowing, no obligation."""
        result = _verify("""
private fn f(@Nat -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Nat = @Nat.0;
  @Nat.0
}
""")
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert errors == []
        assert not [o for o in result.obligations if o.kind == "nat_bind"]

    # ---- Site 2: call arguments -----------------------------------
    def test_call_arg_narrow_unguarded_fails(self) -> None:
        _verify_err("""
private fn takes_nat(@Nat -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{ @Nat.0 }

private fn f(@Int -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{ takes_nat(@Int.0) }
""", "may be negative")

    def test_call_arg_narrow_requires_discharges(self) -> None:
        _verify_ok("""
private fn takes_nat(@Nat -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{ @Nat.0 }

private fn f(@Int -> @Nat)
  requires(@Int.0 >= 0)
  ensures(true)
  effects(pure)
{ takes_nat(@Int.0) }
""")

    # ---- Site 3: constructor fields -------------------------------
    def test_ctor_field_narrow_unguarded_fails(self) -> None:
        _verify_err("""
private data Box { MkBox(Nat) }

private fn f(@Int -> @Box)
  requires(true)
  ensures(true)
  effects(pure)
{ MkBox(@Int.0) }
""", "may be negative")

    def test_ctor_field_narrow_requires_discharges(self) -> None:
        _verify_ok("""
private data Box { MkBox(Nat) }

private fn f(@Int -> @Box)
  requires(@Int.0 >= 0)
  ensures(true)
  effects(pure)
{ MkBox(@Int.0) }
""")

    # ---- Site 4: top-level match binds ----------------------------
    def test_match_bind_narrow_unguarded_fails(self) -> None:
        _verify_err("""
private fn f(@Int -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  match @Int.0 {
    @Nat -> @Nat.0
  }
}
""", "may be negative")

    def test_match_bind_narrow_requires_discharges(self) -> None:
        _verify_ok("""
private fn f(@Int -> @Nat)
  requires(@Int.0 >= 0)
  ensures(true)
  effects(pure)
{
  match @Int.0 {
    @Nat -> @Nat.0
  }
}
""")

    # ---- Site 6: literal-tuple destructure ------------------------
    def test_destructure_narrow_unguarded_fails(self) -> None:
        """Component 0 (`@Int.0`) narrows; component 1 (literal 5) does not."""
        _verify_err("""
private fn f(@Int -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  let Tuple<@Nat, @Nat> = Tuple(@Int.0, 5);
  @Nat.0
}
""", "may be negative")

    def test_destructure_narrow_requires_discharges(self) -> None:
        result = _verify("""
private fn f(@Int -> @Nat)
  requires(@Int.0 >= 0)
  ensures(true)
  effects(pure)
{
  let Tuple<@Nat, @Nat> = Tuple(@Int.0, 5);
  @Nat.0
}
""")
        assert [d for d in result.diagnostics if d.severity == "error"] == []
        assert [o.status for o in result.obligations
                if o.kind == "nat_bind"] == ["verified"]

    # ---- Double-emit disjointness with #520 -----------------------
    def test_nat_minus_nat_is_sub_not_bind(self) -> None:
        """`let @Nat = @Nat.0 - @Nat.1`: value already @Nat -> #520 only."""
        result = _verify("""
private fn f(@Nat, @Nat -> @Nat)
  requires(@Nat.0 >= @Nat.1)
  ensures(true)
  effects(pure)
{
  let @Nat = @Nat.0 - @Nat.1;
  @Nat.0
}
""")
        kinds = [o.kind for o in result.obligations]
        assert kinds.count("nat_bind") == 0, kinds
        assert kinds.count("nat_sub") == 1, kinds
        assert [d for d in result.diagnostics if d.severity == "error"] == []

    def test_int_minus_literal_is_bind_not_sub(self) -> None:
        """`let @Nat = @Int.0 - 100`: value @Int -> #552 only."""
        result = _verify("""
private fn f(@Int -> @Nat)
  requires(@Int.0 >= 100)
  ensures(true)
  effects(pure)
{
  let @Nat = @Int.0 - 100;
  @Nat.0
}
""")
        kinds = [o.kind for o in result.obligations]
        assert kinds.count("nat_bind") == 1, kinds
        assert kinds.count("nat_sub") == 0, kinds
        assert [d for d in result.diagnostics if d.severity == "error"] == []

    def test_nat_addition_not_flagged(self) -> None:
        """`let @Nat = @Nat.0 + @Nat.1`: value already @Nat, no obligation."""
        result = _verify("""
private fn f(@Nat, @Nat -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Nat = @Nat.0 + @Nat.1;
  @Nat.0
}
""")
        assert not [o for o in result.obligations if o.kind == "nat_bind"]

    def test_pure_literal_subtraction_caught(self) -> None:
        """`let @Nat = 0 - 1`: typed @Nat but valued -1.  #520 exempts the
        pure-literal subtraction (no @Nat provenance) and defers it here;
        #552 must catch it (E503)."""
        _verify_err("""
private fn f(@Unit -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Nat = 0 - 1;
  @Nat.0
}
""", "may be negative")

    def test_nonneg_literal_not_flagged(self) -> None:
        """`let @Nat = 5`: a non-negative literal is genuinely @Nat — no
        obligation.  The pure-literal carve-out is subtraction-only, so
        bare literals and additions don't fire."""
        result = _verify("""
private fn f(@Unit -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Nat = 5;
  @Nat.0
}
""")
        assert not [o for o in result.obligations if o.kind == "nat_bind"]

    def test_wrapped_underflow_subtraction_caught(self) -> None:
        """A pure-literal subtraction wrapped in a block / if-branch /
        match arm, or nested in arithmetic, still narrows a
        possibly-negative value into @Nat.  `_is_nat_typed` calls the
        wrapper @Nat, so a top-level-only check would miss these — the
        obligation must look through to the value-producing leaf
        (#552 review)."""
        for body in (
            "let @Nat = { 0 - 1 };\n  @Nat.0",
            "let @Nat = if @Int.0 >= 0 then { 5 } else { 0 - 1 };\n  @Nat.0",
            "let @Nat = match @Int.0 { @Int -> 0 - 1 };\n  @Nat.0",
            "let @Nat = (0 - 1) + (0 - 1);\n  @Nat.0",
        ):
            src = (
                "private fn f(@Int -> @Nat)\n"
                "  requires(true)\n"
                "  ensures(true)\n"
                "  effects(pure)\n"
                "{\n"
                "  " + body + "\n"
                "}\n"
            )
            _verify_err(src, "may be negative")

    def test_subpattern_bind_literal_nat_obligated(self) -> None:
        """An @Nat sub-pattern binding the @Int payload of a *literal*
        `Some(@Int.0)` narrows — #747 obligates the constructor argument
        directly (deferred pre-#747)."""
        _verify_err("""
private fn f(@Int -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  match Some(@Int.0) {
    Some(@Nat) -> @Nat.0,
    None -> 0
  }
}
""", "may be negative")

    def test_subpattern_bind_opaque_nat_obligated(self) -> None:
        """An @Nat sub-pattern binding a non-@Nat field of an *opaque*
        scrutinee (`match opt { Some(@Nat) -> }` on `Option<Int>`) narrows
        — #747 obligates the uninterpreted field accessor `>= 0`."""
        _verify_err("""
private fn f(@Option<Int> -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match @Option<Int>.0 {
    Some(@Nat) -> @Nat.0,
    None -> 0
  }
}
""", "may be negative")

    def test_subpattern_bind_already_nat_not_obligated(self) -> None:
        """A @Nat sub-pattern over an already-@Nat field (`Option<Nat>`)
        is not a narrowing — #747 must NOT obligate it (the accessor
        carries no `>= 0` fact, so a spurious obligation would fail)."""
        result = _verify("""
private fn f(@Option<Nat> -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  match @Option<Nat>.0 {
    Some(@Nat) -> @Nat.0,
    None -> 0
  }
}
""")
        assert not [o for o in result.obligations if o.kind == "nat_bind"]
        assert [d for d in result.diagnostics if d.severity == "error"] == []

    def test_generic_effect_op_formal_nat_obligated(self) -> None:
        """A generic effect-op formal instantiated to @Nat (`E<Nat>.wait`)
        narrows an @Int argument.  #747 makes the checker synthesise op
        arguments against their instantiated formal, recording the @Nat
        target, so the obligation now fires (deferred pre-#747)."""
        result = _verify("""
effect E<T> {
  op wait(T -> Unit);
}

public fn f(@Int -> @Unit)
  requires(true)
  ensures(true)
  effects(<E<Nat>>)
{
  E.wait(@Int.0)
}
""")
        assert [o for o in result.obligations if o.kind == "nat_bind"], \
            "expected a nat_bind obligation at the generic effect-op formal"
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert any("may be negative" in e.description.lower() for e in errors)

    def test_generic_effect_op_formal_nat_discharged(self) -> None:
        """The generic effect-op narrowing discharges from a precondition."""
        _verify_ok("""
effect E<T> {
  op wait(T -> Unit);
}

public fn f(@Int -> @Unit)
  requires(@Int.0 >= 0)
  ensures(true)
  effects(<E<Nat>>)
{
  E.wait(@Int.0)
}
""")

    def test_generic_function_formal_nat_obligated(self) -> None:
        """A generic function formal fixed to @Nat by a sibling argument
        (`pick(@Nat.0, @Int.0)` with `pick<T>(@T, @T -> @T)`) narrows the
        @Int argument into the @Nat-instantiated formal.  #747 recovers the
        instantiation from the target side-table (deferred pre-#747)."""
        result = _verify("""
private forall<T>
fn pick(@T, @T -> @T)
  requires(true)
  ensures(true)
  effects(pure)
{ @T.0 }

private fn f(@Nat, @Int -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{ pick(@Nat.0, @Int.0) }
""")
        assert [o for o in result.obligations if o.kind == "nat_bind"], \
            "expected a nat_bind obligation at the generic function formal"
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert any("may be negative" in e.description.lower() for e in errors)

    def test_generic_function_formal_nat_discharged(self) -> None:
        """The generic function-formal narrowing discharges from a
        precondition constraining the @Int argument."""
        _verify_ok("""
private forall<T>
fn pick(@T, @T -> @T)
  requires(true)
  ensures(true)
  effects(pure)
{ @T.0 }

private fn f(@Nat, @Int -> @Nat)
  requires(@Int.0 >= 0)
  ensures(true)
  effects(pure)
{ pick(@Nat.0, @Int.0) }
""")

    def test_generic_ctor_field_nat_obligated(self) -> None:
        """A generic constructor field instantiated to @Nat (`Some(@Int.0)`
        building an `Option<Nat>`) narrows an @Int into the @Nat field.
        #747 recovers the instantiation from the checker's *target*
        side-table, so the obligation now fires (deferred pre-#747)."""
        result = _verify("""
private fn f(@Int -> @Option<Nat>)
  requires(true)
  ensures(true)
  effects(pure)
{
  Some(@Int.0)
}
""")
        assert [o for o in result.obligations if o.kind == "nat_bind"], \
            "expected a nat_bind obligation at the generic constructor field"
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert any("may be negative" in e.description.lower() for e in errors)

    def test_generic_ctor_field_nat_discharged(self) -> None:
        """The generic constructor-field narrowing discharges from a
        precondition, exactly like the concrete-field case (#747)."""
        _verify_ok("""
private fn f(@Int -> @Option<Nat>)
  requires(@Int.0 >= 0)
  ensures(true)
  effects(pure)
{
  Some(@Int.0)
}
""")

    def test_non_literal_nat_destructure_not_obligated_yet(self) -> None:
        """A non-literal tuple-destructure source narrowing @Int into @Nat
        slots is not obligated (the projected source type isn't resolved
        here) — deferred to #747.  Pin the current behaviour (#748 review)."""
        result = _verify("""
private fn f(@Int -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  let Tuple<@Nat, @Nat> = if @Int.0 > 0 then { Tuple(@Int.0, @Int.0) } else { Tuple(@Int.0, @Int.0) };
  @Nat.0
}
""")
        assert not [o for o in result.obligations if o.kind == "nat_bind"]
        assert [d for d in result.diagnostics if d.severity == "error"] == []

    def test_caught_narrowing_carries_e503_and_nat_bind(self) -> None:
        """A caught narrowing is tagged E503 with a `nat_bind`-kind
        obligation — not merely a description substring (#552 review)."""
        result = _verify("""
private fn f(@Int -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Nat = @Int.0;
  @Nat.0
}
""")
        violated = [o for o in result.obligations
                    if o.kind == "nat_bind" and o.status == "violated"]
        assert len(violated) == 1, [o.kind for o in result.obligations]
        assert violated[0].error_code == "E503"
        # The counterexample must WITNESS the violation with a negative
        # @Int.0, not a model-completed default — pins the check_valid
        # model-before-pop fix, which a revert silently degrades to
        # @Int.0 = 0 (a non-witness for `value >= 0`) (#748 review).
        ce = violated[0].counterexample or {}
        assert "@Int.0" in ce and int(ce["@Int.0"]) < 0, ce

    def test_non_let_tier3_narrowing_warns_unguarded(self) -> None:
        """A non-let narrowing whose value the SMT layer can't translate
        (here `array_length` of an untranslatable string split) surfaces
        an E504 warning + a `tier3_unguarded` obligation — NOT a silent
        `tier3_runtime` 'runtime check', since codegen guards only the let
        site (#552 review / #747)."""
        result = _verify('''
public fn f(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  nat_to_int(array_length(string_lines("a\\nb")))
}
''')
        unguarded = [o for o in result.obligations
                     if o.status == "tier3_unguarded"]
        assert len(unguarded) == 1, [o.status for o in result.obligations]
        assert unguarded[0].error_code == "E504"
        warns = [d for d in result.diagnostics if d.error_code == "E504"]
        assert len(warns) == 1 and warns[0].severity == "warning"
        # excluded from the discharged totals (like a violation)
        assert not any(o.status == "tier3" for o in result.obligations
                       if o.kind == "nat_bind")

    def test_call_arg_nat_minus_nat_is_sub_not_bind(self) -> None:
        """A `@Nat - @Nat` *call argument* is #520's obligation (nat_sub),
        not #552's — the disjointness holds at a non-let site too, where
        the site walk (not just `_narrows_into_nat`) could regress
        (#552 review)."""
        result = _verify("""
private fn takes_nat(@Nat -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{ @Nat.0 }

private fn f(@Nat, @Nat -> @Nat)
  requires(@Nat.0 >= @Nat.1)
  ensures(true)
  effects(pure)
{ takes_nat(@Nat.0 - @Nat.1) }
""")
        kinds = [o.kind for o in result.obligations]
        assert kinds.count("nat_bind") == 0, kinds
        assert kinds.count("nat_sub") == 1, kinds
        assert [d for d in result.diagnostics if d.severity == "error"] == []

    def test_destructure_threads_cur_env_for_later_obligation(self) -> None:
        """After a literal destructure, a later statement's narrowing
        obligation must translate against the destructured slot, not a
        stale outer binding of the same slot name (CodeRabbit, PR #748).
        Both components are -5, so `takes_nat(@Int.0)` must fail (E503),
        proving the destructured value rather than the @Int param (which
        `requires(@Int.0 >= 0)` would have wrongly discharged)."""
        _verify_err("""
private fn takes_nat(@Nat -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{ @Nat.0 }

private fn f(@Int -> @Nat)
  requires(@Int.0 >= 0)
  ensures(true)
  effects(pure)
{
  let Tuple<@Int, @Int> = Tuple(0 - 5, 0 - 5);
  takes_nat(@Int.0)
}
""", "may be negative")

    def test_destructure_non_literal_source_invalidates_stale_binding(
        self,
    ) -> None:
        """A non-literal destructure source (here an `if`-expression) cannot
        pair each binding with a translatable component, so the destructured
        slots must be rebound to fresh vars — otherwise `takes_nat(@Int.0)`
        would wrongly discharge against the `@Int` param's
        `requires(@Int.0 >= 0)` instead of the unknown destructured value
        (CodeRabbit, PR #748)."""
        _verify_err("""
private fn takes_nat(@Nat -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{ @Nat.0 }

private fn f(@Int -> @Nat)
  requires(@Int.0 >= 0)
  ensures(true)
  effects(pure)
{
  let Tuple<@Int, @Int> = if @Int.0 > 0 then { Tuple(0 - 1, 0 - 1) } else { Tuple(1, 1) };
  takes_nat(@Int.0)
}
""", "may be negative")

    def test_let_non_translatable_source_invalidates_stale_binding(
        self,
    ) -> None:
        """An untranslatable `let` RHS (here `array_length(string_lines(...))`)
        rebinds the slot to a fresh var, so a later `takes_nat(@Int.0)` cannot
        falsely discharge against the `@Int` param's `requires(@Int.0 >= 0)` —
        the let-statement analogue of the destructure stale-binding fix
        (CodeRabbit, PR #748)."""
        _verify_err("""
private fn takes_nat(@Nat -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{ @Nat.0 }

private fn f(@Int -> @Nat)
  requires(@Int.0 >= 0)
  ensures(true)
  effects(pure)
{
  let @Int = array_length(string_lines("ab"));
  takes_nat(@Int.0)
}
""", "may be negative")

    def test_narrowing_inside_array_literal_caught(self) -> None:
        """A narrowing nested in an expression container (array literal)
        is visited by the walker, not skipped at the fallthrough
        (CodeRabbit, PR #748)."""
        _verify_err("""
private fn takes_nat(@Nat -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{ @Nat.0 }

private fn f(@Int -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Array<Nat> = [takes_nat(@Int.0)];
  0
}
""", "may be negative")

    def test_effect_op_argument_narrowing_caught(self) -> None:
        """An @Int narrowing into an effect operation's @Nat formal
        (`IO.sleep : Nat -> Unit`) is obligated — qualified calls were
        previously only recursed into, never checked against their
        formal parameter types (CodeRabbit, PR #748)."""
        _verify_err("""
public fn f(@Int -> @Unit)
  requires(true)
  ensures(true)
  effects(<IO>)
{
  IO.sleep(@Int.0)
}
""", "may be negative")

    def test_effect_op_argument_narrowing_discharged(self) -> None:
        """The effect-op narrowing verifies cleanly when the argument is
        constrained non-negative — guards against an over-conservative
        regression at the new binding site (CodeRabbit, PR #748)."""
        result = _verify("""
public fn f(@Int -> @Unit)
  requires(@Int.0 >= 0)
  ensures(true)
  effects(<IO>)
{
  IO.sleep(@Int.0)
}
""")
        assert [d for d in result.diagnostics if d.severity == "error"] == []
        assert [o.status for o in result.obligations
                if o.kind == "nat_bind"] == ["verified"]

    def test_user_effect_op_argument_narrowing_caught(self) -> None:
        """A user-declared effect operation with a @Nat parameter obligates
        an @Int argument the same as built-in IO.sleep. User effects must
        register their OpInfo (operations were previously stored empty), so
        lookup_effect_op exposes param_types (CodeRabbit, PR #748)."""
        _verify_err("""
effect E {
  op wait(Nat -> Unit);
}

public fn f(@Int -> @Unit)
  requires(true)
  ensures(true)
  effects(<E>)
{
  E.wait(@Int.0)
}
""", "may be negative")

    def test_user_effect_op_argument_narrowing_discharged(self) -> None:
        """The user-effect-op narrowing verifies cleanly when the argument
        is constrained non-negative — the discharged companion to
        test_user_effect_op_argument_narrowing_caught.  Asserts the
        `nat_bind` obligation actually fired and verified, not merely "no
        error" (CodeRabbit, PR #748)."""
        result = _verify("""
effect E {
  op wait(Nat -> Unit);
}

public fn f(@Int -> @Unit)
  requires(@Int.0 >= 0)
  ensures(true)
  effects(<E>)
{
  E.wait(@Int.0)
}
""")
        assert [d for d in result.diagnostics if d.severity == "error"] == []
        assert [o.status for o in result.obligations
                if o.kind == "nat_bind"] == ["verified"]


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
        assert result.summary.total == 4
        assert result.summary.tier1_verified == 4
        assert result.summary.tier3_runtime == 0

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

    # -- Branch-aware precondition checking (#283) -------------------------

    def test_call_precondition_satisfied_by_if_guard(self) -> None:
        """Call inside if-branch where branch condition implies precondition."""
        _verify_ok("""
private fn positive(@Int -> @Int)
  requires(@Int.0 > 0)
  ensures(true)
  effects(pure)
{ @Int.0 }

private fn caller(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  if @Int.0 > 0 then { positive(@Int.0) }
  else { 0 }
}
""")

    def test_call_precondition_with_else_guard(self) -> None:
        """Call inside else-branch where negated condition implies precondition."""
        _verify_ok("""
private fn non_negative(@Int -> @Int)
  requires(@Int.0 >= 0)
  ensures(true)
  effects(pure)
{ @Int.0 }

private fn caller(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  if @Int.0 < 0 then { 0 }
  else { non_negative(@Int.0) }
}
""")

    def test_recursive_call_guarded_by_if(self) -> None:
        """Recursive call guarded by if — the fizzbuzz pattern (#283).

        De Bruijn: @Nat.0 = counter (second param, most recent),
        @Nat.1 = limit (first param).  The recursive call passes
        limit first, counter+1 second: loop(@Nat.1, @Nat.0 + 1).
        """
        _verify_ok("""
private fn loop(@Nat, @Nat -> @Nat)
  requires(@Nat.0 <= @Nat.1)
  ensures(true)
  effects(pure)
{
  if @Nat.0 < @Nat.1 then {
    loop(@Nat.1, @Nat.0 + 1)
  } else { @Nat.0 }
}
""")

    def test_call_precondition_with_match_guard(self) -> None:
        """Call inside match arm with nested if-guard."""
        _verify_ok("""
private data Maybe {
  Nothing,
  Just(Int)
}

private fn use_positive(@Int -> @Int)
  requires(@Int.0 > 0)
  ensures(true)
  effects(pure)
{ @Int.0 }

private fn process(@Maybe -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match @Maybe.0 {
    Just(@Int) -> if @Int.0 > 0 then { use_positive(@Int.0) } else { 0 },
    Nothing -> 0
  }
}
""")

    def test_call_precondition_nested_if(self) -> None:
        """Nested if-branches compounding conditions."""
        _verify_ok("""
private fn bounded(@Int -> @Int)
  requires(@Int.0 > 0)
  requires(@Int.0 < 100)
  ensures(true)
  effects(pure)
{ @Int.0 }

private fn caller(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  if @Int.0 > 0 then {
    if @Int.0 < 100 then {
      bounded(@Int.0)
    } else { 0 }
  } else { 0 }
}
""")

    def test_call_precondition_violated_despite_branch(self) -> None:
        """Call violates precondition even inside an if-branch."""
        _verify_err("""
private fn positive(@Int -> @Int)
  requires(@Int.0 > 0)
  ensures(true)
  effects(pure)
{ @Int.0 }

private fn bad_caller(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  if @Int.0 > 10 then { positive(@Int.0) }
  else { positive(@Int.0) }
}
""", "precondition")


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
    ) -> ResolvedModule:
        """Build a ResolvedModule from source text."""
        prog = parse_to_ast(source)
        return ResolvedModule(
            path=path,
            file_path=Path(f"/fake/{'/'.join(path)}.vera"),
            program=prog,
            source=source,
        )

    @staticmethod
    def _verify_mod(
        source: str,
        modules: list[ResolvedModule],
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


# =====================================================================
# Phase A: Match + ADT verification tests
# =====================================================================

class TestMatchAndAdtVerification:
    """Tests for match expression and ADT constructor Z3 translation."""

    # -- Simple match on ADT -----------------------------------------------

    def test_match_trivial_nat_result(self) -> None:
        """Match on ADT with Nat result verifies postcondition."""
        source = """\
private data List<T> {
  Nil,
  Cons(T, List<T>)
}

private fn length(@List<Int> -> @Nat)
  requires(true)
  ensures(@Nat.result >= 0)
  effects(pure)
{
  match @List<Int>.0 {
    Nil -> 0,
    Cons(@Int, @List<Int>) -> 1 + length(@List<Int>.0)
  }
}
"""
        result = _verify(source)
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert errors == [], f"Unexpected errors: {[e.description for e in errors]}"
        # The ensures should be Tier 1 verified (not T3 fallback)
        warns_e522 = [d for d in result.diagnostics
                      if d.error_code == "E522"]
        assert warns_e522 == [], "Match body should be translatable (no E522)"

    def test_match_simple_int_result(self) -> None:
        """Match returning a simple int value is verifiable."""
        source = """\
private data Color {
  Red,
  Green,
  Blue
}

private fn color_value(@Color -> @Int)
  requires(true)
  ensures(@Int.result >= 0)
  effects(pure)
{
  match @Color.0 {
    Red -> 1,
    Green -> 2,
    Blue -> 3
  }
}
"""
        _verify_ok(source)

    def test_match_two_arm_postcondition(self) -> None:
        """Match with two arms can verify a specific postcondition."""
        source = """\
private data Bit {
  Zero,
  One
}

private fn bit_value(@Bit -> @Int)
  requires(true)
  ensures(@Int.result >= 0 && @Int.result <= 1)
  effects(pure)
{
  match @Bit.0 {
    Zero -> 0,
    One -> 1
  }
}
"""
        _verify_ok(source)

    def test_match_postcondition_violation(self) -> None:
        """Match with a wrong postcondition is caught."""
        source = """\
private data Bit {
  Zero,
  One
}

private fn bit_value(@Bit -> @Int)
  requires(true)
  ensures(@Int.result > 0)
  effects(pure)
{
  match @Bit.0 {
    Zero -> 0,
    One -> 1
  }
}
"""
        _verify_err(source, "does not hold")

    # -- Constructor translation -------------------------------------------

    def test_nullary_constructor_in_body(self) -> None:
        """Nullary constructors in function bodies are translatable."""
        source = """\
private data Maybe {
  Nothing,
  Just(Int)
}

private fn always_nothing(@Int -> @Maybe)
  requires(true)
  ensures(true)
  effects(pure)
{ Nothing }
"""
        _verify_ok(source)

    def test_constructor_call_in_body(self) -> None:
        """Constructor calls with args in function bodies are translatable."""
        source = """\
private data Maybe {
  Nothing,
  Just(Int)
}

private fn wrap(@Int -> @Maybe)
  requires(true)
  ensures(true)
  effects(pure)
{ Just(@Int.0) }
"""
        _verify_ok(source)

    # -- ADT parameter declarations ----------------------------------------

    def test_adt_param_declaration(self) -> None:
        """Functions with ADT parameters should declare proper Z3 vars."""
        source = """\
private data List<T> {
  Nil,
  Cons(T, List<T>)
}

private fn is_nil(@List<Int> -> @Bool)
  requires(true)
  ensures(true)
  effects(pure)
{
  match @List<Int>.0 {
    Nil -> true,
    Cons(@Int, @List<Int>) -> false
  }
}
"""
        _verify_ok(source)

    # -- The list_ops.vera example -----------------------------------------

    def test_list_ops_length_no_e522(self) -> None:
        """Ensure list_ops.vera length() no longer gets E522."""
        source = EXAMPLES_DIR / "list_ops.vera"
        if not source.exists():
            pytest.skip("list_ops.vera not found")
        text = source.read_text()
        ast = parse_to_ast(text)
        typecheck(ast, text)
        result = verify(ast, text, file=str(source))
        e522 = [d for d in result.diagnostics if d.error_code == "E522"]
        assert e522 == [], (
            f"list_ops.vera should not have E522 warnings: "
            f"{[d.description for d in e522]}"
        )


# =====================================================================
# Phase B: Decreases verification tests
# =====================================================================

class TestDecreasesVerification:
    """Tests for termination metric verification."""

    def test_simple_nat_decreases(self) -> None:
        """Simple Nat decreases on factorial is Tier 1."""
        source = """\
private fn factorial(@Nat -> @Nat)
  requires(true)
  ensures(@Nat.result >= 1)
  decreases(@Nat.0)
  effects(pure)
{
  if @Nat.0 == 0 then { 1 }
  else { @Nat.0 * factorial(@Nat.0 - 1) }
}
"""
        result = _verify(source)
        e525 = [d for d in result.diagnostics if d.error_code == "E525"]
        assert e525 == [], "Nat decreases should be verified (no E525)"
        assert result.summary.tier1_verified >= 3  # requires + ensures + decreases

    def test_nat_decreases_sum(self) -> None:
        """Nat decreases on a summation function is Tier 1."""
        source = """\
private fn sum_to(@Nat -> @Nat)
  requires(true)
  ensures(@Nat.result >= 0)
  decreases(@Nat.0)
  effects(pure)
{
  if @Nat.0 == 0 then { 0 }
  else { @Nat.0 + sum_to(@Nat.0 - 1) }
}
"""
        result = _verify(source)
        e525 = [d for d in result.diagnostics if d.error_code == "E525"]
        assert e525 == [], "Nat decreases should be verified (no E525)"

    def test_mutual_recursion_verified(self) -> None:
        """Mutual recursion decreases are now verified via where-block groups."""
        source = EXAMPLES_DIR / "mutual_recursion.vera"
        if not source.exists():
            pytest.skip("mutual_recursion.vera not found")
        text = source.read_text()
        ast = parse_to_ast(text)
        typecheck(ast, text)
        result = verify(ast, text, file=str(source))
        e525 = [d for d in result.diagnostics if d.error_code == "E525"]
        assert e525 == [], "Mutual recursion decreases should be verified"
        assert result.summary.tier3_runtime == 0

    def test_factorial_example_all_t1(self) -> None:
        """factorial.vera should have zero Tier 3 contracts."""
        source = EXAMPLES_DIR / "factorial.vera"
        if not source.exists():
            pytest.skip("factorial.vera not found")
        text = source.read_text()
        ast = parse_to_ast(text)
        typecheck(ast, text)
        result = verify(ast, text, file=str(source))
        assert result.summary.tier3_runtime == 0, (
            f"factorial.vera should have 0 T3, got {result.summary.tier3_runtime}"
        )


# =====================================================================
# Phase C: ADT decreases verification tests
# =====================================================================

class TestAdtDecreasesVerification:
    """Tests for ADT structural ordering in decreases clauses."""

    def test_list_length_decreases(self) -> None:
        """List length with structural decreases is Tier 1."""
        source = """\
private data List<T> {
  Nil,
  Cons(T, List<T>)
}

private fn length(@List<Int> -> @Nat)
  requires(true)
  ensures(@Nat.result >= 0)
  decreases(@List<Int>.0)
  effects(pure)
{
  match @List<Int>.0 {
    Nil -> 0,
    Cons(@Int, @List<Int>) -> 1 + length(@List<Int>.0)
  }
}
"""
        result = _verify(source)
        e525 = [d for d in result.diagnostics if d.error_code == "E525"]
        assert e525 == [], "ADT decreases should be verified (no E525)"
        assert result.summary.tier3_runtime == 0

    def test_list_sum_decreases(self) -> None:
        """List sum with structural decreases is Tier 1."""
        source = """\
private data List<T> {
  Nil,
  Cons(T, List<T>)
}

private fn sum(@List<Int> -> @Int)
  requires(true)
  ensures(true)
  decreases(@List<Int>.0)
  effects(pure)
{
  match @List<Int>.0 {
    Nil -> 0,
    Cons(@Int, @List<Int>) -> @Int.0 + sum(@List<Int>.0)
  }
}
"""
        result = _verify(source)
        e525 = [d for d in result.diagnostics if d.error_code == "E525"]
        assert e525 == [], "ADT decreases should be verified (no E525)"

    def test_list_ops_all_tier1(self) -> None:
        """list_ops.vera should have zero Tier 3 contracts."""
        source = EXAMPLES_DIR / "list_ops.vera"
        if not source.exists():
            pytest.skip("list_ops.vera not found")
        text = source.read_text()
        ast = parse_to_ast(text)
        typecheck(ast, text)
        result = verify(ast, text, file=str(source))
        assert result.summary.tier3_runtime == 0, (
            f"list_ops.vera should have 0 T3, got {result.summary.tier3_runtime}"
        )
        assert result.summary.tier1_verified == 8

    def test_overall_tier_counts(self) -> None:
        """All examples together: 255 T1 / 25 T3 / 280 total (current).

        Counts move when examples are added or their contracts become
        more / less verifiable.  Trajectory:

        * 184/23/207 baseline including `array_utilities.vera` (v0.0.117).
        * 213/26/239 after `string_utilities.vera` (#470 + #471 phase 1)
          contributed 29 T1 + 3 T3 + 32 contracts.
        * 219/26/245 after `nested_closures.vera` (#514, v0.0.121)
          contributed 6 T1 + 6 contracts.
        * 222/26/248 after #520 added @Nat subtraction underflow
          obligations.  factorial.vera (+1) and mutual_recursion.vera
          (+2) each have @Nat.0 - 1 sites that the verifier now
          discharges from path conditions.
        * 254/26/280 after `life.vera` (Stage 12 launch) contributed
          32 T1 + 32 contracts including the formal Conway B3/S23
          rule on `next_cell`.
        * 252/26/278 after v0.0.145 — `examples/closures.vera` shed
          the private `option_map` workaround (#604 fix); the removed
          shadow had a `requires(true) ensures(true)` pair
          contributing 2 T1 + 2 contracts that no longer appear.
        * 253/25/278 after v0.0.153 — #667 (SMT translator coverage
          for FloatLit / IndexExpr / ArrayLit).  The shift comes
          entirely from `examples/json.vera::main`'s contract
          relaxation: pre-#667 the body translation failed (FloatLit
          returned None), so the postcondition `ensures(@Int.result
          == 0)` dropped to Tier 3 with an E522 warning ("Cannot
          statically verify postcondition…") — counted in the 26
          T3.  Post-#667 the body translates fully and the verifier
          reaches the contradiction (helpers have `ensures(true)`,
          so `@Int.result == 0` isn't provable); the contract was
          honestly relaxed to `ensures(true)`, which trivially
          verifies T1.  Net: -1 T3 (was a T3-with-warning) + 1 T1
          (the relaxed `ensures(true)`) = +1 T1, -1 T3, total
          unchanged at 278.  No other example contract changed
          tier under #667.
        * 255/25/280 after `examples/read_char.vera` (#618 terminal
          implementation) added 2 T1 + 2 contracts — the trivial
          `requires(true) ensures(true)` on `main`.  Net: +2 T1,
          +2 total.
        * 256/28/284 after #552 generalised the @Nat `>= 0` invariant
          to all binding sites.  `json.vera` gains 1 T1 (a
          provably-safe @Int→@Nat narrowing).  `string_utilities.vera`
          gains 3 T3: each `nat_to_int(array_length(...))` narrows
          array_length's @Int result into nat_to_int's @Nat param, and
          array_length is untranslatable to Z3 so the `>= 0` obligation
          drops to a Tier-3 runtime guard.  Net: +1 T1, +3 T3, +4 total.
        * 256/25/281 after the #552 review round.  `string_utilities.vera`'s
          three `nat_to_int(array_length(...))` narrowings are non-`let`
          sites with no codegen runtime guard, so each is surfaced as an
          E504 `tier3_unguarded` warning and excluded from the totals
          (#747) rather than silently counted as a runtime check: -3 T3,
          -3 total, +3 tier3_unguarded.
        """
        t1 = t3 = total = t3u = 0
        for f in sorted(EXAMPLES_DIR.glob("*.vera")):
            text = f.read_text()
            prog = parse_to_ast(text)
            typecheck(prog, text)
            result = verify(prog, text, file=str(f))
            t1 += result.summary.tier1_verified
            t3 += result.summary.tier3_runtime
            total += result.summary.total
            t3u += sum(1 for o in result.obligations
                       if o.status == "tier3_unguarded")
        assert t1 == 256, f"Expected 256 T1, got {t1}"
        assert t3 == 25, f"Expected 25 T3, got {t3}"
        assert total == 281, f"Expected 281 total, got {total}"
        assert t3u == 3, f"Expected 3 tier3_unguarded, got {t3u}"


# =====================================================================
# Mutual recursion decreases verification tests
# =====================================================================

class TestMutualRecursionDecreases:
    """Verify decreases clauses for mutually recursive where-block functions."""

    def test_mutual_recursion_decreases_verified(self) -> None:
        """is_even/is_odd with matching decreases(@Nat.0) both verify."""
        source = """\
public fn is_even(@Nat -> @Bool)
  requires(true)
  ensures(true)
  decreases(@Nat.0)
  effects(pure)
{
  if @Nat.0 == 0 then { true } else { is_odd(@Nat.0 - 1) }
}
  where {
    fn is_odd(@Nat -> @Bool)
      requires(true)
      ensures(true)
      decreases(@Nat.0)
      effects(pure)
    {
      if @Nat.0 == 0 then { false } else { is_even(@Nat.0 - 1) }
    }
  }
"""
        result = _verify(source)
        e525 = [d for d in result.diagnostics if d.error_code == "E525"]
        assert e525 == [], f"Expected no E525, got {e525}"
        assert result.summary.tier3_runtime == 0

    def test_sibling_without_decreases_stays_tier3(self) -> None:
        """If a sibling has no decreases clause, caller stays Tier 3."""
        source = """\
public fn f(@Nat -> @Nat)
  requires(true)
  ensures(true)
  decreases(@Nat.0)
  effects(pure)
{
  if @Nat.0 == 0 then { 0 } else { g(@Nat.0 - 1) }
}
  where {
    fn g(@Nat -> @Nat)
      requires(true)
      ensures(true)
      effects(pure)
    {
      if @Nat.0 == 0 then { 0 } else { f(@Nat.0 - 1) }
    }
  }
"""
        result = _verify(source)
        e525 = [d for d in result.diagnostics if d.error_code == "E525"]
        assert len(e525) == 1, "f's decreases should be Tier 3 (sibling has none)"

    def test_where_block_contracts_verified(self) -> None:
        """Where-block functions have their own contracts verified."""
        source = """\
public fn outer(@Nat -> @Nat)
  requires(true)
  ensures(@Nat.result >= 0)
  effects(pure)
{
  helper(@Nat.0)
}
  where {
    fn helper(@Nat -> @Nat)
      requires(true)
      ensures(@Nat.result >= 0)
      effects(pure)
    {
      @Nat.0
    }
  }
"""
        result = _verify(source)
        # Both outer and helper have requires + ensures = 4 contracts
        assert result.summary.tier1_verified == 4
        assert result.summary.tier3_runtime == 0

    def test_mutual_recursion_example_all_t1(self) -> None:
        """mutual_recursion.vera should have zero Tier 3 contracts."""
        source = EXAMPLES_DIR / "mutual_recursion.vera"
        if not source.exists():
            pytest.skip("mutual_recursion.vera not found")
        text = source.read_text()
        prog = parse_to_ast(text)
        typecheck(prog, text)
        result = verify(prog, text, file=str(source))
        assert result.summary.tier3_runtime == 0
        # 8 contract obligations + 2 @Nat.0 - 1 underflow obligations
        # (#520) — both discharged from `if @Nat.0 == 0` path condition.
        assert result.summary.tier1_verified == 10


class TestStringLengthVerification:
    """string_length() on @String arguments uses z3.Length() — native Z3 string theory (Tier 1).

    The uninterpreted function path is only a fallback for non-SeqSort arguments and is
    never reached in practice now that String params are correctly declared as SeqSort.
    """

    def test_string_length_gt_zero_requires_tier1(self) -> None:
        """requires(string_length(@String.0) > 0) is verified Tier 1."""
        result = _verify("""
private fn non_empty(@String -> @Int)
  requires(string_length(@String.0) > 0)
  ensures(true)
  effects(pure)
{
  string_length(@String.0)
}
""")
        assert result.summary.tier1_verified >= 1
        assert result.summary.tier3_runtime == 0

    def test_string_length_ensures_tier1(self) -> None:
        """ensures(@Int.result >= 0) on string_length return is verified Tier 1."""
        result = _verify("""
private fn get_length(@String -> @Int)
  requires(true)
  ensures(@Int.result >= 0)
  effects(pure)
{
  string_length(@String.0)
}
""")
        assert result.summary.tier1_verified >= 1
        assert result.summary.tier3_runtime == 0

    def test_string_length_comparison_tier1(self) -> None:
        """string_length in both requires and ensures resolves to Tier 1."""
        result = _verify("""
private fn longer_than(@String, @Int -> @Bool)
  requires(@Int.0 >= 0)
  ensures(string_length(@String.0) >= 0)
  effects(pure)
{
  string_length(@String.0) > @Int.0
}
""")
        assert result.summary.tier1_verified >= 2
        assert result.summary.tier3_runtime == 0


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

    def test_float_is_nan_stays_tier3(self) -> None:
        """float_is_nan stays Tier 3: Float64 maps to reals; BoolVal(False) would be unsound."""
        result = _verify("""
private fn safe_sqrt(@Float64 -> @Float64)
  requires(!float_is_nan(@Float64.0))
  ensures(true)
  effects(pure)
{
  @Float64.0
}
""")
        assert result.summary.tier3_runtime >= 1

    def test_float_is_infinite_stays_tier3(self) -> None:
        """float_is_infinite stays Tier 3 for the same soundness reason as float_is_nan."""
        result = _verify("""
private fn finite_only(@Float64 -> @Float64)
  requires(!float_is_infinite(@Float64.0))
  ensures(true)
  effects(pure)
{
  @Float64.0
}
""")
        assert result.summary.tier3_runtime >= 1


class TestRefinedTypeParamSorts:
    """Refinement types over Bool/String/Float64 use the correct Z3 sort."""

    def test_refined_string_param_string_predicate_tier1(self) -> None:
        """RefinedType(STRING) param uses SeqSort — string predicates resolve to Tier 1.

        Without the RefinedType branch in _is_string_type, the parameter falls through to
        declare_int (IntSort) and string_length uses the uninterpreted function, which cannot
        prove string_length(@NonEmptyString.0) > 0 even with the requires assumption (Tier 3).
        With the fix, z3.Length() is used and Z3 proves the ensures from the requires (Tier 1).
        """
        result = _verify("""
type NonEmptyString = { @String | string_length(@String.0) > 0 };

private fn pass_through(@NonEmptyString -> @Bool)
  requires(string_length(@NonEmptyString.0) > 0)
  ensures(@Bool.result)
  effects(pure)
{
  string_length(@NonEmptyString.0) > 0
}
""")
        assert result.summary.tier3_runtime == 0

    def test_refined_float64_param_verifies_cleanly(self) -> None:
        """RefinedType(FLOAT64) param uses RealSort — function verifies without sort errors.

        Without the RefinedType branch in _is_float64_type, the parameter falls through to
        declare_int (IntSort). With the fix, declare_float64 (RealSort) is used, matching the
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
