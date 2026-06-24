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


def _nat_sub_status(source: str) -> list[str]:
    """Statuses of the `nat_sub` (#520/E502) obligations for *source*.

    Helper for the shadow/projection audit battery
    (:class:`TestShadowAuditSubtraction680`): returns one status string per
    recorded `@Nat`-subtraction site so a test can assert the tier directly.
    """
    result = _verify(source)
    return [o.status for o in result.obligations if o.kind == "nat_sub"]


# A non-literal `@Tuple<Nat, Nat>` source (a call) for the subtraction audit
# battery: destructuring it yields two OPAQUE `@Nat` shadows, so a downstream
# subtraction over them exercises the tracked-shadow / `_contains_opaque_shadow`
# path (see :class:`TestShadowAuditSubtraction680`).
_MK = """
private fn mk(@Nat -> @Tuple<Nat, Nat>)
  requires(true)
  ensures(true)
  effects(pure)
{ Tuple(@Nat.0, @Nat.0) }
"""


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

    def test_unsafe_sub_stmt_position_obligated(self) -> None:
        """A `@Nat - @Nat` in STATEMENT position (result discarded) still carries
        the underflow obligation — the subtraction walker recurses into the
        block's `ExprStmt` statements.  Pins the statement-position path the
        same way #730 closes it for call preconditions."""
        _verify_err("""
private fn stmt_sub(@Nat, @Nat -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{ @Nat.0 - @Nat.1; 0 }
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

    def test_compound_shadow_subtraction_is_tier3_not_e502(self) -> None:
        """A subtraction where BOTH operands are compound expressions embedding
        opaque shadows must fall to Tier-3, not a false E502.  After a
        non-literal destructure shadows both `@Nat` components, `(@Nat.0 + 1) -
        (@Nat.1 + 1)` has neither operand a *direct* shadow, so the direct
        guard misses it — `_contains_opaque_shadow` catches the embedded
        shadows (PR #778 review, the subtraction analogue of the E526
        compound-divisor fix)."""
        result = _verify("""
private fn mksub(@Nat -> @Tuple<Nat, Nat>)
  requires(true)
  ensures(true)
  effects(pure)
{ Tuple(@Nat.0, @Nat.0) }

private fn sub_compound(@Nat -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{ let Tuple<@Nat, @Nat> = mksub(@Nat.0); (@Nat.0 + 1) - (@Nat.1 + 1) }
""")
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert errors == [], [e.error_code for e in errors]
        subs = [o for o in result.obligations if o.kind == "nat_sub"]
        assert len(subs) == 1 and subs[0].status == "tier3", [
            (o.kind, o.status) for o in subs
        ]


class TestPrimitiveDivisionObligation680:
    """`a / b` and `a % b` (Int/Nat) carry a Tier-1 `b != 0` obligation (#680).

    Integer division and modulo by zero trap at runtime (`i64.div_s` /
    `i64.rem_s`).  The divisor lives in the Tier-1 decidable fragment
    (concrete integer arithmetic), so the obligation mirrors `@Nat`
    subtraction (#520): discharged from a precondition, path condition, or
    refinement type at Tier 1; a counterexample (`b = 0`) is a loud E526.

    Two exemptions: float division (`@Float64 / @Float64`) is Real-sorted
    and produces inf/NaN rather than trapping, so it is not obligated; and
    a non-zero integer literal divisor (`x / 5`) is trivially safe, mirroring
    #520's pure-literal exemption.
    """

    def test_unguarded_int_division_fails(self) -> None:
        """Bare `@Int.0 / @Int.1` without a guarding `requires` → E526.

        Counterexample: @Int.1 = 0.  This is silent/clean pre-#680.
        """
        _verify_err("""
private fn unsafe_div(@Int, @Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ @Int.0 / @Int.1 }
""", "by zero")

    def test_unguarded_int_modulo_fails(self) -> None:
        """Bare `@Int.0 % @Int.1` carries the same `@Int.1 != 0` obligation."""
        _verify_err("""
private fn unsafe_mod(@Int, @Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ @Int.0 % @Int.1 }
""", "by zero")

    def test_unguarded_nat_division_fails(self) -> None:
        """`@Nat.0 / @Nat.1` — a @Nat divisor can still be 0 → E526."""
        _verify_err("""
private fn unsafe_nat_div(@Nat, @Nat -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{ @Nat.0 / @Nat.1 }
""", "by zero")

    def test_requires_nonzero_divisor_discharges(self) -> None:
        """`requires(@Int.1 != 0)` discharges the obligation at Tier 1."""
        _verify_ok("""
private fn safe_div(@Int, @Int -> @Int)
  requires(@Int.1 != 0)
  ensures(true)
  effects(pure)
{ @Int.0 / @Int.1 }
""")

    def test_requires_nonzero_divisor_discharges_modulo(self) -> None:
        """`requires(@Int.1 != 0)` discharges a modulo obligation too."""
        _verify_ok("""
private fn safe_mod(@Int, @Int -> @Int)
  requires(@Int.1 != 0)
  ensures(true)
  effects(pure)
{ @Int.0 % @Int.1 }
""")

    def test_if_guard_divisor_discharges(self) -> None:
        """Path condition `@Int.1 != 0` (else branch of `if @Int.1 == 0`)
        discharges `@Int.0 / @Int.1`.  This is the `checked_div` shape used
        in examples/effect_handler.vera."""
        _verify_ok("""
private fn guarded_div(@Int, @Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  if @Int.1 == 0 then {
    0
  } else {
    @Int.0 / @Int.1
  }
}
""")

    def test_posint_refinement_divisor_discharges(self) -> None:
        """A `@PosInt = {@Int | @Int.0 > 0}` divisor discharges `> 0 ⟹ != 0`."""
        _verify_ok("""
type PosInt = { @Int | @Int.0 > 0 };

private fn refined_div(@Int, @PosInt -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ @Int.0 / @PosInt.0 }
""")

    def test_nonzero_literal_divisor_not_flagged(self) -> None:
        """`@Int.0 / 5` — a non-zero literal divisor is trivially safe and
        exempt (mirrors #520's pure-literal exemption); no obligation, so a
        bare `requires(true)` still verifies."""
        _verify_ok("""
private fn div_by_five(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ @Int.0 / 5 }
""")

    def test_float_division_not_obligated(self) -> None:
        """`@Float64.0 / @Float64.1` produces inf/NaN, not a trap — float
        division (Real-sorted divisor) carries no by-zero obligation."""
        _verify_ok("""
private fn float_div(@Float64, @Float64 -> @Float64)
  requires(true)
  ensures(true)
  effects(pure)
{ @Float64.0 / @Float64.1 }
""")

    def test_float64_shadow_divisor_records_no_obligation(self) -> None:
        """A `@Float64` divisor that is opaque (a non-literal destructure
        shadow, so `translate_expr`/the shadow path fires before the Real-sort
        check) must record NO `div_zero` obligation — float division is exempt
        regardless of translatability (`f64.div` by zero is inf/NaN, not a
        trap).  The float exemption keys on the divisor's resolved TYPE up
        front, before the None/shadow recordings (PR #778 review)."""
        result = _verify("""
private fn mk(@Float64 -> @Tuple<Float64, Float64>)
  requires(true)
  ensures(true)
  effects(pure)
{ Tuple(@Float64.0, @Float64.0) }

private fn fdiv(@Float64 -> @Float64)
  requires(true)
  ensures(true)
  effects(pure)
{ let Tuple<@Float64, @Float64> = mk(@Float64.0); @Float64.0 / @Float64.1 }
""")
        divs = [o for o in result.obligations if o.kind == "div_zero"]
        assert divs == [], [(o.kind, o.status) for o in divs]

    def test_partial_requires_does_not_discharge(self) -> None:
        """`requires(@Int.0 != 0)` constrains the numerator, not the divisor
        `@Int.1` — the obligation still fires."""
        _verify_err("""
private fn wrong_guard(@Int, @Int -> @Int)
  requires(@Int.0 != 0)
  ensures(true)
  effects(pure)
{ @Int.0 / @Int.1 }
""", "by zero")

    def test_division_obligation_recorded_div_zero_kind(self) -> None:
        """A guarded division records exactly one `div_zero` obligation,
        discharged (verified)."""
        result = _verify("""
private fn safe_div(@Int, @Int -> @Int)
  requires(@Int.1 != 0)
  ensures(true)
  effects(pure)
{ @Int.0 / @Int.1 }
""")
        div = [o for o in result.obligations if o.kind == "div_zero"]
        assert len(div) == 1, f"expected one div_zero obligation, got {len(div)}"
        assert div[0].status == "verified"

    def test_division_inside_array_literal_fires(self) -> None:
        """An unguarded division in an array-literal element is obligated
        (E526) — the walker recurses into `ArrayLit` elements, so the
        compile-error promise holds outside direct position too (#680 review)."""
        _verify_err("""
private fn arr_div(@Int, @Int -> @Array<Int>)
  requires(true)
  ensures(true)
  effects(pure)
{ [@Int.0 / @Int.1, 99] }
""", "by zero")

    def test_division_inside_assert_fires(self) -> None:
        """An unguarded division in an `assert` condition is obligated (E526)
        — the walker recurses into Assert/Assume conditions (#680 review)."""
        _verify_err("""
private fn assert_div(@Int, @Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ assert(@Int.0 / @Int.1 > 0); @Int.0 }
""", "by zero")

    def test_safe_destructured_divisor_not_flagged(self) -> None:
        """A destructured non-zero divisor (`Tuple(10, 5)`) must NOT be a false
        E526.  The destructured slots are not rebound to fresh unconstrained
        vars — a fresh `@Int` has no `!= 0` invariant (unlike a `@Nat`'s
        `>= 0`), so rebinding would make the safe `5` divisor look like a
        possible zero.  (Regression guard for the #680 review's destructure
        walk.)"""
        _verify_ok("""
private fn ld_safe(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ let Tuple<@Int, @Int> = Tuple(10, 5); @Int.0 / @Int.1 }
""")

    def test_division_inside_letdestruct_value_fires(self) -> None:
        """An unguarded division in a `let`-destructure value
        (`let Tuple<...> = Tuple(@Int.0 / @Int.1, ...)`) is obligated (E526) —
        the block walker walks the destructured value (#680 review)."""
        _verify_err("""
private fn ld_div(@Int, @Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ let Tuple<@Int, @Int> = Tuple(@Int.0 / @Int.1, 5); @Int.0 }
""", "by zero")

    def test_untranslatable_let_divisor_not_falsely_discharged(self) -> None:
        """An untranslatable scalar `let` (a `random_int` effect result the SMT
        layer doesn't model) that shadows a constrained outer must NOT let the
        outer's `requires(@Int.0 != 0)` falsely discharge a division by it.
        `requires(@Int.0 != 0); let @Int = random_int(0, 10); 1 / @Int.0` —
        random_int can be 0, so the division is unsafe and must be honest Tier-3
        (the shadowed value is unknown), not a false Tier-1 (#680 review).  This
        is the silent-failure differential: before the shadow fix it verified
        clean (Tier-1) yet trapped at runtime."""
        result = _verify("""
public fn f(@Int -> @Int)
  requires(@Int.0 != 0)
  ensures(true)
  effects(<Random>)
{ let @Int = random_int(0, 10); 1 / @Int.0 }
""")
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert errors == [], f"expected no error, got: {[e.description for e in errors]}"
        div = [o for o in result.obligations if o.kind == "div_zero"]
        assert len(div) == 1 and div[0].status == "tier3", (
            "divisor must be honest Tier-3 (the shadowed let value is unknown), "
            f"got {[(o.kind, o.status) for o in div]}"
        )

    def test_division_inside_interpolated_string_fires(self) -> None:
        r"""An unguarded division in an interpolated-string expression
        (`"x: \(@Int.0 / @Int.1)"`) is obligated (E526) — the walker recurses
        into InterpolatedString parts, mirroring the @Nat-binding walker
        (#680 review)."""
        _verify_err(
            'private fn interp_div(@Int, @Int -> @String)\n'
            '  requires(true)\n'
            '  ensures(true)\n'
            '  effects(pure)\n'
            '{ "x: \\(@Int.0 / @Int.1)" }\n',
            "by zero",
        )

    def test_div_by_zero_fix_hint_renders_actual_divisor(self) -> None:
        """The E526 fix hint names the *actual* divisor, not a fixed slot.

        For `@Int.1 / @Int.0` the divisor is `@Int.0` (De Bruijn: most
        recent binding).  The pre-review hint hard-coded `@Int.1 != 0`,
        which points at the wrong parameter here; `format_expr(expr.right)`
        renders the real operand (PR #778 review, `verifier.py` E526 hint).
        """
        matched = _verify_err("""
private fn wrong_slot_div(@Int, @Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ @Int.1 / @Int.0 }
""", "by zero")
        fix = matched[0].fix
        assert "@Int.0 != 0" in fix, fix
        assert "@Int.1" not in fix, fix

    def test_literal_destructure_divisor_discharges_at_tier1(self) -> None:
        """A divisor projected from a literal-constructor destructure is
        Tier-1, not Tier-3.  `let Tuple<@Int, @Int> = Tuple(10, 6);
        @Int.0 / @Int.1` discharges `10 != 0` — the divisor `@Int.1` is the
        literal first component — rather than shadowing it to an opaque
        Tier-3 value (PR #778 review: rebind translatable components to
        their projected terms, mirroring the @Nat-binding walker)."""
        result = _verify("""
private fn lit_destr_div(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ let Tuple<@Int, @Int> = Tuple(10, 6); @Int.0 / @Int.1 }
""")
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert errors == [], [e.error_code for e in errors]
        divs = [o for o in result.obligations if o.kind == "div_zero"]
        assert len(divs) == 1 and divs[0].status == "verified", [
            (o.kind, o.status) for o in divs
        ]

    def test_nonliteral_destructure_divisor_stays_tier3(self) -> None:
        """A divisor from a NON-literal destructure source (a call) can't be
        projected, so each component stays a tracked opaque shadow → Tier-3,
        never a false E526.  Guards the 77d90fb regression: a bare fresh
        `@Int` slot var carries no `!= 0` invariant and false-fired E526."""
        result = _verify("""
private fn mk(@Int -> @Tuple<Int, Int>)
  requires(true)
  ensures(true)
  effects(pure)
{ Tuple(@Int.0, @Int.0) }

private fn nonlit_destr_div(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ let Tuple<@Int, @Int> = mk(@Int.0); @Int.0 / @Int.1 }
""")
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert errors == [], [e.error_code for e in errors]
        divs = [o for o in result.obligations if o.kind == "div_zero"]
        assert len(divs) == 1 and divs[0].status == "tier3", [
            (o.kind, o.status) for o in divs
        ]

    def test_untranslatable_destructure_component_keeps_debruijn(self) -> None:
        """An untranslatable destructured component with NO stale outer must
        still push a tracked placeholder, so same-type De Bruijn positions
        don't collapse.  `let Tuple<@Int, @Int> = Tuple(10, random_int(0, 10));
        1 / @Int.0` must be Tier-3: `@Int.0` is the *opaque second component*,
        not the literal `10` it would shift onto if the component were skipped
        (PR #778 review, `verifier.py` De Bruijn collapse).  A skip here is a
        silent false-discharge — the worst #680 failure class."""
        result = _verify("""
private fn debruijn_keep(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(<Random>)
{ let Tuple<@Int, @Int> = Tuple(10, random_int(0, 10)); 1 / @Int.0 }
""")
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert errors == [], [e.error_code for e in errors]
        divs = [o for o in result.obligations if o.kind == "div_zero"]
        assert len(divs) == 1 and divs[0].status == "tier3", [
            (o.kind, o.status) for o in divs
        ]

    def test_compound_shadow_divisor_is_tier3_not_e526(self) -> None:
        """A divisor that *contains* an opaque shadow (`shadow + 1`), not just
        one that IS a shadow, must fall to Tier-3 — Z3 must not pick
        `shadow = -1` and emit a false E526.  `let @Int = random_int(0, 10);
        1 / (@Int.0 + 1)` shadows the outer `@Int.0`, so the compound divisor
        is opaque (PR #778 review, `verifier.py` `_contains_opaque_shadow`)."""
        result = _verify("""
private fn compound_shadow(@Int -> @Int)
  requires(@Int.0 != 0)
  ensures(true)
  effects(<Random>)
{ let @Int = random_int(0, 10); 1 / (@Int.0 + 1) }
""")
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert errors == [], [e.error_code for e in errors]
        divs = [o for o in result.obligations if o.kind == "div_zero"]
        assert len(divs) == 1 and divs[0].status == "tier3", [
            (o.kind, o.status) for o in divs
        ]

    def test_opaque_match_scrutinee_shadows_arm_bindings(self) -> None:
        """A match arm binding over an UNTRANSLATABLE scrutinee (an effect op)
        must shadow its pattern slots, so a primitive op in the arm falls to
        Tier-3 — never discharged against a stale same-name outer slot.
        Without it, `match Source.next(()) { Some(@Int) -> 1 / @Int.0 }` under
        `requires(@Int.0 != 0)` silently verifies `1 / @Int.0` against the
        *outer* param's `!= 0` while the matched field can be 0 — a silent
        false-discharge (PR #778 review, outside-diff; the match-arm analogue
        of the untranslatable-`let` shadow, mirroring `_fresh_pattern_env`)."""
        result = _verify("""
effect Source {
  op next(Unit -> Option<Int>);
}

private fn opaque_match(@Int -> @Int)
  requires(@Int.0 != 0)
  ensures(true)
  effects(<Source>)
{
  match Source.next(()) {
    Some(@Int) -> 1 / @Int.0,
    None -> 1
  }
}
""")
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert errors == [], [e.error_code for e in errors]
        divs = [o for o in result.obligations if o.kind == "div_zero"]
        assert len(divs) == 1 and divs[0].status == "tier3", [
            (o.kind, o.status) for o in divs
        ]


class TestPrimitiveIndexObligation680:
    """`arr[i]` carries a `0 <= i < array_length(arr)` obligation (#680).

    Array indexing traps at runtime (codegen emits a bounds check +
    `unreachable`).  Unlike division, the array length is an *uninterpreted*
    SMT function — spec §6.4.3 documents array bounds as needing reasoning
    beyond the Tier-1 decidable fragment (#427).  So the verifier uses a
    two-check: provably in bounds (a literal/refinement/precondition pins
    the length) → Tier 1; provably *out* of bounds (statically-known length
    the index exceeds, e.g. `[1,2,3][5]`) → loud E527; otherwise (opaque /
    dynamic length) → honest Tier 3, guarded by the runtime trap.  An
    unguarded dynamic index is therefore NOT an error — it degrades
    gracefully, never silently.

    String indexing is a type error (E161 "Cannot index String"), so there
    is no string-index obligation — `IndexExpr` is array-only.

    Index sites inside closure / quantifier bodies are intentionally not
    walked (the captured length is beyond Tier 1 without #427); they remain
    runtime-guarded.  `test_index_inside_closure_not_obligated` pins that.
    """

    def test_literal_in_bounds_index_discharges(self) -> None:
        """`[10, 20, 30][1]` — literal length 3, index 1 < 3 → Tier 1, no error."""
        _verify_ok("""
private fn second(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ [10, 20, 30][1] }
""")

    def test_literal_out_of_bounds_index_fails(self) -> None:
        """`[1, 2, 3][5]` — provably out of bounds (5 >= 3) → loud E527."""
        _verify_err("""
private fn oob(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ [1, 2, 3][5] }
""", "out of bounds")

    def test_requires_guarded_index_discharges(self) -> None:
        """`requires(@Nat.0 < array_length(@Array<Int>.0))` discharges the
        bounds obligation at Tier 1."""
        _verify_ok("""
private fn at(@Array<Int>, @Nat -> @Int)
  requires(@Nat.0 < array_length(@Array<Int>.0))
  ensures(true)
  effects(pure)
{ @Array<Int>.0[@Nat.0] }
""")

    def test_if_guard_index_discharges(self) -> None:
        """`if @Nat.0 < array_length(arr) then arr[@Nat.0] else 0` — the
        then-branch path condition discharges the bounds obligation at Tier 1.
        The complementary `>= ... then 0 else arr[...]` shape (used in
        examples/life.vera) discharges via the negated else-branch condition."""
        _verify_ok("""
private fn at(@Array<Int>, @Nat -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ if @Nat.0 < array_length(@Array<Int>.0) then { @Array<Int>.0[@Nat.0] } else { 0 } }
""")

    def test_refinement_nonempty_array_index_is_tier3(self) -> None:
        """A `@NonEmptyArray` refinement index is honest Tier 3, not an error.

        The `array_length(@Array<Int>.0) > 0` predicate is over a non-primitive
        (Array) base that Z3 cannot decide at Tier 1 (the same reason the
        refinement narrowing itself is a Tier-3 E506; see
        examples/refinement_types.vera and TestAdtDecreasesVerification's tier
        ledger).  So the `[0]` access degrades to a runtime-guarded Tier 3 —
        no error, never silent.  Lifting this to Tier 1 is #427 (Tier-2 array
        reasoning)."""
        result = _verify("""
type NonEmptyArray = { @Array<Int> | array_length(@Array<Int>.0) > 0 };

private fn head(@NonEmptyArray -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ @NonEmptyArray.0[0] }
""")
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert errors == [], f"expected no error, got: {[e.description for e in errors]}"
        idx = [o for o in result.obligations if o.kind == "index_bounds"]
        assert len(idx) == 1 and idx[0].status == "tier3"

    def test_opaque_unguarded_index_is_tier3(self) -> None:
        """An unguarded index into a dynamic-length array is NOT an error —
        the length is opaque (beyond Tier 1), so it degrades to Tier 3,
        guarded by the runtime trap.  This is the honest-tiering differential:
        the obligation is RECORDED as tier3, not silently dropped.  (A wrong
        fix that emitted nothing would pass the no-error check but fail the
        obligation-recorded assertion.)"""
        result = _verify("""
private fn at(@Array<Int>, @Nat -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ @Array<Int>.0[@Nat.0] }
""")
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert errors == [], f"expected no error (Tier-3), got: {[e.description for e in errors]}"
        idx = [o for o in result.obligations if o.kind == "index_bounds"]
        assert len(idx) == 1, f"expected one index_bounds obligation, got {len(idx)}"
        assert idx[0].status == "tier3"

    def test_index_inside_closure_not_obligated(self) -> None:
        """An index inside an `array_map` closure body (a captured array) is
        NOT obligated — the walker does not recurse into closure bodies, where
        the captured length is beyond Tier 1 (#427).  Pinned via a differential:
        the closure body records ZERO index_bounds obligations.  A `_verify_ok`
        alone would NOT catch a walker that started recursing into AnonFn —
        the captured index degrades to honest Tier 3 (no error) — so we assert
        the obligation count directly.  (Mirrors ch05_capture_array_index.)"""
        result = _verify("""
private fn step_flat(@Array<Int> -> @Array<Int>)
  requires(true)
  ensures(true)
  effects(pure)
{ array_map(@Array<Int>.0, fn(@Int -> @Int) effects(pure) { @Array<Int>.0[0] }) }
""")
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert errors == [], f"expected no error, got: {[e.description for e in errors]}"
        idx = [o for o in result.obligations if o.kind == "index_bounds"]
        assert idx == [], f"closure-body index must not be obligated, got {len(idx)}"

    def test_index_obligation_recorded_index_bounds_kind(self) -> None:
        """A guarded index records exactly one `index_bounds` obligation,
        discharged (verified)."""
        result = _verify("""
private fn at(@Array<Int>, @Nat -> @Int)
  requires(@Nat.0 < array_length(@Array<Int>.0))
  ensures(true)
  effects(pure)
{ @Array<Int>.0[@Nat.0] }
""")
        idx = [o for o in result.obligations if o.kind == "index_bounds"]
        assert len(idx) == 1, f"expected one index_bounds obligation, got {len(idx)}"
        assert idx[0].status == "verified"

    def test_literal_index_equal_length_fails(self) -> None:
        """`[1, 2, 3][3]` — index exactly equal to the length is out of bounds
        → E527.  Pins the strict `<` in `i < length` (an off-by-one `<=` would
        let `[1,2,3][3]` through)."""
        _verify_err("""
private fn at_len(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ [1, 2, 3][3] }
""", "out of bounds")

    def test_provably_negative_index_fails(self) -> None:
        """`[1, 2, 3][0 - 1]` — a provably-negative index is out of bounds
        regardless of length → E527.  Pins the lower-bound (`i >= 0`)
        conjunct."""
        _verify_err("""
private fn at_neg(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ [1, 2, 3][0 - 1] }
""", "out of bounds")

    def test_int_index_upper_bound_only_guard_is_tier3(self) -> None:
        """A signed `@Int` index guarded ONLY on the upper bound
        (`requires(@Int.0 < array_length(...))`, no `>= 0`) is NOT proven —
        the index could be negative, so it stays honest Tier 3, not a false
        Tier-1.  If the obligation's `i >= 0` conjunct were dropped this would
        wrongly verify; the differential pins it."""
        result = _verify("""
private fn at_int(@Array<Int>, @Int -> @Int)
  requires(@Int.0 < array_length(@Array<Int>.0))
  ensures(true)
  effects(pure)
{ @Array<Int>.0[@Int.0] }
""")
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert errors == [], f"expected no error (Tier-3), got: {[e.description for e in errors]}"
        idx = [o for o in result.obligations if o.kind == "index_bounds"]
        assert len(idx) == 1 and idx[0].status == "tier3"

    def test_op_inside_index_is_walked(self) -> None:
        """An unguarded division in the index sub-expression is obligated
        (E526) — the walker recurses into `expr.index` before checking the
        bound, so a trap buried in the index isn't silently lost."""
        _verify_err("""
private fn idx_div(@Array<Int>, @Int, @Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ @Array<Int>.0[@Int.0 / @Int.1] }
""", "by zero")

    def test_untranslatable_array_let_shadows_stale_outer(self) -> None:
        """An untranslatable array `let` (`array_append`, unmodelled by the SMT
        layer) must shadow a stale same-type outer array, so a later index does
        not resolve to the stale length and false-E527.  `let a = [1,2,3]; let a
        = array_append(a, 99); a[3]` is valid (the appended array has length 4),
        so it must NOT be E527 — the stale outer is replaced by a fresh
        (opaque) array, making the index honest Tier-3 (#680 review)."""
        _verify_ok("""
private fn append_index(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ let @Array<Int> = [1, 2, 3]; let @Array<Int> = array_append(@Array<Int>.0, 99); @Array<Int>.0[3] }
""")

    def test_untranslatable_destructure_array_shadows_stale_outer(self) -> None:
        """A destructured array slot from an untranslatable destructure must
        also shadow a stale same-type outer array (#680 review) — `let a =
        [1,2,3]; let Tuple<@Array<Int>, @Int> = mk(...); a[5]` must be Tier-3,
        not a false E527 against the stale length 3."""
        _verify_ok("""
private fn mk(@Array<Int> -> @Tuple<Array<Int>, Int>)
  requires(true)
  ensures(true)
  effects(pure)
{ Tuple(@Array<Int>.0, 0) }

private fn destructure_shadow(@Array<Int> -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ let @Array<Int> = [1, 2, 3]; let Tuple<@Array<Int>, @Int> = mk(@Array<Int>.0); @Array<Int>.0[5] }
""")

    def test_index_oob_fix_hint_renders_operands_and_both_bounds(self) -> None:
        """The E527 fix hint names the actual collection and index, and
        covers BOTH bounds (`0 <= i && i < array_length(...)`) — not a
        fixed slot or an upper-bound-only guard (PR #778 review,
        `verifier.py` E527 hint).  `[10, 20, 30][5]` exercises the
        `ArrayLit` render path in `format_expr`."""
        matched = _verify_err("""
private fn oob_hint(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ [10, 20, 30][5] }
""", "out of bounds")
        fix = matched[0].fix
        assert "0 <= 5 && 5 < array_length([10, 20, 30])" in fix, fix


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

    def test_narrow_stmt_position_obligated(self) -> None:
        """An `@Int -> @Nat` narrowing in STATEMENT position (a discarded call
        whose `@Nat` formal receives an `@Int` arg) still carries the
        `value >= 0` obligation — the narrowing walker recurses into the block's
        `ExprStmt` statements.  Same statement-position blind spot #730 closes
        for call preconditions."""
        _verify_err("""
private fn takes_nat(@Nat -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{ @Nat.0 }

private fn g(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ takes_nat(@Int.0); @Int.0 }
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

    def test_generic_nat_call_subtraction_obligated(self) -> None:
        """`idv(@Nat.0) - idv(@Nat.1)` with `idv<T>(@T -> @T)`: both operands
        are generic calls returning @Nat.  `_has_nat_origin` now recovers the
        instantiated @Nat result from the checker's side-table — the declared
        return is a `TypeVar` the local heuristic missed — so the #520
        underflow obligation fires instead of being silently skipped (CR #756).
        The generic calls are untranslatable to Z3, so the obligation is
        Tier-3 (codegen-#520-guarded), not a static E502; the point is it is no
        longer dropped."""
        result = _verify("""
private forall<T>
fn idv(@T -> @T)
  requires(true)
  ensures(true)
  effects(pure)
{ @T.0 }

public fn f(@Nat, @Nat -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{ idv(@Nat.0) - idv(@Nat.1) }
""")
        kinds = [o.kind for o in result.obligations]
        assert kinds.count("nat_sub") >= 1, kinds
        assert any(o.kind == "nat_sub" and o.status == "tier3"
                   for o in result.obligations), \
            [(o.kind, o.status) for o in result.obligations]

    def test_array_nat_element_subtraction_obligated(self) -> None:
        """`arr[0] - arr[1]` on an `@Array<Nat>` parameter (length >= 2, so both
        indices are in bounds) reports the #520 underflow (E502): array indexing
        preserves the element's @Nat provenance.  `_has_nat_origin` consults the
        checker's
        side-table for the IndexExpr's resolved element type (it cannot recurse
        on the `@Array` operand, which is not itself @Nat), so the subtraction
        is obligated like any `@Nat - @Nat` (CR #756)."""
        result = _verify("""
public fn f(@Array<Nat> -> @Nat)
  requires(array_length(@Array<Nat>.0) >= 2)
  ensures(true)
  effects(pure)
{ @Array<Nat>.0[0] - @Array<Nat>.0[1] }
""")
        assert [o.status for o in result.obligations
                if o.kind == "nat_sub"] == ["violated"], \
            [(o.kind, o.status) for o in result.obligations]
        assert any(d.error_code == "E502"
                   for d in result.diagnostics if d.severity == "error")

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
        """The generic effect-op narrowing discharges from a precondition.
        Pins the emitted `nat_bind` status as ``verified`` so a regression to
        *no* obligation can't pass silently (CR #756)."""
        result = _verify("""
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
        assert [o.status for o in result.obligations
                if o.kind == "nat_bind"] == ["verified"], \
            [(o.kind, o.status) for o in result.obligations]
        assert [d for d in result.diagnostics if d.severity == "error"] == []

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
        precondition constraining the @Int argument.  Pins the emitted
        `nat_bind` status as ``verified`` (CR #756)."""
        result = _verify("""
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
        assert [o.status for o in result.obligations
                if o.kind == "nat_bind"] == ["verified"], \
            [(o.kind, o.status) for o in result.obligations]
        assert [d for d in result.diagnostics if d.severity == "error"] == []

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
        precondition, exactly like the concrete-field case (#747).  Pins the
        emitted `nat_bind` status as ``verified`` (CR #756)."""
        result = _verify("""
private fn f(@Int -> @Option<Nat>)
  requires(@Int.0 >= 0)
  ensures(true)
  effects(pure)
{
  Some(@Int.0)
}
""")
        assert [o.status for o in result.obligations
                if o.kind == "nat_bind"] == ["verified"], \
            [(o.kind, o.status) for o in result.obligations]
        assert [d for d in result.diagnostics if d.severity == "error"] == []

    def test_generic_nat_returning_call_no_false_narrowing(self) -> None:
        """A generic call whose result is @Nat (`ident(@Nat.0)` with
        `ident<T>(@T -> @T)`) flowing into a @Nat slot is NOT a narrowing —
        the source is already @Nat.  `_is_nat_typed` consults the checker's
        semantic side-table (the local heuristics see only the callee's
        TypeVar return), so no spurious obligation / false E504 fires at the
        unguarded generic constructor field (CR #756)."""
        result = _verify("""
private forall<T>
fn ident(@T -> @T)
  requires(true)
  ensures(true)
  effects(pure)
{ @T.0 }

public fn f(@Nat -> @Option<Nat>)
  requires(true)
  ensures(true)
  effects(pure)
{ Some(ident(@Nat.0)) }
""")
        assert not [o for o in result.obligations if o.kind == "nat_bind"], \
            [(o.kind, o.status) for o in result.obligations]
        assert not [d for d in result.diagnostics if d.error_code == "E504"]
        assert [d for d in result.diagnostics if d.severity == "error"] == []

    def test_non_literal_nat_destructure_obligated(self) -> None:
        """#747 site 2: a non-literal tuple-destructure source — here a
        function call returning `Tuple<Int, Int>` — narrowing both @Int
        components into @Nat slots is obligated `>= 0`.  Under `requires(true)`
        each component is unconstrained, so both narrowings fail (E503).
        Closes the deferral the SMT tuple-datatype support unblocked: the RHS
        now translates to a projectable Z3 datatype."""
        result = _verify("""
private fn mk(@Unit -> @Tuple<Int, Int>)
  requires(true)
  ensures(true)
  effects(pure)
{ Tuple(1, 2) }

private fn f(@Unit -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  let Tuple<@Nat, @Nat> = mk(@Unit.0);
  @Nat.0
}
""")
        violated = [o for o in result.obligations
                    if o.kind == "nat_bind" and o.status == "violated"]
        assert len(violated) == 2, [(o.kind, o.status)
                                    for o in result.obligations]
        assert all(o.error_code == "E503" for o in violated)
        assert any(d.error_code == "E503" for d in result.diagnostics)

    def test_non_literal_nat_destructure_already_nat_not_obligated(
        self,
    ) -> None:
        """#747: a non-literal destructure whose source components are
        *already* @Nat (`Tuple<Nat, Nat>`) is not a narrowing, so no
        obligation fires.  Pins the soundness guard — the projected accessor
        term carries no `>= 0` fact, so obligating an already-@Nat source
        would fail the proof spuriously (the parallel of the ADT-sub-pattern
        guard).  A `requires`-discharge isn't expressible here: Vera contracts
        cannot project an opaque tuple's components, so the already-@Nat
        source is the discharge analog."""
        result = _verify("""
private fn mkn(@Unit -> @Tuple<Nat, Nat>)
  requires(true)
  ensures(true)
  effects(pure)
{ Tuple(1, 2) }

private fn f(@Unit -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  let Tuple<@Nat, @Nat> = mkn(@Unit.0);
  @Nat.0
}
""")
        assert not [o for o in result.obligations if o.kind == "nat_bind"]
        assert [d for d in result.diagnostics if d.severity == "error"] == []

    def test_if_expr_destructure_tier3_runtime(self) -> None:
        """#747: an `if`-expression tuple source the SMT layer does not model
        as a projectable datatype leaves a real @Int->@Nat destructure
        narrowing unverifiable *statically* — but codegen guards every @Nat
        destructure component at run time, so each is recorded as a guarded
        Tier-3 obligation (`tier3` / `tier3_runtime`), not a false unguarded
        E504 (CodeRabbit, PR #756).  Both @Nat components of the
        `Tuple<@Nat, @Nat>` are recorded independently — the per-component
        accounting the untranslatable fallback must mirror the projectable
        path (CodeRabbit, PR #756 round 6)."""
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
        tier3 = [o for o in result.obligations
                 if o.kind == "nat_bind" and o.status == "tier3"]
        # One Tier-3 obligation per @Nat component (the 2-tuple → 2).
        assert len(tier3) == 2, [(o.kind, o.status)
                                 for o in result.obligations]
        # Codegen-guarded → counted as runtime checks, with no E504 warning.
        assert result.summary.tier3_runtime == 2
        assert not [d for d in result.diagnostics if d.error_code == "E504"]
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
        """A narrowing at a *genuinely unguarded* site whose value the SMT
        layer can't translate surfaces an E504 warning + a `tier3_unguarded`
        obligation — NOT a silent `tier3_runtime` 'runtime check'.  The
        effect-operation argument is the canonical unguarded site: codegen
        does not yet emit a runtime guard there (#754), so an untranslatable
        narrowing into a @Nat effect-op formal (here `array_length`'s opaque
        @Int into `E.wait(Nat)`) is neither statically proven nor
        runtime-checked.  Distinct from the concrete @Nat *call argument*
        form, which #747 codegen DOES guard (now a `tier3_runtime`) — the
        `guarded` flag the verifier threads must distinguish them
        (CodeRabbit, PR #756 round 6)."""
        result = _verify('''
effect E {
  op wait(Nat -> Unit);
}

public fn f(@Unit -> @Unit)
  requires(true)
  ensures(true)
  effects(<E>)
{
  E.wait(array_length(string_lines("a\\nb")))
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
        assert result.summary.tier3_runtime == 0

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

    def test_pipe_call_arg_narrowing_obligated(self) -> None:
        """`(0 - 5) |> takesNat()` desugars to `takesNat(0 - 5)` — the piped
        left operand narrows @Int into a @Nat formal, so it must carry the
        same `value >= 0` obligation as the direct call.  The walker keeps the
        pipe as a `BinaryExpr`, so without explicit handling the narrowing was
        missed entirely — a false 'verified' for a negative value (CR #756)."""
        _verify_err("""
private fn takesNat(@Nat -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{ @Nat.0 }

public fn f(@Unit -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{ (0 - 5) |> takesNat() }
""", "may be negative")

    def test_pipe_call_arg_narrowing_discharged(self) -> None:
        """The piped narrowing verifies when the precondition proves the
        argument non-negative — the discharged companion to
        `test_pipe_call_arg_narrowing_obligated` (CR #756)."""
        result = _verify("""
private fn takesNat(@Nat -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{ @Nat.0 }

public fn f(@Int -> @Nat)
  requires(@Int.0 >= 0)
  ensures(true)
  effects(pure)
{ @Int.0 |> takesNat() }
""")
        assert [o.status for o in result.obligations
                if o.kind == "nat_bind"] == ["verified"], \
            [(o.kind, o.status) for o in result.obligations]
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

    def test_narrowing_inside_index_expr_caught(self) -> None:
        """A narrowing nested in an `IndexExpr` (here the index position) is
        visited by the walker, not skipped — pins the IndexExpr recursion
        branch a regression could silently drop (#749 item 1)."""
        _verify_err("""
private fn takes_nat(@Nat -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{ @Nat.0 }

private fn f(@Array<Int>, @Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ @Array<Int>.0[takes_nat(@Int.0)] }
""", "may be negative")

    def test_narrowing_inside_interpolated_string_caught(self) -> None:
        """A narrowing nested in an interpolated-string part is visited by
        the walker — pins the InterpolatedString recursion branch a
        regression could silently drop (#749 item 1)."""
        _verify_err(r"""
private fn takes_nat(@Nat -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{ @Nat.0 }

private fn f(@Int -> @String)
  requires(true)
  ensures(true)
  effects(pure)
{ "v: \(takes_nat(@Int.0))" }
""", "may be negative")

    def test_fresh_slot_var_resolves_nat_alias(self) -> None:
        """`_fresh_slot_var` dispatches on the *resolved* type, so a
        destructure slot whose declared type is an alias of a scalar
        (`type Count = Nat`) is invalidated with the scalar's Z3 invariant,
        not dropped as an unknown ADT.  Direct unit pin for the alias path
        the destructure suite only exercises indirectly (#749 item 2)."""
        from vera import ast
        from vera.smt import SmtContext
        from vera.verifier import ContractVerifier

        verifier = ContractVerifier()
        verifier._register_all(parse_to_ast(
            "type Count = Nat;\n"
            "private fn f(@Int -> @Int)\n"
            "  requires(true) ensures(true) effects(pure)\n"
            "{ @Int.0 }"
        ))
        smt = SmtContext()

        def named(name: str) -> ast.NamedType:
            return ast.NamedType(name=name, type_args=())

        alias = verifier._fresh_slot_var(smt, named("Count"))
        direct = verifier._fresh_slot_var(smt, named("Nat"))
        # The alias resolves to Nat and gets a real Z3 var with the same
        # sort as a directly-@Nat slot...
        assert alias is not None and direct is not None
        assert alias.sort() == direct.sort()
        # ...while a genuinely-unknown ADT type has no scalar sort.
        assert verifier._fresh_slot_var(smt, named("SomeUserAdt")) is None

    def test_narrows_into_nat_verifier_codegen_parity(self) -> None:
        """`_narrows_into_nat` is hand-mirrored in the verifier and codegen
        (#749 item 3).  The soundness-relevant property is an *implication*,
        not equality: codegen must emit a runtime guard for everything the
        verifier obligates (`verifier ⟹ codegen`).  The reverse — codegen
        guarding a value the verifier already proves @Nat — is a harmless
        over-guard (e.g. `string_length`, whose @Nat return codegen's
        `_is_static_nat_typed` does not recognise, so it conservatively
        guards while the verifier raises no obligation).  The *dangerous*
        desync is verifier-obligates-but-codegen-doesn't-guard, which would
        let a negative @Nat escape an unverified compile — a builtin's @Nat
        return wired into the verifier mirror but not codegen would trip the
        assertion below."""
        from vera.verifier import ContractVerifier
        from vera.wasm.context import StringPool, WasmContext

        verifier = ContractVerifier()
        codegen = WasmContext(StringPool())
        corpus = [
            "@Int.0", "@Nat.0", "0 - 1", "5 - 1", "@Int.0 + 1",
            "@Nat.0 - @Nat.1", "-1", "{ 0 - 1 }",
            "if @Int.0 > 0 then { 1 } else { 0 - 1 }",
            # FnCall returns are the most likely place the two mirrors desync,
            # since each independently classifies the callee's @Nat-ness.
            "array_length(@Array<Int>.0)", 'string_length("hi")',
            "abs(@Int.0)", "nat_to_int(@Nat.0)",
        ]
        for body in corpus:
            src = (
                "private fn f(@Int, @Nat, @Array<Int> -> @Int)\n"
                "  requires(true) ensures(true) effects(pure)\n"
                f"{{ {body} }}"
            )
            expr = parse_to_ast(src).declarations[0].decl.body.expr
            v = verifier._narrows_into_nat(expr)
            c = codegen._narrows_into_nat(expr)
            # codegen guards ⊇ verifier obligates (no unsound miss).
            assert (not v) or c, (
                f"unsound `_narrows_into_nat` desync on {body!r}: the verifier "
                f"obligates a `>= 0` check but codegen emits no runtime guard")

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

    # ---- #730: preconditions for calls in STATEMENT position ----
    # A call whose result is discarded (a bare `f(x);` statement) must still be
    # checked against its requires(...) — DESIGN.md: contracts are checked "at
    # every call site".  Before #730 the SMT body translation skipped ExprStmt.

    def test_call_violated_precondition_stmt_position(self) -> None:
        """#730 (headline): a statement-position call (result discarded) whose
        precondition is violated must fire E501 — the gap this fix closes."""
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
{ non_zero(0); 1 }
""", "precondition")

    def test_call_satisfied_precondition_stmt_position(self) -> None:
        """#730 guard: a satisfied precondition in statement position must NOT
        fire a spurious E501 (the fix must not over-fire)."""
        _verify_ok("""
private fn non_zero(@Int -> @Int)
  requires(@Int.0 != 0)
  ensures(true)
  effects(pure)
{ @Int.0 }

private fn ok_caller(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ non_zero(1); 1 }
""")

    def test_call_violated_precondition_stmt_position_in_if_branch(self) -> None:
        """#730: a statement-position call inside an if-branch block (routed via
        _translate_if -> _translate_block) is precondition-checked."""
        _verify_err("""
private fn non_zero(@Int -> @Int)
  requires(@Int.0 != 0)
  ensures(true)
  effects(pure)
{ @Int.0 }

private fn caller(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ if @Int.0 > 5 then { non_zero(0); @Int.0 } else { @Int.0 } }
""", "precondition")

    def test_call_violated_precondition_stmt_position_in_match_arm(self) -> None:
        """#730: a statement-position call inside a match-arm block (routed via
        _translate_match -> _translate_block) is precondition-checked."""
        _verify_err("""
private fn non_zero(@Int -> @Int)
  requires(@Int.0 != 0)
  ensures(true)
  effects(pure)
{ @Int.0 }

public data Flag {
  On,
  Off
}

private fn caller(@Flag -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ match @Flag.0 { On -> { non_zero(0); 1 }, Off -> 2 } }
""", "precondition")

    def test_call_stmt_position_sees_preceding_let(self) -> None:
        """#730: a statement-position call sees preceding let bindings — the env
        is threaded through ExprStmt translation (here @Int.0 == 0 violates)."""
        _verify_err("""
private fn non_zero(@Int -> @Int)
  requires(@Int.0 != 0)
  ensures(true)
  effects(pure)
{ @Int.0 }

private fn caller(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ let @Int = 0; non_zero(@Int.0); 1 }
""", "precondition")

    def test_call_stmt_position_no_double_count(self) -> None:
        """#730: a single statement-position violating call yields EXACTLY ONE
        call_pre E501 obligation — not zero (the bug pre-fix), not accidentally
        more.  In statement position the call is translated once, so this is a
        precise-count guard; the span-keyed #727 dedup's no-OVER-collapse
        property is pinned separately by
        test_two_distinct_stmt_position_violations_each_fire."""
        result = _verify("""
private fn non_zero(@Int -> @Int)
  requires(@Int.0 != 0)
  ensures(true)
  effects(pure)
{ @Int.0 }

private fn caller(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ non_zero(0); 1 }
""")
        e501 = [o for o in result.obligations
                if o.kind == "call_pre" and o.error_code == "E501"]
        assert len(e501) == 1, (
            f"expected exactly one call_pre E501 obligation, got {len(e501)}: "
            f"{[(o.line, o.column) for o in e501]}"
        )

    def test_call_stmt_position_effect_op_degrades(self) -> None:
        """#730 guard: an untranslatable statement (an effect op) is ignored, not
        crashed on, and does not abort verification of the rest of the block."""
        _verify_ok("""
private fn logged(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(<IO>)
{ IO.print("hi"); @Int.0 }
""")

    def test_call_violated_precondition_after_untranslatable_stmt(self) -> None:
        """#730 soundness: an untranslatable statement (an effect op) preceding a
        decidable violating call must NOT abort the block — the later call is
        still precondition-checked.  Guards the `_translate_block` invariant that
        a None-returning ExprStmt is IGNORED, not propagated as a block bail: the
        abort-on-None wrong-fix passes every other statement-position test yet
        silently drops this E501 (PR #777 review)."""
        _verify_err("""
private fn non_zero(@Int -> @Int)
  requires(@Int.0 != 0)
  ensures(true)
  effects(pure)
{ @Int.0 }

private fn caller(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(<IO>)
{ IO.print("side"); non_zero(0); @Int.0 }
""", "precondition")

    def test_two_distinct_stmt_position_violations_each_fire(self) -> None:
        """Two distinct statement-position violating calls produce TWO E501
        obligations — the span-keyed #727 dedup collapses a re-translated SAME
        site to one, but must NOT over-collapse genuinely-different sites
        (PR #777 review)."""
        result = _verify("""
private fn non_zero(@Int -> @Int)
  requires(@Int.0 != 0)
  ensures(true)
  effects(pure)
{ @Int.0 }

private fn caller(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ non_zero(0); non_zero(0); 1 }
""")
        e501 = [o for o in result.obligations
                if o.kind == "call_pre" and o.error_code == "E501"]
        assert len(e501) == 2, (
            f"two distinct statement-position violations must each fire, got "
            f"{len(e501)}: {[(o.line, o.column) for o in e501]}"
        )

    def test_call_violated_precondition_nested_in_stmt_expr(self) -> None:
        """A violating call buried inside a larger statement-position expression
        (`non_zero(0) + 5;`) is precondition-checked — the ExprStmt translation
        recurses into sub-expressions, not just the outermost node (PR #777
        review)."""
        _verify_err("""
private fn non_zero(@Int -> @Int)
  requires(@Int.0 != 0)
  ensures(true)
  effects(pure)
{ @Int.0 }

private fn caller(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ non_zero(0) + 5; 1 }
""", "precondition")

    def test_decreases_resolves_via_stmt_position_recursive_call(self) -> None:
        """A recursive call in STATEMENT position (result discarded) is seen by
        the termination walker, so `decreases` still resolves to Tier-1 — the
        third statement-iterating walker (`_walk_for_calls`) recurses into
        ExprStmt (the branch that was the last `# pragma: no cover`).  Without it
        the recursive call is invisible and `decreases` silently degrades to
        Tier-3 (PR #777 review)."""
        result = _verify("""
private fn countdown(@Nat -> @Nat)
  requires(true)
  ensures(true)
  decreases(@Nat.0)
  effects(pure)
{ if @Nat.0 == 0 then { 0 } else { countdown(@Nat.0 - 1); 0 } }
""")
        decr = [o for o in result.obligations
                if o.fn_name == "countdown" and o.kind == "decreases"]
        assert len(decr) == 1 and decr[0].status == "verified", (
            "decreases must resolve to Tier-1 via the statement-position "
            f"recursive call; got {[(o.kind, o.status) for o in decr]}"
        )
        assert [d for d in result.diagnostics if d.severity == "error"] == []

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

    def test_generic_call_verified_per_instantiation(self) -> None:
        """#732: a generic instantiated by a caller is verified statically per
        monomorphization — Tier 1, not the old Tier-3 bail."""
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
        # id<Int>'s ensures(@T.result == @T.0) holds for the body @T.0, so the
        # instantiated generic is now discharged statically with no Tier-3
        # fallback — the core #732 behavior change.
        assert result.summary.tier3_runtime == 0
        assert not result.diagnostics
        # Check id's OWN ensures is the verified obligation, not just the
        # summary counter (which a non-generic obligation could also bump).
        assert any(
            o.fn_name == "id" and o.kind == "ensures" and o.status == "verified"
            for o in result.obligations
        )

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

    # -- #747 site 4: imported constructor @Nat-field narrowing ------------

    BOXES_MODULE = """\
public data NatBox {
  WrapN(Nat)
}

public data Box<T> {
  Wrap(T)
}
"""

    def test_imported_ctor_concrete_nat_field_obligated(self) -> None:
        """#747 site 4: an imported constructor with a concrete @Nat field
        (`WrapN(Nat)` from another module) narrowing an @Int argument is
        obligated `>= 0`.  The verifier harvests the imported ctor's field
        types into `_module_constructors`, so the narrowing fires (E503)
        under `requires(true)` instead of passing silently."""
        mod = self._resolved(("boxes",), self.BOXES_MODULE)
        result = self._verify_mod("""\
import boxes(WrapN, NatBox);
private fn f(@Int -> @NatBox)
  requires(true)
  ensures(true)
  effects(pure)
{ WrapN(@Int.0) }
""", [mod])
        violated = [o for o in result.obligations
                    if o.kind == "nat_bind" and o.status == "violated"]
        assert len(violated) == 1, [(o.kind, o.status)
                                    for o in result.obligations]
        assert violated[0].error_code == "E503"

    def test_imported_ctor_concrete_nat_field_discharged(self) -> None:
        """The imported concrete-@Nat-field narrowing discharges from a
        precondition that proves the argument non-negative."""
        mod = self._resolved(("boxes",), self.BOXES_MODULE)
        result = self._verify_mod("""\
import boxes(WrapN, NatBox);
private fn f(@Int -> @NatBox)
  requires(@Int.0 >= 0)
  ensures(true)
  effects(pure)
{ WrapN(@Int.0) }
""", [mod])
        # Pin that the obligation actually fired and verified — not merely the
        # absence of a violation (which a no-obligation regression would also
        # satisfy), mirroring the generic discharged companion (CR #756).
        statuses = [o.status for o in result.obligations
                    if o.kind == "nat_bind"]
        assert statuses == ["verified"], statuses
        assert [d for d in result.diagnostics if d.severity == "error"] == []

    def test_imported_ctor_generic_field_nat_obligated(self) -> None:
        """#747 site 4: an imported *generic* constructor field instantiated
        to @Nat at the call site (`Wrap(@Int.0)` building `Box<Nat>`) is
        obligated — the harvested field type is a TypeVar, so the
        instantiated @Nat target comes from the checker's side-table."""
        mod = self._resolved(("boxes",), self.BOXES_MODULE)
        result = self._verify_mod("""\
import boxes(Wrap, Box);
private fn f(@Int -> @Box<Nat>)
  requires(true)
  ensures(true)
  effects(pure)
{ Wrap(@Int.0) }
""", [mod])
        violated = [o for o in result.obligations
                    if o.kind == "nat_bind" and o.status == "violated"]
        assert len(violated) == 1, [(o.kind, o.status)
                                    for o in result.obligations]
        assert violated[0].error_code == "E503"

    def test_imported_ctor_generic_field_nat_discharged(self) -> None:
        """The imported generic-constructor narrowing discharges from a
        precondition — pins that imported generic-field instantiation isn't
        always treated as violated (CodeRabbit, PR #756)."""
        mod = self._resolved(("boxes",), self.BOXES_MODULE)
        result = self._verify_mod("""\
import boxes(Wrap, Box);
private fn f(@Int -> @Box<Nat>)
  requires(@Int.0 >= 0)
  ensures(true)
  effects(pure)
{ Wrap(@Int.0) }
""", [mod])
        # The obligation must be present AND verified — not merely absent
        # (a regression that stopped emitting it would also be "not
        # violated") (CodeRabbit, PR #756).
        verified = [o for o in result.obligations
                    if o.kind == "nat_bind" and o.status == "verified"]
        assert len(verified) == 1, [(o.kind, o.status)
                                    for o in result.obligations]
        assert [d for d in result.diagnostics if d.severity == "error"] == []


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
        """All examples together: 260 T1 / 27 T3 / 287 total (current).

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
          three `nat_to_int(array_length(...))` narrowings were treated as
          non-`let` sites with no codegen runtime guard, so each was surfaced
          as an E504 `tier3_unguarded` warning and excluded from the totals
          rather than counted as a runtime check: -3 T3, -3 total,
          +3 tier3_unguarded.
        * 256/28/284 after #747 (PR #756) extended codegen's runtime guard to
          the concrete @Nat *call-argument* site (`vera/wasm/calls.py`).  The
          three `nat_to_int(array_length(...))` narrowings pass an opaque @Int
          into nat_to_int's CONCRETE @Nat formal, which codegen now traps on
          `< 0` at run time — so each is correctly a codegen-guarded
          `tier3_runtime` again, not an E504: +3 T3, +3 total,
          -3 tier3_unguarded.  Only genuinely-unguarded sites (effect-op
          arguments, generic-instantiated fields/args whose @Nat erases to
          i64 — #754) still warn, and no example exercises one: +0
          tier3_unguarded.
        * 258/29/287/0 after #746 generalised the @Nat discharge to arbitrary
          refinement predicates and added a codegen runtime guard.
          `refinement_types.vera` gains 2 T1 — the `safe_divide(10, 3)`
          argument now discharges `3 > 0` into its `@PosInt` formal, and
          `to_percentage`'s body now discharges its `@Percentage` return
          predicate (`>= 0 && <= 100`) — and 1 T3: `head([42, 1, 2])` narrows
          into `@NonEmptyArray`, whose `array_length(...) > 0` predicate is over
          a non-primitive (`Array`) base Z3 cannot decide, so it is a
          runtime-checked Tier-3 (an informational E506; codegen emits the
          predicate guard at the function boundary).  Net: +2 T1, +1 T3,
          +3 total, +0 tier3_unguarded.
        * 260/27/287/0 after #732 verified instantiated generics per
          monomorphization.  `generics.vera`'s `identity` and `const` are
          instantiated at concrete types (`identity<Int>`, `const<Int, Bool>`),
          so their `ensures(@T.result == @T.0)` / `ensures(@A.result == @A.0)`
          postconditions are now discharged statically instead of bailing to
          Tier 3 (E520): +2 T1, -2 T3, +0 total (the two contracts change tier;
          the total is unchanged).
        * 263/32/295/0 after #680 auto-synthesised obligations for integer
          division/modulo (`b != 0`, E526) and array indexing
          (`0 <= i < array_length`, E527).  The corpus gains 3 T1 from guarded
          divisions discharged at Tier 1 — effect_handler's path-guarded
          `@Int.0 / @Int.1`, refinement_types' `@PosInt` divisor, and
          safe_divide's `requires(@Int.1 != 0)` — and 5 T3: json's opaque
          divisor (1) plus opaque / dynamic array indices in json (1),
          life (2, deeply-nested match+if guards beyond Tier 1), and
          refinement_types' `@NonEmptyArray` (1, an Array-base refinement Z3
          cannot decide at Tier 1 — #427).  No example indexes provably out of
          bounds, so none is a loud E527.  Net: +3 T1, +5 T3, +8 total, +0 t3u.
        * 263/31/294/0 after the #680-review Float64-divisor fix: json's `/`
          divisor resolves to `@Float64`, so it is now exempt up front
          (`f64.div` by zero is inf/NaN, not a trap) instead of recording a
          bogus Tier-3 `div_zero` — it was the corpus's only tier3 div_zero.
          -1 T3, -1 total.
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
        assert t1 == 263, f"Expected 263 T1, got {t1}"
        assert t3 == 31, f"Expected 31 T3, got {t3}"
        assert total == 294, f"Expected 294 total, got {total}"
        assert t3u == 0, f"Expected 0 tier3_unguarded, got {t3u}"


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
        """A predicate calling a builtin (`string_length(@String.0) > 0`)
        translates with the binder substituted — same surface as a `requires`
        clause, so `translate_expr` handles it."""
        import z3
        from vera.smt import SmtContext
        from vera.types import RefinedType, STRING
        from vera.verifier import ContractVerifier

        pred = self._predicate_of(
            "type NEStr = { @String | string_length(@String.0) > 0 };\n"
        )
        refined = RefinedType(STRING, pred)
        smt = SmtContext()
        s = z3.Const("s", z3.StringSort())
        result = ContractVerifier._translate_refined_predicate(smt, refined, s)
        assert result is not None
        assert z3.is_true(
            z3.simplify(z3.substitute(result, (s, z3.StringVal("ab"))))
        )
        assert z3.is_false(
            z3.simplify(z3.substitute(result, (s, z3.StringVal(""))))
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

    def test_string_length_predicate_discharges(self) -> None:
        """A predicate calling a builtin (`string_length(...) > 0`) discharges
        a non-empty string literal at a call argument (R8)."""
        result = _verify("""
type NonEmpty = { @String | string_length(@String.0) > 0 };

private fn use(@NonEmpty -> @Int)
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


class TestPerMonomorphizationVerification:
    """#732: instantiated generics are verified statically per monomorphization.

    Before #732 a generic body skipped SMT entirely — every non-trivial
    contract fell to Tier 3 (E520), a silent Tier-1 -> Tier-3 downgrade.  Now
    each concrete instantiation is verified through the normal path, so body
    obligations (a @Nat underflow, an `ensures`, a refined return) are actually
    discharged — or caught.
    """

    def test_body_nat_underflow_caught_per_instantiation(self) -> None:
        """An unguarded @Nat subtraction in a generic body — silently skipped
        (Tier-3 E520) before #732 — is now caught, naming the instantiation."""
        result = _verify("""
private forall<T>
fn dec(@Nat, @Nat, @T -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{ @Nat.0 - @Nat.1 }

private fn caller(@Nat, @Nat -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{ dec(@Nat.1, @Nat.0, true) }
""")
        errs = [d for d in result.diagnostics if d.error_code == "E502"]
        assert len(errs) == 1, "expected exactly one underflow diagnostic"
        assert "instantiated at dec<Bool>" in errs[0].description
        assert "underflow" in errs[0].description
        violated = [o for o in result.obligations
                    if o.kind == "nat_sub" and o.status == "violated"]
        assert len(violated) == 1
        assert violated[0].fn_name == "dec"
        assert violated[0].counterexample is not None

    def test_body_nat_underflow_discharged_when_guarded(self) -> None:
        """The same body verifies statically (Tier 1) when a precondition
        guards it — the per-instance path PROVES, it does not merely reject."""
        result = _verify("""
private forall<T>
fn dec(@Nat, @Nat, @T -> @Nat)
  requires(@Nat.0 >= @Nat.1)
  ensures(true)
  effects(pure)
{ @Nat.0 - @Nat.1 }

private fn caller(@Nat, @Nat -> @Nat)
  requires(@Nat.0 >= @Nat.1)
  ensures(true)
  effects(pure)
{ dec(@Nat.1, @Nat.0, true) }
""")
        assert [d for d in result.diagnostics if d.severity == "error"] == []
        assert result.summary.tier3_runtime == 0
        # the body's nat_sub obligation is discharged statically for dec<Bool>
        assert any(o.kind == "nat_sub" and o.status == "verified"
                   for o in result.obligations)

    def test_never_instantiated_generic_stays_tier3(self) -> None:
        """A generic with no call site cannot be monomorphized, so its
        non-trivial contracts still fall to Tier 3 (E520) — the residual that
        #732 deliberately leaves untouched."""
        result = _verify("""
private forall<T>
fn unused(@T -> @T)
  requires(true)
  ensures(@T.result == @T.0)
  effects(pure)
{ @T.0 }
""")
        assert result.summary.tier3_runtime == 1
        e520 = [d for d in result.diagnostics if d.error_code == "E520"]
        assert len(e520) == 1
        assert [d for d in result.diagnostics if d.severity == "error"] == []

    def test_collapsed_type_vars_verify_correctly(self) -> None:
        """When two type vars collapse to the same concrete type (A=B=Int), the
        De Bruijn reindex must keep slot references consistent — the contract
        over the collapsed slots still discharges, with no false result."""
        result = _verify("""
private forall<A, B>
fn pick_first(@A, @B -> @A)
  requires(true)
  ensures(@A.result == @A.0)
  effects(pure)
{ @A.0 }

private fn use_same(@Int, @Int -> @Int)
  requires(true)
  ensures(@Int.result == @Int.1)
  effects(pure)
{ pick_first(@Int.1, @Int.0) }
""")
        assert [d for d in result.diagnostics if d.severity == "error"] == []
        # pick_first<Int, Int>'s ensures discharges statically.
        assert any(o.fn_name == "pick_first" and o.kind == "ensures"
                   and o.status == "verified" for o in result.obligations)

    def test_one_diagnostic_dedups_across_instantiations(self) -> None:
        """A body bug reachable in several instantiations surfaces ONCE (deduped
        to the source span), naming each offending instantiation — not N times."""
        result = _verify("""
private forall<T>
fn dec(@Nat, @Nat, @T -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{ @Nat.0 - @Nat.1 }

private fn use_bool(@Nat, @Nat -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{ dec(@Nat.1, @Nat.0, true) }

private fn use_int(@Nat, @Nat -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{ dec(@Nat.1, @Nat.0, 7) }
""")
        errs = [d for d in result.diagnostics if d.error_code == "E502"]
        assert len(errs) == 1, "one diagnostic per source site, not per instance"
        assert "dec<Bool>" in errs[0].description
        assert "dec<Int>" in errs[0].description
        # exactly one violated nat_sub obligation, not one per instantiation
        violated = [o for o in result.obligations
                    if o.kind == "nat_sub" and o.status == "violated"]
        assert len(violated) == 1

    def test_body_ensures_violation_caught_per_instantiation(self) -> None:
        """A generic body that violates its own `ensures` is caught per
        instantiation (E500), naming the instantiation.  A violated
        postcondition records its obligation with no error_code while its
        diagnostic carries E500, so the aggregation must correlate by
        (severity, span) — not error code — or it silently drops the violation
        (a false Tier-1).  Regression for the PR #767 review."""
        result = _verify("""
private forall<T>
fn bad_id(@Int, @T -> @Int)
  requires(true)
  ensures(@Int.result == @Int.0)
  effects(pure)
{ @Int.0 + 1 }

private fn caller(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ bad_id(@Int.0, true) }
""")
        errs = [d for d in result.diagnostics
                if d.severity == "error" and d.error_code == "E500"]
        assert len(errs) == 1
        assert "instantiated at bad_id<Bool>" in errs[0].description
        violated = [o for o in result.obligations
                    if o.kind == "ensures" and o.status == "violated"]
        assert len(violated) == 1
        assert violated[0].fn_name == "bad_id"

    def test_body_bug_in_transitively_reached_generic_caught(self) -> None:
        """A body bug in a generic reached only transitively (through another
        generic's body) is verified and caught — discovery AND verification
        both follow the transitive worklist, not just discovery."""
        result = _verify("""
private forall<T>
fn inner(@Nat, @Nat, @T -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{ @Nat.0 - @Nat.1 }

private forall<T>
fn outer(@Nat, @Nat, @T -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{ inner(@Nat.1, @Nat.0, @T.0) }

private fn caller(@Nat, @Nat -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{ outer(@Nat.1, @Nat.0, true) }
""")
        errs = [d for d in result.diagnostics if d.error_code == "E502"]
        assert len(errs) == 1
        assert "instantiated at inner<Bool>" in errs[0].description

    def test_generic_in_arraylit_is_discovered_and_verified(self) -> None:
        """The discovery walk is TOTAL over Expr, so a generic reachable only
        from inside an `ArrayLit` (a form the old explicit-arm walk skipped) is
        discovered and verified — its body @Nat underflow is caught, not missed
        into the Tier-3 fallback."""
        result = _verify("""
private forall<T>
fn dec(@Nat, @Nat, @T -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{ @Nat.0 - @Nat.1 }

private fn caller(@Nat, @Nat -> @Array<Nat>)
  requires(true)
  ensures(true)
  effects(pure)
{ [dec(@Nat.1, @Nat.0, true)] }
""")
        errs = [d for d in result.diagnostics if d.error_code == "E502"]
        assert len(errs) == 1
        assert "instantiated at dec<Bool>" in errs[0].description

    def test_generic_in_contract_clause_is_verified(self) -> None:
        """A generic reachable only from a contract predicate (here an `ensures`)
        is discovered and verified — discovery walks contract clauses, not just
        the body and where-helpers — so its body bug is caught."""
        result = _verify("""
private forall<T>
fn bad_dec(@Nat, @Nat, @T -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{ @Nat.0 - @Nat.1 }

private fn checker(@Nat, @Nat -> @Bool)
  requires(true)
  ensures(bad_dec(@Nat.1, @Nat.0, true) >= 0)
  effects(pure)
{ true }
""")
        errs = [d for d in result.diagnostics if d.error_code == "E502"]
        assert len(errs) == 1
        assert "instantiated at bad_dec<Bool>" in errs[0].description

    def test_generic_reached_only_via_decreases_is_verified(self) -> None:
        """A generic reachable only from a `decreases(...)` measure is discovered
        and verified.  Decreases is the one Contract subclass that holds its
        predicates in `.exprs` (a tuple) rather than `.expr`, so a contract walk
        reading only `.expr` silently skipped it (PR #767 review) — degrading
        such a generic to the E520 Tier-3 fallback and missing its body bug.  The
        first lexicographic component (`@Nat.0`) carries termination; the second
        only has to be discovered."""
        result = _verify("""
private forall<T>
fn bad_measure(@Nat, @Nat, @T -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{ @Nat.0 - @Nat.1 }

private fn countdown(@Nat -> @Nat)
  requires(true)
  ensures(true)
  decreases(@Nat.0, bad_measure(@Nat.0, 0, true))
  effects(pure)
{ if @Nat.0 == 0 then { 0 } else { countdown(@Nat.0 - 1) } }
""")
        errs = [d for d in result.diagnostics if d.error_code == "E502"]
        assert len(errs) == 1
        assert "instantiated at bad_measure<Bool>" in errs[0].description

    def test_typevar_contract_aggregates_across_instantiations(self) -> None:
        """A generic whose contract references @T renders different expr_text per
        instantiation; the meet must group by SOURCE SITE so it stays ONE
        obligation, not one per instantiation (else summaries over-count) — from
        the PR #767 review."""
        result = _verify("""
private forall<T>
fn idc(@T -> @T)
  requires(true)
  ensures(@T.result == @T.0)
  effects(pure)
{ @T.0 }

private fn use2(@Int, @Bool -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Int = idc(@Int.0);
  let @Bool = idc(@Bool.0);
  @Int.0
}
""")
        ens = [o for o in result.obligations
               if o.fn_name == "idc" and o.kind == "ensures"]
        assert len(ens) == 1, "one obligation per source site, not per instance"
        assert ens[0].status == "verified"
        assert [d for d in result.diagnostics if d.severity == "error"] == []

    def test_aggregated_tier3_label_includes_timeout_instances(self) -> None:
        """A mixed tier3/timeout Tier-3 aggregate must list BOTH instantiations
        in the diagnostic prefix.  ``_meet_status`` folds ``timeout`` into
        ``tier3``, so the instantiation-label filter must group them together;
        an exact status-match drops the ``timeout`` instance from the prefix
        (PR #767 review).  Synthesised directly because a real Z3 timeout is
        non-deterministic and cannot be pinned through the normal pipeline."""
        from types import SimpleNamespace

        from vera.errors import Diagnostic, SourceLocation
        from vera.obligations.core import ProofObligation
        from vera.verifier import ContractVerifier

        v = ContractVerifier(source="", file="t.vera")
        decl = SimpleNamespace(name="g")
        ob_t3 = ProofObligation(
            fn_name="g", kind="ensures", expr_text="p", status="tier3",
            line=3, column=5, error_code="E506",
        )
        ob_to = ProofObligation(
            fn_name="g", kind="ensures", expr_text="p", status="timeout",
            line=3, column=5, error_code="E506",
        )
        members = [(("Int",), ob_t3), (("Float64",), ob_to)]
        src = Diagnostic(
            description="runtime check deferred",
            location=SourceLocation(file="t.vera", line=3, column=5),
            severity="warning", error_code="E506", tier=None,
        )
        errs = {("Int",): [src]}
        v._emit_aggregated_diagnostic(
            decl, members, ("Int",), ob_t3, errs,  # type: ignore[arg-type]
        )

        assert v.errors, "expected an aggregated Tier-3 diagnostic"
        desc = v.errors[-1].description
        assert "g<Int>" in desc and "g<Float64>" in desc, (
            f"both the tier3 and the timeout instance must appear: {desc}"
        )

    def test_recursive_generic_clone_keeps_source_name_for_decreases(self) -> None:
        """A recursive generic's clone must keep the SOURCE name so the verifier
        recognizes its recursive call and obligates `decreases`.

        `monomorphize_fn` mangles the clone name (for codegen WAT symbols), but
        `_verify_generic_instances` renames it back to `decl.name` ("keep the
        source name").  Recursion/`decreases` resolution is purely by name
        (`_collect_recursive_calls` matches `FnCall.name`), so without that
        rename the clone `countdown$Int` whose body still calls `countdown`
        would have NO recognized recursive call → no `decreases` obligation → a
        terminating function's measure silently unchecked.  Pin that the
        obligation is present and verified — identical to the non-generic twin
        — which refutes the "mangled clone breaks recursion" claim (PR #767
        review) and fails loudly if the source-name rename is ever removed."""
        result = _verify("""
private forall<T> fn countdown(@T, @Nat -> @Nat)
  requires(true)
  ensures(true)
  decreases(@Nat.0)
  effects(pure)
{ if @Nat.0 == 0 then { 0 } else { countdown(@T.0, @Nat.0 - 1) } }

private fn driver(@Int, @Nat -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{ countdown(@Int.0, @Nat.0) }
""")
        decr = [o for o in result.obligations
                if o.fn_name == "countdown" and o.kind == "decreases"]
        assert len(decr) == 1, (
            "the recursive generic clone must obligate `decreases` (recursion "
            f"recognized via the source-name clone); got {decr}"
        )
        assert decr[0].status == "verified"
        assert [d for d in result.diagnostics if d.severity == "error"] == []

    def test_generic_reached_only_via_where_helper_is_verified(self) -> None:
        """A generic reachable solely through a `where` helper is discovered and
        verified — its body bug is caught — not missed into the uninstantiated
        Tier-3 fallback (the PR #767 review)."""
        result = _verify("""
private forall<T>
fn inner(@Nat, @Nat, @T -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{ @Nat.0 - @Nat.1 }

private fn caller(@Nat, @Nat -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{ helper(@Nat.1, @Nat.0) }
where {
  fn helper(@Nat, @Nat -> @Nat)
    requires(true)
    ensures(true)
    effects(pure)
  { inner(@Nat.1, @Nat.0, true) }
}
""")
        errs = [d for d in result.diagnostics if d.error_code == "E502"]
        assert len(errs) == 1
        assert "instantiated at inner<Bool>" in errs[0].description


class TestShadowAuditDivision680:
    def test_compound_mult_shadow_divisor_is_tier3(self) -> None:
        """`2 * shadow` divisor (opaque shadow inside a multiplication) stays
        Tier-3 — never a false E526 AND never silently discharged.  The `let`
        shadows a guarded `requires(@Int.0 != 0)` outer, so a lost shadow would
        verify `2 * @Int.0 != 0` against the stale `!= 0`; the *tracked* shadow
        forces `_contains_opaque_shadow` to route it to Tier-3.  (Breaking the
        `*`-operand recursion flips this to a false E526 — mutation-checked.)"""
        result = _verify("""
private fn f(@Int -> @Int)
  requires(@Int.0 != 0)
  ensures(true)
  effects(<Random>)
{ let @Int = random_int(0, 10); 1 / (2 * @Int.0) }
""")
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert errors == [], [e.error_code for e in errors]
        divs = [o for o in result.obligations if o.kind == "div_zero"]
        assert len(divs) == 1 and divs[0].status == "tier3", [
            (o.kind, o.status) for o in divs
        ]

    def test_product_of_two_shadow_terms_is_tier3(self) -> None:
        """A divisor that is a product of two shadow-bearing subexpressions
        `(shadow + 1) * (shadow + 2)` stays Tier-3: the opaque-shadow walk must
        descend into BOTH operands of the `*`, not just the leftmost.  The `let`
        shadows a guarded `requires(@Int.0 != 0)` outer — a lost shadow would
        silently discharge against the stale `!= 0` (mutation-checked)."""
        result = _verify("""
private fn f(@Int -> @Int)
  requires(@Int.0 != 0)
  ensures(true)
  effects(<Random>)
{ let @Int = random_int(0, 10); 1 / ((@Int.0 + 1) * (@Int.0 + 2)) }
""")
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert errors == [], [e.error_code for e in errors]
        divs = [o for o in result.obligations if o.kind == "div_zero"]
        assert len(divs) == 1 and divs[0].status == "tier3", [
            (o.kind, o.status) for o in divs
        ]

    def test_self_subtraction_of_shadow_is_provably_zero_e526(self) -> None:
        """`shadow - shadow` as a divisor is a loud E526 — the compound-shadow
        guard must NOT over-mask a *provably*-zero divisor just because it
        embeds a shadow.  Even with a tracked shadow `s`, `s - s` simplifies to
        0 for every value, so `divisor == 0` is valid and the guard correctly
        falls through to E526 (the `let` shadows a guarded `requires(@Int.0 !=
        0)` outer, so this is the genuine-zero half of the differential, not a
        stale-outer leak).  A `tier3` here would be the guard wrongly masking a
        decidable divide-by-zero — mutation-checked against an over-eager
        guard."""
        result = _verify("""
private fn f(@Int -> @Int)
  requires(@Int.0 != 0)
  ensures(true)
  effects(<Random>)
{ let @Int = random_int(0, 10); 1 / (@Int.0 - @Int.0) }
""")
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert [e.error_code for e in errors] == ["E526"], [
            e.error_code for e in errors
        ]
        divs = [o for o in result.obligations if o.kind == "div_zero"]
        assert len(divs) == 1 and divs[0].status == "violated", [
            (o.kind, o.status) for o in divs
        ]

    def test_modulo_compound_shadow_divisor_is_tier3(self) -> None:
        """Modulo mirrors division on the compound-shadow path: `1 % (shadow + 1)`
        is Tier-3, never a false E526.  Pins `%` to the same
        `_contains_opaque_shadow` treatment as `/`.  The `let` shadows a guarded
        `requires(@Int.0 != 0)` outer — a lost shadow would silently discharge
        the modulo against the stale `!= 0` (mutation-checked)."""
        result = _verify("""
private fn f(@Int -> @Int)
  requires(@Int.0 != 0)
  ensures(true)
  effects(<Random>)
{ let @Int = random_int(0, 10); 1 % (@Int.0 + 1) }
""")
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert errors == [], [e.error_code for e in errors]
        divs = [o for o in result.obligations if o.kind == "div_zero"]
        assert len(divs) == 1 and divs[0].status == "tier3", [
            (o.kind, o.status) for o in divs
        ]

    def test_modulo_opaque_let_divisor_is_tier3(self) -> None:
        """A direct opaque-let modulo divisor `1 % shadow` is Tier-3 — the `%`
        obligation is recorded under the same `div_zero` kind as `/` and is not
        silently dropped.  The `let` shadows a guarded `requires(@Int.0 != 0)`
        outer, so a lost (untracked) shadow would discharge `@Int.0 != 0`
        against the stale `!= 0` — `_is_opaque_shadow` keeps it Tier-3
        (mutation-checked: turning it off flips this to a false E526)."""
        result = _verify("""
private fn f(@Int -> @Int)
  requires(@Int.0 != 0)
  ensures(true)
  effects(<Random>)
{ let @Int = random_int(0, 10); 1 % @Int.0 }
""")
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert errors == [], [e.error_code for e in errors]
        divs = [o for o in result.obligations if o.kind == "div_zero"]
        assert len(divs) == 1 and divs[0].status == "tier3", [
            (o.kind, o.status) for o in divs
        ]

    def test_mixed_destructure_divisor_by_literal_component_discharges(self) -> None:
        """In `Tuple(10, random_int(...))` the FIRST component is a translatable
        literal: dividing by it (`@Int.1`, the prior De Bruijn slot) discharges
        `10 != 0` at Tier-1 even though the SECOND component is opaque.  The
        literal projection must survive an opaque sibling in the same tuple."""
        result = _verify("""
private fn f(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(<Random>)
{ let Tuple<@Int, @Int> = Tuple(10, random_int(0, 10)); 1 / @Int.1 }
""")
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert errors == [], [e.error_code for e in errors]
        divs = [o for o in result.obligations if o.kind == "div_zero"]
        assert len(divs) == 1 and divs[0].status == "verified", [
            (o.kind, o.status) for o in divs
        ]

    def test_mixed_destructure_divisor_by_opaque_component_stays_tier3(self) -> None:
        """The De Bruijn-collapse trap: in `Tuple(10, random_int(...))` dividing
        by `@Int.0` (most-recent slot = the OPAQUE second component) must stay
        Tier-3.  If the opaque component were skipped instead of pushed, `@Int.0`
        would collapse onto the literal `10` and falsely discharge — the worst
        #680 failure class (silent false-discharge)."""
        result = _verify("""
private fn f(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(<Random>)
{ let Tuple<@Int, @Int> = Tuple(10, random_int(0, 10)); 1 / @Int.0 }
""")
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert errors == [], [e.error_code for e in errors]
        divs = [o for o in result.obligations if o.kind == "div_zero"]
        assert len(divs) == 1 and divs[0].status == "tier3", [
            (o.kind, o.status) for o in divs
        ]

    def test_outer_requires_does_not_discharge_shadowing_opaque_let(self) -> None:
        """The canonical silent-failure differential: an opaque `let @Int =
        random_int(...)` shadows an outer `@Int` param guarded by
        `requires(@Int.0 != 0)`.  Dividing by `@Int.0` now refers to the
        *shadow* (which can be 0), so it must be Tier-3, NOT verified against
        the stale outer guard.  A `verified` here is a SILENT_FAILURE."""
        result = _verify("""
public fn f(@Int -> @Int)
  requires(@Int.0 != 0)
  ensures(true)
  effects(<Random>)
{ let @Int = random_int(0, 10); 1 / @Int.0 }
""")
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert errors == [], [e.error_code for e in errors]
        divs = [o for o in result.obligations if o.kind == "div_zero"]
        assert len(divs) == 1 and divs[0].status == "tier3", [
            (o.kind, o.status) for o in divs
        ]

    def test_divisor_is_outer_param_after_opaque_let_discharges(self) -> None:
        """The complement of the shadow trap: after an opaque `let @Int` shadows
        the param, the ORIGINAL guarded param is reachable as `@Int.1` (prior
        slot).  Dividing by `@Int.1` discharges the outer `requires(@Int.0 != 0)`
        at Tier-1 — the shadow must not poison the still-visible outer slot, and
        De Bruijn must address the correct one."""
        result = _verify("""
private fn f(@Int -> @Int)
  requires(@Int.0 != 0)
  ensures(true)
  effects(<Random>)
{ let @Int = random_int(0, 10); 1 / @Int.1 }
""")
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert errors == [], [e.error_code for e in errors]
        divs = [o for o in result.obligations if o.kind == "div_zero"]
        assert len(divs) == 1 and divs[0].status == "verified", [
            (o.kind, o.status) for o in divs
        ]

    def test_two_opaque_lets_divide_by_each_keep_debruijn(self) -> None:
        """Two same-type opaque lets each occupy a distinct De Bruijn slot, and
        both shadow the guarded `requires(@Int.0 != 0)` outer.  The divisor
        `@Int.1` (the FIRST, prior let) is a tracked shadow → Tier-3; a lost
        shadow would resolve `@Int.1` to the guarded param and silently
        discharge.  Pins that the prior-slot divisor stays tracked (not
        collapsed onto the most-recent let or leaked to the param)."""
        result = _verify("""
private fn f(@Int -> @Int)
  requires(@Int.0 != 0)
  ensures(true)
  effects(<Random>)
{ let @Int = random_int(1, 10); let @Int = random_int(0, 10); @Int.0 / @Int.1 }
""")
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert errors == [], [e.error_code for e in errors]
        divs = [o for o in result.obligations if o.kind == "div_zero"]
        assert len(divs) == 1 and divs[0].status == "tier3", [
            (o.kind, o.status) for o in divs
        ]

    def test_two_ops_reuse_same_shadow_both_tier3(self) -> None:
        """A shadow stays opaque across MULTIPLE ops in the same body.  Both
        `1 / @Int.0` and `2 / @Int.0` over one opaque `let @Int` (shadowing a
        guarded `requires(@Int.0 != 0)` outer) each record a Tier-3 `div_zero`
        obligation — the first op must not "consume" the shadow and leave the
        second silently discharged against the stale `!= 0`."""
        result = _verify("""
private fn f(@Int -> @Int)
  requires(@Int.0 != 0)
  ensures(true)
  effects(<Random>)
{ let @Int = random_int(0, 10); (1 / @Int.0) + (2 / @Int.0) }
""")
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert errors == [], [e.error_code for e in errors]
        divs = [o for o in result.obligations if o.kind == "div_zero"]
        assert len(divs) == 2 and all(d.status == "tier3" for d in divs), [
            (o.kind, o.status) for o in divs
        ]

    def test_opaque_match_arm_divisor_does_not_use_stale_outer_guard(self) -> None:
        """Match-arm binding over an UNTRANSLATABLE scrutinee (effect op) shadows
        its pattern slot, so `1 / @Int.0` in the arm is Tier-3 even though an
        outer `@Int` param carries `requires(@Int.0 != 0)`.  The matched field
        can be 0; discharging against the outer guard would be a silent
        false-discharge."""
        result = _verify("""
effect Source {
  op next(Unit -> Option<Int>);
}

private fn f(@Int -> @Int)
  requires(@Int.0 != 0)
  ensures(true)
  effects(<Source>)
{ match Source.next(()) { Some(@Int) -> 1 / @Int.0, None -> 1 } }
""")
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert errors == [], [e.error_code for e in errors]
        divs = [o for o in result.obligations if o.kind == "div_zero"]
        assert len(divs) == 1 and divs[0].status == "tier3", [
            (o.kind, o.status) for o in divs
        ]


class TestShadowAuditSubtraction680:
    """Soundness battery for the `nat_sub` (#520, E502) underflow obligation
    under the shadow/projection machinery.

    Invariant trichotomy:
      * provably non-underflowing  -> 'verified' (Tier-1)
      * an opaque operand (direct OR embedded in a compound) for which the
        obligation is genuinely undecidable -> 'tier3' (runtime guard);
        MUST NOT be 'verified' (silent failure) NOR 'violated' (false E502)
      * provably underflowing for *every* runtime value -> 'violated' (E502)
    """

    def test_opaque_direct_operand_is_tier3(self) -> None:
        """A direct opaque shadow operand (`@Nat.0 - 1` after a non-literal
        destructure) is undecidable -> Tier-3, never a false E502."""
        st = _nat_sub_status(_MK + """
private fn d(@Nat -> @Nat)
  requires(true) ensures(true) effects(pure)
{ let Tuple<@Nat, @Nat> = mk(@Nat.0); @Nat.0 - 1 }
""")
        assert st == ["tier3"], st

    def test_opaque_both_compound_undecidable_is_tier3(self) -> None:
        """Both operands compound over *different* opaque shadows
        (`(@Nat.0 + 1) - (@Nat.1 + 1)`): neither a direct shadow, and
        `lhs >= rhs` / `lhs < rhs` both undecidable, so the recursive
        `_contains_opaque_shadow` guard routes to Tier-3, not E502."""
        st = _nat_sub_status(_MK + """
private fn c(@Nat -> @Nat)
  requires(true) ensures(true) effects(pure)
{ let Tuple<@Nat, @Nat> = mk(@Nat.0); (@Nat.0 + 1) - (@Nat.1 + 1) }
""")
        assert st == ["tier3"], st

    def test_opaque_compound_minus_direct_is_tier3(self) -> None:
        """Asymmetric compound/direct over different opaque shadows
        (`(@Nat.0 + 1) - @Nat.1`) is undecidable -> Tier-3."""
        st = _nat_sub_status(_MK + """
private fn c(@Nat -> @Nat)
  requires(true) ensures(true) effects(pure)
{ let Tuple<@Nat, @Nat> = mk(@Nat.0); (@Nat.0 + 1) - @Nat.1 }
""")
        assert st == ["tier3"], st

    def test_opaque_scaled_compound_undecidable_is_tier3(self) -> None:
        """Scaled compound over different opaque shadows
        (`(2 * @Nat.0) - (@Nat.1 + 5)`) is undecidable -> Tier-3."""
        st = _nat_sub_status(_MK + """
private fn c(@Nat -> @Nat)
  requires(true) ensures(true) effects(pure)
{ let Tuple<@Nat, @Nat> = mk(@Nat.0); (2 * @Nat.0) - (@Nat.1 + 5) }
""")
        assert st == ["tier3"], st

    def test_opaque_match_bound_operand_is_tier3(self) -> None:
        """A @Nat bound by matching `Some(@Nat)` over an opaque effect-op
        scrutinee (`Src.g(()) : Option<Nat>`) is opaque; `@Nat.0 - 1` in the
        arm is undecidable -> Tier-3, never a false E502."""
        st = _nat_sub_status("""
effect Src { op g(Unit -> Option<Nat>); }

private fn m(@Nat -> @Nat)
  requires(true) ensures(true) effects(<Src>)
{ match Src.g(()) { Some(@Nat) -> @Nat.0 - 1, None -> 0 } }
""")
        assert st == ["tier3"], st

    def test_param_requires_does_not_leak_to_shadow(self) -> None:
        """SILENT-FAILURE guard: a `requires(@Nat.0 >= 100)` constraining the
        *parameter* must NOT discharge an obligation whose operands are the
        independent destructured shadows -- the param is shadowed out of
        scope at the subtraction site, so it stays Tier-3 (not falsely
        'verified')."""
        st = _nat_sub_status(_MK + """
private fn leak(@Nat -> @Nat)
  requires(@Nat.0 >= 100)
  ensures(true) effects(pure)
{ let Tuple<@Nat, @Nat> = mk(@Nat.0); @Nat.0 - @Nat.1 }
""")
        assert st == ["tier3"], st

    def test_effect_op_nat_operands_are_tier3(self) -> None:
        """Two @Nat values produced by an effect op (`Rng.rand()`), let-bound
        and subtracted, are opaque -> Tier-3."""
        st = _nat_sub_status("""
effect Rng { op rand(Unit -> Nat); }

private fn e(@Unit -> @Nat)
  requires(true) ensures(true) effects(<Rng>)
{ let @Nat = Rng.rand(()); let @Nat = Rng.rand(()); @Nat.0 - @Nat.1 }
""")
        assert st == ["tier3"], st

    def test_compound_shadow_provably_safe_is_verified(self) -> None:
        """When the opaque shadow CANCELS so the obligation is decidable and
        true (`(@Nat.0 + 2) - (@Nat.0 + 1) == 1 >= 0` for all values), the
        compound-shadow Tier-3 fallback is correctly suppressed (its guard
        requires `lhs < rhs` to be non-valid) -> 'verified', not Tier-3.
        Pins that the fallback does not over-fire into a silent under-check."""
        st = _nat_sub_status(_MK + """
private fn safe(@Nat -> @Nat)
  requires(true) ensures(true) effects(pure)
{ let Tuple<@Nat, @Nat> = mk(@Nat.0); (@Nat.0 + 2) - (@Nat.0 + 1) }
""")
        assert st == ["verified"], st

    def test_compound_shadow_provably_underflow_is_violated(self) -> None:
        """When the opaque shadow CANCELS so underflow holds for *every*
        runtime value (`(@Nat.0 + 1) - (@Nat.0 + 2) == -1` for all values),
        this is a genuine bug -> loud 'violated'/E502, NOT a Tier-3 mask.
        Distinguishes 'undecidable-because-opaque' (Tier-3) from
        'decidably-underflows-regardless-of-opaque' (E502)."""
        r = _verify(_MK + """
private fn bad(@Nat -> @Nat)
  requires(true) ensures(true) effects(pure)
{ let Tuple<@Nat, @Nat> = mk(@Nat.0); (@Nat.0 + 1) - (@Nat.0 + 2) }
""")
        subs = [o.status for o in r.obligations if o.kind == "nat_sub"]
        assert subs == ["violated"], subs
        codes = [d.error_code for d in r.diagnostics if d.severity == "error"]
        assert "E502" in codes, codes

    def test_requires_ge_discharges_to_verified(self) -> None:
        """Baseline (no shadow): explicit `requires(@Nat.0 >= @Nat.1)` on the
        actual subtraction operands -> 'verified'."""
        st = _nat_sub_status("""
private fn safe(@Nat, @Nat -> @Nat)
  requires(@Nat.0 >= @Nat.1)
  ensures(true) effects(pure)
{ @Nat.0 - @Nat.1 }
""")
        assert st == ["verified"], st


class TestShadowAuditIndex680:
    """Soundness battery for the `index_bounds` (#680/E527) obligation under the
    shadow/projection machinery: in-bounds -> verified, provably-OOB ->
    violated, opaque length/index -> honest Tier-3 (never silent, never a false
    E527).  Array length is an uninterpreted SMT function (#427)."""

    def test_index_lower_edge_literal_discharges(self) -> None:
        """`[1, 2, 3][0]` — index 0 is the in-bounds lower edge -> Tier 1.
        Pins the `0 <= i` conjunct's *inclusive* lower edge."""
        result = _verify("""
private fn first(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ [1, 2, 3][0] }
""")
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert errors == [], [e.error_code for e in errors]
        idx = [o for o in result.obligations if o.kind == "index_bounds"]
        assert len(idx) == 1 and idx[0].status == "verified", [
            (o.kind, o.status) for o in idx
        ]

    def test_index_equals_opaque_length_is_violated(self) -> None:
        """`arr[array_length(arr)]` is out of bounds for ANY length, even an
        uninterpreted one: `i == length` makes `i >= length` tautologically
        valid -> loud E527 (not a silent drop on a non-numeric length)."""
        matched = _verify_err("""
private fn at_len(@Array<Int> -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Array<Int>.0[array_length(@Array<Int>.0)] }
""", "out of bounds")
        assert matched[0].error_code == "E527", matched[0].error_code

    def test_index_last_elem_opaque_length_is_tier3(self) -> None:
        """`arr[array_length(arr) - 1]` is in bounds iff `length > 0`, unknown
        for an opaque length -> honest Tier 3, never a false E527."""
        result = _verify("""
private fn last(@Array<Int> -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Array<Int>.0[array_length(@Array<Int>.0) - 1] }
""")
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert errors == [], [e.error_code for e in errors]
        idx = [o for o in result.obligations if o.kind == "index_bounds"]
        assert len(idx) == 1 and idx[0].status == "tier3", [
            (o.kind, o.status) for o in idx
        ]

    def test_unguarded_nat_index_into_literal_is_tier3_not_violated(self) -> None:
        """`[1, 2, 3][@Nat.0]` with an unconstrained `@Nat` — could be in range
        (0/1/2) so NOT provably OOB (no false E527), but could be >= 3 so not
        provably in bounds -> honest Tier 3."""
        result = _verify("""
private fn at(@Nat -> @Int)
  requires(true) ensures(true) effects(pure)
{ [1, 2, 3][@Nat.0] }
""")
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert errors == [], [e.error_code for e in errors]
        idx = [o for o in result.obligations if o.kind == "index_bounds"]
        assert len(idx) == 1 and idx[0].status == "tier3", [
            (o.kind, o.status) for o in idx
        ]

    def test_precondition_guards_wrong_array_stays_tier3(self) -> None:
        """A precondition bounding a DIFFERENT array than the one indexed must
        not discharge.  `requires(@Nat.0 < array_length(@Array<Int>.1))` but
        body indexes `@Array<Int>.0` -> Tier 3, never a silent 'verified'
        against an unrelated array's length (De Bruijn discrimination)."""
        result = _verify("""
private fn at(@Array<Int>, @Array<Int>, @Nat -> @Int)
  requires(@Nat.0 < array_length(@Array<Int>.1))
  ensures(true) effects(pure)
{ @Array<Int>.0[@Nat.0] }
""")
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert errors == [], [e.error_code for e in errors]
        idx = [o for o in result.obligations if o.kind == "index_bounds"]
        assert len(idx) == 1 and idx[0].status == "tier3", [
            (o.kind, o.status) for o in idx
        ]

    def test_precondition_guards_wrong_nat_index_stays_tier3(self) -> None:
        """A precondition bounding a DIFFERENT index var than the one used must
        not discharge.  Two `@Nat` params, `requires(@Nat.1 < array_length(arr))`
        but body indexes `@Nat.0` -> Tier 3 (the indexed var carries no upper
        bound)."""
        result = _verify("""
private fn at(@Array<Int>, @Nat, @Nat -> @Int)
  requires(@Nat.1 < array_length(@Array<Int>.0))
  ensures(true) effects(pure)
{ @Array<Int>.0[@Nat.0] }
""")
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert errors == [], [e.error_code for e in errors]
        idx = [o for o in result.obligations if o.kind == "index_bounds"]
        assert len(idx) == 1 and idx[0].status == "tier3", [
            (o.kind, o.status) for o in idx
        ]

    def test_reassign_to_longer_literal_uses_current_length(self) -> None:
        """Re-binding to a LONGER literal then indexing past the OLD length is
        valid against the CURRENT one.  `let a = [1,2]; let a = [1,2,3,4,5];
        a[4]` -> Tier 1 (4 < 5), reading the current binding's length."""
        result = _verify("""
private fn grow(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ let @Array<Int> = [1, 2]; let @Array<Int> = [1, 2, 3, 4, 5]; @Array<Int>.0[4] }
""")
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert errors == [], [e.error_code for e in errors]
        idx = [o for o in result.obligations if o.kind == "index_bounds"]
        assert len(idx) == 1 and idx[0].status == "verified", [
            (o.kind, o.status) for o in idx
        ]

    def test_reassign_to_shorter_literal_violates_current_length(self) -> None:
        """Re-binding to a SHORTER literal then indexing past the NEW length is
        provably OOB.  `let a = [1,2,3,4,5]; let a = [1,2]; a[4]` -> E527
        (4 >= 2), checking the shadowing binding's shorter length."""
        matched = _verify_err("""
private fn shrink(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ let @Array<Int> = [1, 2, 3, 4, 5]; let @Array<Int> = [1, 2]; @Array<Int>.0[4] }
""", "out of bounds")
        assert matched[0].error_code == "E527", matched[0].error_code

    def test_append_then_low_index_is_tier3_not_verified(self) -> None:
        """`let a = [1,2,3]; let a = array_append(a, 9); a[0]` — a[0] IS valid,
        but the appended length is OPAQUE, so the verifier cannot PROVE in
        bounds -> Tier 3.  A 'verified' would claim a Tier-1 proof the opaque
        length can't support (silent over-claim)."""
        result = _verify("""
private fn appended(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ let @Array<Int> = [1, 2, 3]; let @Array<Int> = array_append(@Array<Int>.0, 9); @Array<Int>.0[0] }
""")
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert errors == [], [e.error_code for e in errors]
        idx = [o for o in result.obligations if o.kind == "index_bounds"]
        assert len(idx) == 1 and idx[0].status == "tier3", [
            (o.kind, o.status) for o in idx
        ]

    def test_opaque_shadow_index_does_not_leak_outer_bound(self) -> None:
        """An index `let`-shadowing a guarded index param must be Tier-3, NOT
        silently verified against the stale outer bound.  The param carries
        `0 <= @Int.0 && @Int.0 < array_length(...)`; after `let @Int =
        random_int(...)`, `@Int.0` is the (unbounded) shadow, so the bounds are
        indeterminate → Tier 3.  A lost shadow would resolve `@Int.0` to the
        guarded param and falsely *verify* (silent failure) — the differential:
        the same body WITHOUT the `let` verifies at Tier 1, with it falls to
        Tier 3 (mutation-checked against the scalar `let`-shadow push)."""
        result = _verify("""
private fn idx(@Array<Int>, @Int -> @Int)
  requires(0 <= @Int.0 && @Int.0 < array_length(@Array<Int>.0))
  ensures(true) effects(<Random>)
{ let @Int = random_int(0, 5); @Array<Int>.0[@Int.0] }
""")
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert errors == [], [e.error_code for e in errors]
        idx = [o for o in result.obligations if o.kind == "index_bounds"]
        assert len(idx) == 1 and idx[0].status == "tier3", [
            (o.kind, o.status) for o in idx
        ]

    def test_literal_constructor_tuple_destructure_projects_lengths(self) -> None:
        """A LITERAL-constructor tuple destructure projects each component's
        length; De Bruijn indexes the right array.  `let Tuple<@Array, @Array>
        = Tuple([1,2,3], [9,9]); @Array<Int>.0[5]` -> `@Array<Int>.0` is the
        2nd component [9,9] (length 2), so [5] is OOB -> E527."""
        matched = _verify_err("""
private fn pick(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ let Tuple<@Array<Int>, @Array<Int>> = Tuple([1, 2, 3], [9, 9]); @Array<Int>.0[5] }
""", "out of bounds")
        assert matched[0].error_code == "E527", matched[0].error_code

    def test_call_sourced_tuple_destructure_array_is_tier3(self) -> None:
        """A tuple destructure whose source is a CALL cannot project, so each
        array slot shadows to an opaque array -> Tier 3, never a false E527
        against a stale same-type outer's length (the alignment trap)."""
        result = _verify("""
private fn mk(@Array<Int> -> @Tuple<Array<Int>, Int>)
  requires(true) ensures(true) effects(pure)
{ Tuple(@Array<Int>.0, 0) }

private fn destr(@Array<Int> -> @Int)
  requires(true) ensures(true) effects(pure)
{ let @Array<Int> = [1, 2, 3]; let Tuple<@Array<Int>, @Int> = mk(@Array<Int>.0); @Array<Int>.0[5] }
""")
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert errors == [], [e.error_code for e in errors]
        idx = [o for o in result.obligations if o.kind == "index_bounds"]
        assert len(idx) == 1 and idx[0].status == "tier3", [
            (o.kind, o.status) for o in idx
        ]

    def test_index_inside_quantifier_closure_not_obligated(self) -> None:
        """An index inside a `forall` quantifier closure body is NOT walked
        (captured length beyond Tier 1 without #427), so it records ZERO
        index_bounds obligations — left to the runtime trap (#779)."""
        result = _verify("""
private fn allpos(@Array<Int> -> @Bool)
  requires(true) ensures(true) effects(pure)
{ forall(@Int, array_length(@Array<Int>.0), fn(@Int -> @Bool) effects(pure) { @Array<Int>.1[5] == 0 }) }
""")
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert errors == [], [e.error_code for e in errors]
        idx = [o for o in result.obligations if o.kind == "index_bounds"]
        assert idx == [], f"quantifier-body index must not be obligated, got {len(idx)}"


class TestDestructureDeBruijnAlignment680:
    """Every destructure binding occupies exactly its De Bruijn slot, and a
    trapping op reads the value actually at that slot — never a stale sibling,
    never a collapsed/shifted index (#680 review's `collapse` failure class).
    Values are chosen so reading the WRONG sibling flips the verdict."""

    def test_literal_destructure_divisor_order_pins_first_component(self) -> None:
        """`Tuple(10, 0)`: `@Int.1` = first (10), `@Int.0` = second (0).
        Dividing by `@Int.1` discharges `10 != 0` — a swap onto the `0` sibling
        would flip to a false E526."""
        result = _verify("""
private fn lit_order_first(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ let Tuple<@Int, @Int> = Tuple(10, 0); @Int.0 / @Int.1 }
""")
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert errors == [], [e.error_code for e in errors]
        divs = [o for o in result.obligations if o.kind == "div_zero"]
        assert len(divs) == 1 and divs[0].status == "verified", [
            (o.kind, o.status) for o in divs
        ]

    def test_literal_destructure_divisor_order_pins_second_component(self) -> None:
        """`Tuple(10, 0)`: `@Int.0` = second (0) -> dividing by it is a provable
        E526.  Reading the `10` sibling would silently discharge a real zero."""
        _verify_err("""
private fn lit_order_second(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ let Tuple<@Int, @Int> = Tuple(10, 0); @Int.1 / @Int.0 }
""", "by zero")

    def test_mixed_literal_opaque_keeps_debruijn_no_collapse(self) -> None:
        """`Tuple(10, <opaque>)`: `@Int.0` = OPAQUE second component -> Tier 3,
        NOT shifted onto the literal `10`.  A skip would collapse `@Int.0` onto
        `10` and silently discharge (the worst #680 failure)."""
        result = _verify("""
private fn mixed_opaque_first(@Unit -> @Int)
  requires(true) ensures(true) effects(<Random>)
{ let Tuple<@Int, @Int> = Tuple(10, random_int(0, 10)); 1 / @Int.0 }
""")
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert errors == [], [e.error_code for e in errors]
        divs = [o for o in result.obligations if o.kind == "div_zero"]
        assert len(divs) == 1 and divs[0].status == "tier3", [
            (o.kind, o.status) for o in divs
        ]

    def test_mixed_literal_opaque_literal_component_still_tier1(self) -> None:
        """`Tuple(10, <opaque>)`: the literal `@Int.1` (10) stays Tier 1 even
        with an opaque sibling — projection precision survives a mixed source."""
        result = _verify("""
private fn mixed_opaque_lit(@Unit -> @Int)
  requires(true) ensures(true) effects(<Random>)
{ let Tuple<@Int, @Int> = Tuple(10, random_int(0, 10)); 1 / @Int.1 }
""")
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert errors == [], [e.error_code for e in errors]
        divs = [o for o in result.obligations if o.kind == "div_zero"]
        assert len(divs) == 1 and divs[0].status == "verified", [
            (o.kind, o.status) for o in divs
        ]

    def test_three_component_literal_each_index_reads_its_own(self) -> None:
        """`Tuple(10, 0, 7)`: `@Int.1` = middle (0 -> violated), `@Int.2` = first
        (7 -> safe).  Distinct values so any off-by-one flips a verdict."""
        _verify_err("""
private fn tri_middle(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ let Tuple<@Int, @Int, @Int> = Tuple(10, 0, 7); 1 / @Int.1 }
""", "by zero")
        _verify_ok("""
private fn tri_last(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ let Tuple<@Int, @Int, @Int> = Tuple(10, 0, 7); 1 / @Int.2 }
""")

    def test_intervening_different_type_does_not_shift_same_type_index(self) -> None:
        """`Tuple<@Int, @Nat, @Int> = Tuple(7, 99, 0)`: `@Int.0` skips the
        intervening `@Nat` to read the 3rd component (0 -> violated); `@Int.1`
        reads the first (7 -> safe).  Different types = different namespaces."""
        _verify_err("""
private fn interleaved_zero(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ let Tuple<@Int, @Nat, @Int> = Tuple(7, 99, 0); 1 / @Int.0 }
""", "by zero")
        _verify_ok("""
private fn interleaved_safe(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ let Tuple<@Int, @Nat, @Int> = Tuple(7, 99, 0); 1 / @Int.1 }
""")

    def test_destructure_zero_shadows_guarded_outer_param(self) -> None:
        """A destructure binding `0` that shadows a `requires(@Int.0 != 0)`
        outer param makes `@Int.0` read the destructured `0` (violated), not
        the stale guarded outer."""
        _verify_err("""
public fn destr_shadows_guard(@Int -> @Int)
  requires(@Int.0 != 0) ensures(true) effects(pure)
{ let Tuple<@Int, @Int> = Tuple(5, 0); 1 / @Int.0 }
""", "by zero")

    def test_opaque_destructure_component_not_discharged_by_outer_guard(self) -> None:
        """`requires(@Int.0 != 0)` then `let Tuple = Tuple(<opaque>, <opaque>)`:
        `@Int.0` = opaque -> Tier 3.  The outer `!= 0` must NOT leak through the
        shadow (silent-failure differential)."""
        result = _verify("""
public fn opaque_destr_guard(@Int -> @Int)
  requires(@Int.0 != 0) ensures(true) effects(<Random>)
{ let Tuple<@Int, @Int> = Tuple(random_int(0, 10), random_int(0, 10)); 1 / @Int.0 }
""")
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert errors == [], [e.error_code for e in errors]
        divs = [o for o in result.obligations if o.kind == "div_zero"]
        assert len(divs) == 1 and divs[0].status == "tier3", [
            (o.kind, o.status) for o in divs
        ]

    def test_stacked_destructures_deep_index_reaches_outer_first(self) -> None:
        """Two stacked literal destructures: `@Int.3` reaches PAST the inner two
        slots to the first component of the OUTER destructure.  Pins the 4-deep
        De Bruijn stack and stacked literal projection."""
        _verify_ok("""
private fn stacked_outer_safe(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ let Tuple<@Int, @Int> = Tuple(3, 9); let Tuple<@Int, @Int> = Tuple(0, 5); 1 / @Int.3 }
""")
        _verify_err("""
private fn stacked_outer_zero(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ let Tuple<@Int, @Int> = Tuple(0, 9); let Tuple<@Int, @Int> = Tuple(7, 5); 1 / @Int.3 }
""", "by zero")

    def test_nat_subtraction_destructure_projection_is_order_sensitive(self) -> None:
        """Non-commutative `@Nat` subtraction through projection: `Tuple(3, 10)`.
        `@Nat.1 - @Nat.0` = 3 - 10 underflows (E502); `@Nat.0 - @Nat.1` = 10 - 3
        is safe.  Alignment is op-agnostic."""
        _verify_err("""
private fn sub_underflow(@Unit -> @Nat)
  requires(true) ensures(true) effects(pure)
{ let Tuple<@Nat, @Nat> = Tuple(3, 10); @Nat.1 - @Nat.0 }
""", "underflow")
        _verify_ok("""
private fn sub_safe(@Unit -> @Nat)
  requires(true) ensures(true) effects(pure)
{ let Tuple<@Nat, @Nat> = Tuple(3, 10); @Nat.0 - @Nat.1 }
""")

    def test_index_bounds_destructure_projection_reads_right_index(self) -> None:
        """`index_bounds` through projection: `Tuple(5, 1)` indexing `[10,20,30]`.
        `[..][@Int.0]` = `[..][1]` in bounds; `[..][@Int.1]` = `[..][5]` OOB
        (E527).  Alignment holds for the index op too."""
        _verify_ok("""
private fn idx_inbounds(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ let Tuple<@Int, @Int> = Tuple(5, 1); [10, 20, 30][@Int.0] }
""")
        _verify_err("""
private fn idx_oob(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ let Tuple<@Int, @Int> = Tuple(5, 1); [10, 20, 30][@Int.1] }
""", "bounds")

    def test_refinement_typed_component_projects_value_and_invariant(self) -> None:
        """A refinement-typed component keeps its own namespace AND invariant:
        `Tuple<@PosInt, @Int> = Tuple(3, 0)`.  `@Int.0` = literal 0 (violated);
        `@PosInt.0` = 3, discharges `3 > 0 => != 0` (verified)."""
        _verify_err("""
type PosInt = { @Int | @Int.0 > 0 };

private fn refined_zero_sibling(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ let Tuple<@PosInt, @Int> = Tuple(3, 0); 1 / @Int.0 }
""", "by zero")
        _verify_ok("""
type PosInt = { @Int | @Int.0 > 0 };

private fn refined_posint_divisor(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ let Tuple<@PosInt, @Int> = Tuple(3, 0); 1 / @PosInt.0 }
""")


class TestShadowAuditInteractions680:
    """Cross-construct shadow interactions: a `1 / shadow` (or `%` / `@Nat -`)
    embedded in array-literals, asserts, nested blocks, nested matches, and
    alongside independent shadows must stay Tier-3 (never silent, never false),
    and shadows must respect block scoping (#680 audit, interaction dimension)."""

    def test_shadow_div_inside_array_literal_is_tier3(self) -> None:
        """A `1 / shadow` inside an array-literal element is Tier-3 — the
        array-lit walker arm recurses into elements and the opaque-shadow guard
        applies one host-construct deep."""
        result = _verify("""
private fn f(@Int -> @Array<Int>)
  requires(@Int.0 != 0) ensures(true) effects(<Random>)
{ let @Int = random_int(0, 10); [1 / @Int.0, 99] }
""")
        assert [d for d in result.diagnostics if d.severity == "error"] == []
        divs = [o for o in result.obligations if o.kind == "div_zero"]
        assert len(divs) == 1 and divs[0].status == "tier3", [(o.kind, o.status) for o in divs]

    def test_shadow_div_inside_assert_is_tier3(self) -> None:
        """`assert(1 / shadow > 0)` over an opaque `random_int` shadow is
        Tier-3 — the Assert walker arm recurses into the condition."""
        result = _verify("""
private fn f(@Int -> @Int)
  requires(@Int.0 != 0) ensures(true) effects(<Random>)
{ let @Int = random_int(0, 10); assert(1 / @Int.0 > 0); 0 }
""")
        assert [d for d in result.diagnostics if d.severity == "error"] == []
        divs = [o for o in result.obligations if o.kind == "div_zero"]
        assert len(divs) == 1 and divs[0].status == "tier3", [(o.kind, o.status) for o in divs]

    def test_let_value_is_opaque_match_then_divisor_is_tier3(self) -> None:
        """A `let @Int = match <opaque-scrutinee> {...}` value is opaque (the
        SMT layer returns None for a match over an effect op), so a later
        `1 / @Int.0` is Tier-3 even when both arms are non-zero literals (the
        arm taken is unknown)."""
        result = _verify("""
effect Src {
  op g(Unit -> Option<Int>);
}

private fn f(@Int -> @Int)
  requires(@Int.0 != 0) ensures(true) effects(<Src>)
{ let @Int = match Src.g(()) { Some(@Int) -> 7, None -> 1 }; 1 / @Int.0 }
""")
        assert [d for d in result.diagnostics if d.severity == "error"] == []
        divs = [o for o in result.obligations if o.kind == "div_zero"]
        assert len(divs) == 1 and divs[0].status == "tier3", [(o.kind, o.status) for o in divs]

    def test_nested_opaque_match_divisor_is_tier3(self) -> None:
        """A divisor in a `match` nested inside another `match`, both over an
        opaque effect-op scrutinee, is Tier-3 — `_fresh_pattern_env` shadows the
        inner pattern slot through two arm levels, never discharging against the
        outer `requires(@Int.0 != 0)`."""
        result = _verify("""
effect Src {
  op g(Unit -> Option<Int>);
}

private fn f(@Int -> @Int)
  requires(@Int.0 != 0) ensures(true) effects(<Src>)
{
  match Src.g(()) {
    Some(@Int) -> match Src.g(()) { Some(@Int) -> 1 / @Int.0, None -> 1 },
    None -> 1
  }
}
""")
        assert [d for d in result.diagnostics if d.severity == "error"] == []
        divs = [o for o in result.obligations if o.kind == "div_zero"]
        assert len(divs) == 1 and divs[0].status == "tier3", [(o.kind, o.status) for o in divs]

    def test_independent_shadows_do_not_cross_contaminate(self) -> None:
        """Two independent opaque shadows — a `random_int` Int and a
        `random_nat` Nat — keep separate obligations: the `1 / @Int.0` div and
        the `@Nat.0 - @Nat.1` subtraction each fall to their own Tier-3,
        neither masking nor leaking onto the other."""
        result = _verify("""
private fn f(@Int, @Nat -> @Array<Int>)
  requires(@Int.0 != 0) ensures(true) effects(<Random>)
{
  let @Int = random_int(0, 9);
  let @Nat = random_nat(0, 9);
  [1 / @Int.0, @Nat.0 - @Nat.1]
}
""")
        assert [d for d in result.diagnostics if d.severity == "error"] == []
        divs = [o for o in result.obligations if o.kind == "div_zero"]
        subs = [o for o in result.obligations if o.kind == "nat_sub"]
        assert len(divs) == 1 and divs[0].status == "tier3", [(o.kind, o.status) for o in divs]
        assert len(subs) == 1 and subs[0].status == "tier3", [(o.kind, o.status) for o in subs]

    def test_division_before_shadow_let_stays_tier1(self) -> None:
        """A division by the constrained param *before* an opaque shadow let is
        Tier-1; a division by the shadow *after* is Tier-3.  The shadow applies
        only from its binding point onward (intra-block scoping)."""
        result = _verify("""
private fn f(@Int -> @Array<Int>)
  requires(@Int.0 != 0) ensures(true) effects(<Random>)
{
  let @Int = 1 / @Int.0;
  let @Int = random_int(0, 9);
  [@Int.1, 1 / @Int.0]
}
""")
        assert [d for d in result.diagnostics if d.severity == "error"] == []
        divs = [o for o in result.obligations if o.kind == "div_zero"]
        statuses = sorted(o.status for o in divs)
        assert statuses == ["tier3", "verified"], [(o.kind, o.status) for o in divs]

    def test_nested_block_shadow_does_not_leak_to_outer_divisor(self) -> None:
        """An opaque shadow bound inside a nested block does not bleed onto an
        outer divisor.  `let @Int = { let @Int = random_int(...); ... }; 1 /
        @Int.1` divides by the outer constrained param (`@Int.1`), Tier-1."""
        result = _verify("""
private fn f(@Int -> @Int)
  requires(@Int.0 != 0) ensures(true) effects(<Random>)
{
  let @Int = { let @Int = random_int(0, 9); @Int.0 + 0 };
  1 / @Int.1
}
""")
        assert [d for d in result.diagnostics if d.severity == "error"] == []
        divs = [o for o in result.obligations if o.kind == "div_zero"]
        assert len(divs) == 1 and divs[0].status == "verified", [(o.kind, o.status) for o in divs]

    def test_nested_block_opaque_return_bound_to_outer_let_is_tier3(self) -> None:
        """When a nested block's RETURN value is opaque (a `random_int` in inner
        scope) and is bound to an outer `let`, a division by that outer binding
        is Tier-3 (the outer let value translates to None)."""
        result = _verify("""
private fn f(@Int -> @Int)
  requires(@Int.0 != 0) ensures(true) effects(<Random>)
{
  let @Int = { let @Int = random_int(0, 9); @Int.0 };
  1 / @Int.0
}
""")
        assert [d for d in result.diagnostics if d.severity == "error"] == []
        divs = [o for o in result.obligations if o.kind == "div_zero"]
        assert len(divs) == 1 and divs[0].status == "tier3", [(o.kind, o.status) for o in divs]

    def test_modulo_in_opaque_match_arm_is_tier3(self) -> None:
        """The modulo analogue of the opaque-match-scrutinee case: `1 % @Int.0`
        in an arm over an opaque effect op is Tier-3 (modulo carries the same
        `!= 0` obligation)."""
        result = _verify("""
effect Src {
  op g(Unit -> Option<Int>);
}

private fn f(@Int -> @Int)
  requires(@Int.0 != 0) ensures(true) effects(<Src>)
{ match Src.g(()) { Some(@Int) -> 1 % @Int.0, None -> 1 } }
""")
        assert [d for d in result.diagnostics if d.severity == "error"] == []
        divs = [o for o in result.obligations if o.kind == "div_zero"]
        assert len(divs) == 1 and divs[0].status == "tier3", [(o.kind, o.status) for o in divs]

    def test_nat_sub_in_opaque_match_arm_is_tier3(self) -> None:
        """The subtraction analogue: `@Nat.0 - @Nat.1` in an arm over an opaque
        effect op (returning Option<Nat>) is Tier-3 — the matched field is an
        opaque shadow, so the underflow obligation can't discharge against it."""
        result = _verify("""
effect SrcN {
  op g(Unit -> Option<Nat>);
}

private fn f(@Nat -> @Nat)
  requires(true) ensures(true) effects(<SrcN>)
{ match SrcN.g(()) { Some(@Nat) -> @Nat.0 - @Nat.1, None -> 0 } }
""")
        assert [d for d in result.diagnostics if d.severity == "error"] == []
        subs = [o for o in result.obligations if o.kind == "nat_sub"]
        assert len(subs) == 1 and subs[0].status == "tier3", [(o.kind, o.status) for o in subs]


# =====================================================================
# Obligation-record completeness (#387 mutation sweep — V0)
#
# The #680/#552/#520 batteries pin each obligation's `kind` + `status`.
# These pin the REMAINING `ProofObligation` fields — `fn_name`,
# `error_code`, `counterexample`, `expr_text` — across the
# `_check_*_obligation` discharge layer and its `_report_*` siblings.
# The coarse `_verify_err` / `_verify_ok` helpers only assert "an error
# exists", so a mutation that drops `fn_name` (→ `None`), nulls the
# counterexample, or flips an `error_code` string survives them.  A
# distinct `_387` function name per test ensures the `None`-substitution
# mutant (`_record_obligation(None, ...)`) cannot coincide with a default.
# =====================================================================

class TestObligationRecordCompleteness387:
    """Pin every `ProofObligation` field at the primitive-safety discharge
    sites so the discharge / report bookkeeping cannot silently mutate."""

    def test_div_zero_violation_pins_full_record(self) -> None:
        result = _verify("""
private fn unsafe_div_387(@Int, @Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ @Int.0 / @Int.1 }
""")
        divs = [o for o in result.obligations if o.kind == "div_zero"]
        assert len(divs) == 1, [(o.kind, o.status) for o in divs]
        o = divs[0]
        assert o.status == "violated", o.status
        assert o.error_code == "E526", o.error_code
        assert o.fn_name == "unsafe_div_387", o.fn_name
        assert o.counterexample, o.counterexample
        assert o.expr_text == "@Int.0 / @Int.1", o.expr_text
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert [e.error_code for e in errors] == ["E526"], [
            (e.error_code, e.description) for e in errors]

    def test_div_zero_verified_pins_record(self) -> None:
        result = _verify("""
private fn safe_div_387(@Int, @Int -> @Int)
  requires(@Int.1 != 0)
  ensures(true)
  effects(pure)
{ @Int.0 / @Int.1 }
""")
        assert [d for d in result.diagnostics if d.severity == "error"] == []
        divs = [o for o in result.obligations if o.kind == "div_zero"]
        assert len(divs) == 1, [(o.kind, o.status) for o in divs]
        o = divs[0]
        assert o.status == "verified", o.status
        assert o.fn_name == "safe_div_387", o.fn_name
        assert o.error_code == "", o.error_code
        assert o.counterexample is None, o.counterexample

    def test_nat_sub_violation_pins_full_record(self) -> None:
        result = _verify("""
private fn unsafe_sub_387(@Nat, @Nat -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{ @Nat.0 - @Nat.1 }
""")
        subs = [o for o in result.obligations if o.kind == "nat_sub"]
        assert len(subs) == 1, [(o.kind, o.status) for o in subs]
        o = subs[0]
        assert o.status == "violated", o.status
        assert o.error_code == "E502", o.error_code
        assert o.fn_name == "unsafe_sub_387", o.fn_name
        assert o.counterexample, o.counterexample
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert [e.error_code for e in errors] == ["E502"], [
            (e.error_code, e.description) for e in errors]

    def test_nat_sub_verified_pins_record(self) -> None:
        result = _verify("""
private fn safe_sub_387(@Nat, @Nat -> @Nat)
  requires(@Nat.0 >= @Nat.1)
  ensures(true)
  effects(pure)
{ @Nat.0 - @Nat.1 }
""")
        assert [d for d in result.diagnostics if d.severity == "error"] == []
        subs = [o for o in result.obligations if o.kind == "nat_sub"]
        assert len(subs) == 1, [(o.kind, o.status) for o in subs]
        o = subs[0]
        assert o.status == "verified", o.status
        assert o.fn_name == "safe_sub_387", o.fn_name
        assert o.error_code == "", o.error_code

    def test_index_oob_violation_pins_full_record(self) -> None:
        result = _verify("""
private fn oob_387(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ [1, 2, 3][5] }
""")
        idxs = [o for o in result.obligations if o.kind == "index_bounds"]
        assert len(idxs) == 1, [(o.kind, o.status) for o in idxs]
        o = idxs[0]
        assert o.status == "violated", o.status
        assert o.error_code == "E527", o.error_code
        assert o.fn_name == "oob_387", o.fn_name
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert [e.error_code for e in errors] == ["E527"], [
            (e.error_code, e.description) for e in errors]

    def test_index_in_bounds_verified_pins_record(self) -> None:
        result = _verify("""
private fn inbounds_387(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ [10, 20, 30][1] }
""")
        assert [d for d in result.diagnostics if d.severity == "error"] == []
        idxs = [o for o in result.obligations if o.kind == "index_bounds"]
        assert len(idxs) == 1, [(o.kind, o.status) for o in idxs]
        o = idxs[0]
        assert o.status == "verified", o.status
        assert o.fn_name == "inbounds_387", o.fn_name
        assert o.error_code == "", o.error_code

    # --- _report_* diagnostic content (deterministic; runs after the solver) ---

    def test_div_by_zero_diagnostic_content(self) -> None:
        """Pin the E526 diagnostic's description / rationale / fix / spec_ref /
        counterexample (`_report_div_by_zero`), not just its code."""
        result = _verify("""
private fn unsafe_div_387(@Int, @Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ @Int.0 / @Int.1 }
""")
        errs = [d for d in result.diagnostics if d.error_code == "E526"]
        assert len(errs) == 1, [d.description for d in result.diagnostics]
        d = errs[0]
        assert "unsafe_div_387" in d.description, d.description
        assert "may divide by zero" in d.description, d.description
        assert "division" in d.description, d.description
        assert "Counterexample" in d.description, d.description
        assert "@Int.1 = " in d.description, d.description
        assert "divisor is non-zero" in d.rationale, d.rationale
        assert "i64.div_s" in d.rationale, d.rationale
        assert "requires(@Int.1 != 0)" in d.fix, d.fix
        assert "6.4.3" in d.spec_ref, d.spec_ref

    def test_modulo_diagnostic_says_modulo(self) -> None:
        """`a % b` must report "modulo", not "division" — pins the
        `op_word = "modulo" if MOD else "division"` branch (`_report_div_by_zero`)."""
        result = _verify("""
private fn unsafe_mod_387(@Int, @Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ @Int.0 % @Int.1 }
""")
        errs = [d for d in result.diagnostics if d.error_code == "E526"]
        assert len(errs) == 1, [d.description for d in result.diagnostics]
        assert "modulo" in errs[0].description, errs[0].description
        assert "division" not in errs[0].description, errs[0].description

    def test_float_divisor_is_exempt_no_obligation(self) -> None:
        """A `@Float64` divisor traps to inf/NaN, not a runtime trap, so it
        carries NO `div_zero` obligation — pins the float64 early-exit guard
        in `_check_div_zero_obligation` (a mutation here would emit a bogus
        E526 on float division)."""
        result = _verify("""
private fn fdiv_387(@Float64, @Float64 -> @Float64)
  requires(true) ensures(true) effects(pure)
{ @Float64.0 / @Float64.1 }
""")
        assert [d for d in result.diagnostics if d.severity == "error"] == []
        assert [o for o in result.obligations if o.kind == "div_zero"] == [], [
            (o.kind, o.status) for o in result.obligations]

    def test_underflow_diagnostic_content(self) -> None:
        """Pin the E502 diagnostic's description / rationale / fix / spec_ref
        (`_report_underflow`)."""
        result = _verify("""
private fn unsafe_sub_387(@Nat, @Nat -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{ @Nat.0 - @Nat.1 }
""")
        errs = [d for d in result.diagnostics if d.error_code == "E502"]
        assert len(errs) == 1, [d.description for d in result.diagnostics]
        d = errs[0]
        assert "unsafe_sub_387" in d.description, d.description
        assert "may underflow" in d.description, d.description
        assert "@Nat subtraction" in d.description, d.description
        assert "Counterexample" in d.description, d.description
        # The counterexample loop renders each non-@result slot as
        # `    <name> = <value>`; pin the format (value is Z3-chosen).
        assert "@Nat.0 = " in d.description, d.description
        assert "@Nat.1 = " in d.description, d.description
        assert "non-negativity" in d.rationale, d.rationale
        assert "requires(@Nat.0 >= @Nat.1)" in d.fix, d.fix
        assert "4.4" in d.spec_ref, d.spec_ref

    def test_index_oob_diagnostic_content(self) -> None:
        """Pin the E527 diagnostic's description / rationale / fix / spec_ref
        (`_report_index_oob`)."""
        result = _verify("""
private fn oob_387(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ [1, 2, 3][5] }
""")
        errs = [d for d in result.diagnostics if d.error_code == "E527"]
        assert len(errs) == 1, [d.description for d in result.diagnostics]
        d = errs[0]
        assert "oob_387" in d.description, d.description
        assert "out of bounds" in d.description, d.description
        assert "array_length" in d.rationale, d.rationale
        assert "array_length" in d.fix, d.fix
        assert "6.4.3" in d.spec_ref, d.spec_ref

    def test_nat_binding_violation_pins_record_and_content(self) -> None:
        """`let @Nat = @Int.0` (unguarded) → E503 nat_bind violation;
        pins the record fields + `_report_nat_binding` content."""
        result = _verify("""
private fn narrow_neg_387(@Int -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Nat = @Int.0;
  @Nat.0
}
""")
        binds = [o for o in result.obligations if o.kind == "nat_bind"]
        assert len(binds) == 1, [(o.kind, o.status) for o in binds]
        o = binds[0]
        assert o.status == "violated", o.status
        assert o.error_code == "E503", o.error_code
        assert o.fn_name == "narrow_neg_387", o.fn_name
        assert o.counterexample, o.counterexample
        errs = [d for d in result.diagnostics if d.error_code == "E503"]
        assert len(errs) == 1, [d.description for d in result.diagnostics]
        d = errs[0]
        assert "narrow_neg_387" in d.description, d.description
        assert "narrowing into a @Nat" in d.description, d.description
        assert "may be negative" in d.description, d.description
        assert "Counterexample" in d.description, d.description
        assert "@Int.0 = " in d.description, d.description
        assert "non-negativity invariant" in d.rationale, d.rationale
        assert "requires(@Int.0 >= 0)" in d.fix, d.fix
        assert "4.7" in d.spec_ref, d.spec_ref

    def test_nat_binding_verified_pins_record(self) -> None:
        result = _verify("""
private fn narrow_ok_387(@Int -> @Nat)
  requires(@Int.0 >= 0)
  ensures(true)
  effects(pure)
{
  let @Nat = @Int.0;
  @Nat.0
}
""")
        assert [d for d in result.diagnostics if d.severity == "error"] == []
        binds = [o for o in result.obligations if o.kind == "nat_bind"]
        assert len(binds) == 1, [(o.kind, o.status) for o in binds]
        o = binds[0]
        assert o.status == "verified", o.status
        assert o.fn_name == "narrow_ok_387", o.fn_name
        assert o.error_code == "", o.error_code

    def test_postcondition_violation_diagnostic_content(self) -> None:
        """A false `ensures` → E500; pins `_report_violation`'s description /
        rationale / fix (all three repair classes, #675) / spec_ref + the
        recorded `ensures` obligation."""
        result = _verify("""
private fn bad_post_387(@Int -> @Int)
  requires(true)
  ensures(@Int.result > @Int.0)
  effects(pure)
{ @Int.0 }
""")
        errs = [d for d in result.diagnostics if d.error_code == "E500"]
        assert len(errs) == 1, [d.description for d in result.diagnostics]
        d = errs[0]
        assert "Postcondition does not hold" in d.description, d.description
        assert "bad_post_387" in d.description, d.description
        assert "Counterexample" in d.description, d.description
        # E500 also renders the @result slot via `_type_expr_to_slot_name`.
        assert "@Int.0 = " in d.description, d.description
        assert "@Int.result = " in d.description, d.description
        assert "concrete input values" in d.rationale, d.rationale
        assert "implementation" in d.fix, d.fix
        assert "strengthen" in d.fix and "requires(" in d.fix, d.fix
        assert "ensures(" in d.fix, d.fix
        assert "6.4.1" in d.spec_ref, d.spec_ref
        # The E500 code lives on the diagnostic (asserted above); the
        # `ensures` obligation records kind + status + fn_name (no error_code).
        viol = [o for o in result.obligations
                if o.kind == "ensures" and o.status == "violated"]
        assert len(viol) == 1, [(o.kind, o.status) for o in result.obligations]
        assert viol[0].fn_name == "bad_post_387", viol[0].fn_name

    # --- summary-counter bookkeeping ------------------------------------
    # Pin `tier1_verified` / `tier3_runtime` / `total` so a `summary.X += 1`
    # cannot silently mutate to `= 1` or `+= 2`.  A guarded obligation already
    # sits at counter >= 1 (requires + ensures discharged first), so ONE
    # obligation pins the verified + total counters.  The tier3 counter starts
    # at 0 (contracts verify, they don't go tier3), so TWO tier3 sites are
    # needed to make `tier3_runtime += 1 → = 1` observable.

    def test_div_verified_summary_counts(self) -> None:
        result = _verify("""
private fn sdiv_387(@Int, @Int -> @Int)
  requires(@Int.1 != 0) ensures(true) effects(pure)
{ @Int.0 / @Int.1 }
""")
        s = result.summary
        assert (s.tier1_verified, s.tier3_runtime, s.total) == (3, 0, 3), (
            s.tier1_verified, s.tier3_runtime, s.total)

    def test_div_two_tier3_summary_counts(self) -> None:
        result = _verify("""
effect Src387 { op g(Unit -> Option<Int>); }
private fn d1_387(@Int -> @Int)
  requires(@Int.0 != 0) ensures(true) effects(<Src387>)
{ match Src387.g(()) { Some(@Int) -> 1 / @Int.0, None -> 1 } }
private fn d2_387(@Int -> @Int)
  requires(@Int.0 != 0) ensures(true) effects(<Src387>)
{ match Src387.g(()) { Some(@Int) -> 1 / @Int.0, None -> 1 } }
""")
        s = result.summary
        divs = [o for o in result.obligations if o.kind == "div_zero"]
        assert [o.status for o in divs] == ["tier3", "tier3"], [
            (o.kind, o.status) for o in result.obligations]
        assert (s.tier1_verified, s.tier3_runtime, s.total) == (4, 2, 6), (
            s.tier1_verified, s.tier3_runtime, s.total)

    def test_sub_verified_summary_counts(self) -> None:
        result = _verify("""
private fn ssub_387(@Nat, @Nat -> @Nat)
  requires(@Nat.0 >= @Nat.1) ensures(true) effects(pure)
{ @Nat.0 - @Nat.1 }
""")
        s = result.summary
        assert (s.tier1_verified, s.tier3_runtime, s.total) == (3, 0, 3), (
            s.tier1_verified, s.tier3_runtime, s.total)

    def test_sub_two_tier3_summary_counts(self) -> None:
        result = _verify("""
effect SrcN387 { op g(Unit -> Option<Nat>); }
private fn s1_387(@Nat -> @Nat)
  requires(true) ensures(true) effects(<SrcN387>)
{ match SrcN387.g(()) { Some(@Nat) -> @Nat.0 - @Nat.1, None -> 0 } }
private fn s2_387(@Nat -> @Nat)
  requires(true) ensures(true) effects(<SrcN387>)
{ match SrcN387.g(()) { Some(@Nat) -> @Nat.0 - @Nat.1, None -> 0 } }
""")
        s = result.summary
        subs = [o for o in result.obligations if o.kind == "nat_sub"]
        assert [o.status for o in subs] == ["tier3", "tier3"], [
            (o.kind, o.status) for o in result.obligations]
        assert s.tier3_runtime == 2, s.tier3_runtime

    def test_index_verified_summary_counts(self) -> None:
        result = _verify("""
private fn sidx_387(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ [10, 20, 30][1] }
""")
        s = result.summary
        assert (s.tier1_verified, s.tier3_runtime, s.total) == (3, 0, 3), (
            s.tier1_verified, s.tier3_runtime, s.total)

    def test_index_two_tier3_summary_counts(self) -> None:
        result = _verify("""
private fn i1_387(@Array<Int>, @Nat -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Array<Int>.0[@Nat.0] }
private fn i2_387(@Array<Int>, @Nat -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Array<Int>.0[@Nat.0] }
""")
        s = result.summary
        idxs = [o for o in result.obligations if o.kind == "index_bounds"]
        assert [o.status for o in idxs] == ["tier3", "tier3"], [
            (o.kind, o.status) for o in result.obligations]
        assert s.tier3_runtime == 2, s.tier3_runtime

    def test_nat_binding_verified_summary_counts(self) -> None:
        result = _verify("""
private fn nbind_ok_387(@Int -> @Nat)
  requires(@Int.0 >= 0) ensures(true) effects(pure)
{ let @Nat = @Int.0; @Nat.0 }
""")
        s = result.summary
        assert (s.tier1_verified, s.tier3_runtime, s.total) == (3, 0, 3), (
            s.tier1_verified, s.tier3_runtime, s.total)

    # --- refinement-predicate binding (refine_bind, E505) ----------------

    def test_refined_binding_violation_pins_record_and_content(self) -> None:
        """`let @Pos387 = @Int.0 - 100` cannot prove `> 0` → E505 refine_bind
        violation; pins the record fields + `_report_refined_binding` content."""
        result = _verify("""
type Pos387 = { @Int | @Int.0 > 0 };

private fn rbind_neg_387(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ let @Pos387 = @Int.0 - 100; @Pos387.0 }
""")
        binds = [o for o in result.obligations if o.kind == "refine_bind"]
        assert len(binds) == 1, [(o.kind, o.status) for o in binds]
        o = binds[0]
        assert o.status == "violated", o.status
        assert o.error_code == "E505", o.error_code
        assert o.fn_name == "rbind_neg_387", o.fn_name
        assert o.counterexample, o.counterexample
        errs = [d for d in result.diagnostics if d.error_code == "E505"]
        assert len(errs) == 1, [d.description for d in result.diagnostics]
        d = errs[0]
        assert "rbind_neg_387" in d.description, d.description
        assert "may violate the refinement predicate" in d.description, d.description
        assert "Counterexample" in d.description, d.description
        assert "@Int.0 = " in d.description, d.description
        assert "refinement type" in d.rationale, d.rationale
        assert "requires(" in d.fix, d.fix
        assert "2.6" in d.spec_ref, d.spec_ref

    def test_refined_binding_verified_pins_record(self) -> None:
        result = _verify("""
type Pos387 = { @Int | @Int.0 > 0 };

private fn rbind_ok_387(@Int -> @Int)
  requires(@Int.0 > 0) ensures(true) effects(pure)
{ let @Pos387 = @Int.0; @Pos387.0 }
""")
        assert [d for d in result.diagnostics if d.severity == "error"] == []
        binds = [o for o in result.obligations if o.kind == "refine_bind"]
        assert len(binds) == 1, [(o.kind, o.status) for o in binds]
        o = binds[0]
        assert o.status == "verified", o.status
        assert o.fn_name == "rbind_ok_387", o.fn_name
        assert o.error_code == "", o.error_code


class TestProjectionHelpers387:
    """#387: pin the De Bruijn *projection* / *term* obligation helpers — the
    methods that obligate a @Nat / refined narrowing against an uninterpreted
    field-accessor Z3 term rather than an AST node.

    These have no translation step and (for ADT sub-patterns / nested ctor
    patterns) no Tier-3 ``let``-downgrade, so an undischarged obligation is a
    genuine E503 / E505.  The De Bruijn projection math (which accessor index
    maps to which obligation) is SOUNDNESS: a ``(idx, i)`` off-by-one silently
    obligates the wrong field, flipping an obligation's existence or verdict.

    Reachability (probed):
      - ``_check_nat_binding_obligation_term`` / ``_obligate_subpattern_
        narrowings``: ``match opt { Some(@Nat) -> ... }`` on ``Option<Int>``
        (the @Int payload narrows into @Nat).
      - ``_check_refined_binding_obligation_term``: same shape narrowing into a
        refined type (``Some(@Pos387)`` on ``Option<Int>``) → E505.
      - ``_obligate_subpattern_term``: nested ``Some(Some(@Nat))`` on
        ``Option<Option<Int>>``.
      - ``_obligate_destructure_narrowings``: ``let Tuple<@Nat,@Nat> = mk()``.

    Assertions use ``==`` on obligation fields/codes (mutmut wraps string
    literals as ``"XX"+s+"XX"``, so substring ``in`` does NOT kill a string
    mutation) and exact tuples on the summary counters.  Distinct ``_387``
    function names catch a ``fn_name → None`` mutation.
    """

    # =================================================================
    # _check_nat_binding_obligation_term  (3243-3283)
    # via _obligate_subpattern_narrowings opaque path (Some(@Nat))
    # =================================================================

    def test_nat_subpattern_violated_pins_record_and_content(self) -> None:
        """``Some(@Nat)`` on ``Option<Int>`` (unguarded @Int payload) → E503.
        Pins the violated branch: status/code/fn_name/CE + ``total -= 1`` and
        the ``_report_nat_binding`` "ADT sub-pattern bind" diagnostic."""
        result = _verify("""
private fn sp_nat_neg_387(@Option<Int> -> @Nat)
  requires(true) ensures(true) effects(pure)
{ match @Option<Int>.0 { Some(@Nat) -> @Nat.0, None -> 0 } }
""")
        binds = [o for o in result.obligations if o.kind == "nat_bind"]
        assert len(binds) == 1, [(o.kind, o.status) for o in result.obligations]
        o = binds[0]
        assert o.kind == "nat_bind", o.kind
        assert o.status == "violated", o.status
        assert o.error_code == "E503", o.error_code
        assert o.fn_name == "sp_nat_neg_387", o.fn_name
        assert o.counterexample, o.counterexample
        errs = [d for d in result.diagnostics if d.error_code == "E503"]
        assert len(errs) == 1, [d.description for d in result.diagnostics]
        d = errs[0]
        assert "sp_nat_neg_387" in d.description, d.description
        assert "ADT sub-pattern bind" in d.description, d.description
        assert "may be negative" in d.description, d.description
        assert "Counterexample" in d.description, d.description
        # The narrowed @Nat obligation decrements `total` (it's an error, not a
        # counted verdict); requires + ensures remain the only counted verdicts.
        s = result.summary
        assert (s.tier1_verified, s.tier3_runtime, s.total) == (2, 0, 2), (
            s.tier1_verified, s.tier3_runtime, s.total)

    def test_nat_subpattern_verified_pins_record(self) -> None:
        """``Some(@Nat)`` on ``Option<Pos387>`` — the source field is ``> 0``
        hence ``>= 0``, so the projection VERIFIES.  Pins the verified branch
        (``tier1_verified += 1``, status ``verified``, empty code, no CE) AND
        the ``source_ty`` premise: drop the ``_term_source_fact`` assumption and
        this flips to a false E503."""
        result = _verify("""
type Pos387 = { @Int | @Int.0 > 0 };
private fn sp_nat_ok_387(@Option<Pos387> -> @Nat)
  requires(true) ensures(true) effects(pure)
{ match @Option<Pos387>.0 { Some(@Nat) -> @Nat.0, None -> 0 } }
""")
        assert [d for d in result.diagnostics if d.severity == "error"] == [], [
            d.description for d in result.diagnostics if d.severity == "error"]
        binds = [o for o in result.obligations if o.kind == "nat_bind"]
        assert len(binds) == 1, [(o.kind, o.status) for o in result.obligations]
        o = binds[0]
        assert o.status == "verified", o.status
        assert o.error_code == "", o.error_code
        assert o.fn_name == "sp_nat_ok_387", o.fn_name
        assert o.counterexample is None, o.counterexample
        # verified narrowing counts: requires + nat_bind + ensures.
        s = result.summary
        assert (s.tier1_verified, s.tier3_runtime, s.total) == (3, 0, 3), (
            s.tier1_verified, s.tier3_runtime, s.total)

    # =================================================================
    # _check_refined_binding_obligation_term  (3495-3548)
    # via _obligate_subpattern_narrowings (Some(@Pos387))
    # =================================================================

    def test_refined_subpattern_violated_pins_record_and_content(self) -> None:
        """``Some(@Pos387)`` on ``Option<Int>`` → E505 (Int payload may be
        ``<= 0``).  Pins the violated branch of
        ``_check_refined_binding_obligation_term``: refine_bind / E505 / CE /
        ``total -= 1`` + the predicate text in the diagnostic."""
        result = _verify("""
type Pos387 = { @Int | @Int.0 > 0 };
private fn sp_ref_neg_387(@Option<Int> -> @Int)
  requires(true) ensures(true) effects(pure)
{ match @Option<Int>.0 { Some(@Pos387) -> @Pos387.0, None -> 1 } }
""")
        binds = [o for o in result.obligations if o.kind == "refine_bind"]
        assert len(binds) == 1, [(o.kind, o.status) for o in result.obligations]
        o = binds[0]
        assert o.kind == "refine_bind", o.kind
        assert o.status == "violated", o.status
        assert o.error_code == "E505", o.error_code
        assert o.fn_name == "sp_ref_neg_387", o.fn_name
        assert o.counterexample, o.counterexample
        errs = [d for d in result.diagnostics if d.error_code == "E505"]
        assert len(errs) == 1, [d.description for d in result.diagnostics]
        d = errs[0]
        assert "sp_ref_neg_387" in d.description, d.description
        assert "ADT sub-pattern bind" in d.description, d.description
        assert "@Int.0 > 0" in d.description, d.description
        s = result.summary
        assert (s.tier1_verified, s.tier3_runtime, s.total) == (2, 0, 2), (
            s.tier1_verified, s.tier3_runtime, s.total)

    def test_refined_subpattern_verified_pins_source_fact(self) -> None:
        """``Some(@Pos387)`` (``> 0``) on ``Option<Gt5_387>`` (``> 5``): a
        GENUINE narrowing (the predicates differ) that nonetheless holds —
        because the ``source_ty`` premise ``> 5`` implies ``> 0``.  Soundness:
        if ``_term_source_fact`` drops the source predicate, this flips to a
        false E505; if ``_refined_field_narrows`` mis-fires, the obligation
        vanishes entirely."""
        result = _verify("""
type Gt5_387 = { @Int | @Int.0 > 5 };
type Pos387 = { @Int | @Int.0 > 0 };
private fn sp_ref_ok_387(@Option<Gt5_387> -> @Int)
  requires(true) ensures(true) effects(pure)
{ match @Option<Gt5_387>.0 { Some(@Pos387) -> @Pos387.0, None -> 1 } }
""")
        assert [d for d in result.diagnostics if d.severity == "error"] == [], [
            d.description for d in result.diagnostics if d.severity == "error"]
        binds = [o for o in result.obligations if o.kind == "refine_bind"]
        assert len(binds) == 1, [(o.kind, o.status) for o in result.obligations]
        o = binds[0]
        assert o.status == "verified", o.status
        assert o.error_code == "", o.error_code
        assert o.fn_name == "sp_ref_ok_387", o.fn_name
        s = result.summary
        assert (s.tier1_verified, s.tier3_runtime, s.total) == (3, 0, 3), (
            s.tier1_verified, s.tier3_runtime, s.total)

    def test_refined_vs_nat_subpattern_kind_discriminates(self) -> None:
        """A refined sub-pattern records ``refine_bind``/E505, a bare-@Nat one
        records ``nat_bind``/E503 — pins the kind/code routing in
        ``_obligate_subpattern_narrowings`` (refined-first branch vs nat
        branch).  A mutation collapsing the refined branch would re-route the
        @Pos387 narrowing through the nat path (wrong kind + wrong code)."""
        result = _verify("""
type Pos387 = { @Int | @Int.0 > 0 };
private fn route_ref_387(@Option<Int> -> @Int)
  requires(true) ensures(true) effects(pure)
{ match @Option<Int>.0 { Some(@Pos387) -> @Pos387.0, None -> 1 } }
private fn route_nat_387(@Option<Int> -> @Nat)
  requires(true) ensures(true) effects(pure)
{ match @Option<Int>.0 { Some(@Nat) -> @Nat.0, None -> 0 } }
""")
        by_fn = {o.fn_name: o for o in result.obligations
                 if o.kind in ("nat_bind", "refine_bind")}
        assert by_fn["route_ref_387"].kind == "refine_bind", by_fn
        assert by_fn["route_ref_387"].error_code == "E505", by_fn
        assert by_fn["route_nat_387"].kind == "nat_bind", by_fn
        assert by_fn["route_nat_387"].error_code == "E503", by_fn

    # =================================================================
    # _obligate_subpattern_term  (3697-3755) — nested ctor patterns
    # Some(Some(@Nat)) on Option<Option<Int>>
    # =================================================================

    def test_nested_subpattern_violated_is_obligated(self) -> None:
        """``Some(Some(@Nat))`` on ``Option<Option<Int>>``: the INNER @Int->@Nat
        narrowing must be obligated (E503) — pins the recursion in
        ``_obligate_subpattern_narrowings`` → ``_obligate_subpattern_term``.
        Drop the recursion and this becomes an unguarded false Tier-1 (NO
        obligation at all)."""
        result = _verify("""
private fn nested_neg_387(@Option<Option<Int>> -> @Nat)
  requires(true) ensures(true) effects(pure)
{ match @Option<Option<Int>>.0 {
    Some(Some(@Nat)) -> @Nat.0, Some(None) -> 0, None -> 0 } }
""")
        binds = [o for o in result.obligations if o.kind == "nat_bind"]
        assert len(binds) == 1, [(o.kind, o.status) for o in result.obligations]
        o = binds[0]
        assert o.status == "violated", o.status
        assert o.error_code == "E503", o.error_code
        assert o.fn_name == "nested_neg_387", o.fn_name
        assert o.counterexample, o.counterexample

    def test_nested_subpattern_verified_carries_source_fact(self) -> None:
        """``Some(Some(@Nat))`` on ``Option<Option<Pos387>>``: the inner source
        is ``> 0`` hence ``>= 0``, so the nested narrowing VERIFIES — pins both
        the recursion AND the recursive ``_subpattern_source_facts_term`` carry
        of the inner field's source fact through the nesting."""
        result = _verify("""
type Pos387 = { @Int | @Int.0 > 0 };
private fn nested_ok_387(@Option<Option<Pos387>> -> @Nat)
  requires(true) ensures(true) effects(pure)
{ match @Option<Option<Pos387>>.0 {
    Some(Some(@Nat)) -> @Nat.0, Some(None) -> 0, None -> 0 } }
""")
        assert [d for d in result.diagnostics if d.severity == "error"] == [], [
            d.description for d in result.diagnostics if d.severity == "error"]
        binds = [o for o in result.obligations if o.kind == "nat_bind"]
        assert len(binds) == 1, [(o.kind, o.status) for o in result.obligations]
        o = binds[0]
        assert o.status == "verified", o.status
        assert o.fn_name == "nested_ok_387", o.fn_name
        assert o.error_code == "", o.error_code

    def test_nested_refined_subpattern_violated(self) -> None:
        """``Some(Some(@Pos387))`` on ``Option<Option<Int>>`` → E505 via the
        nested-recursion refined branch of ``_obligate_subpattern_term``."""
        result = _verify("""
type Pos387 = { @Int | @Int.0 > 0 };
private fn nested_ref_neg_387(@Option<Option<Int>> -> @Int)
  requires(true) ensures(true) effects(pure)
{ match @Option<Option<Int>>.0 {
    Some(Some(@Pos387)) -> @Pos387.0, Some(None) -> 1, None -> 1 } }
""")
        binds = [o for o in result.obligations if o.kind == "refine_bind"]
        assert len(binds) == 1, [(o.kind, o.status) for o in result.obligations]
        o = binds[0]
        assert o.status == "violated", o.status
        assert o.error_code == "E505", o.error_code
        assert o.fn_name == "nested_ref_neg_387", o.fn_name
        assert o.counterexample, o.counterexample

    # =================================================================
    # _obligate_destructure_narrowings  (3901-3995)
    # =================================================================

    def test_destructure_projectable_violated_two_components(self) -> None:
        """``let Tuple<@Nat,@Nat> = Tuple(@Int.0, @Int.1)`` — a literal tuple
        RHS the SMT layer projects.  Both components narrow @Int->@Nat and both
        VIOLATE (E503) via the projectable ``for i in nat_narrowing`` loop.
        Pins: 2 obligations (a ``+= 2``→``+= 1`` loop mutation drops one), each
        violated/E503/fn_name."""
        result = _verify("""
private fn dest_neg_387(@Int, @Int -> @Nat)
  requires(true) ensures(true) effects(pure)
{
  let Tuple<@Nat, @Nat> = Tuple(@Int.0, @Int.1);
  @Nat.0 + @Nat.1
}
""")
        binds = [o for o in result.obligations if o.kind == "nat_bind"]
        assert len(binds) == 2, [(o.kind, o.status) for o in result.obligations]
        assert all(o.status == "violated" for o in binds), [
            o.status for o in binds]
        assert all(o.error_code == "E503" for o in binds), [
            o.error_code for o in binds]
        assert all(o.fn_name == "dest_neg_387" for o in binds), [
            o.fn_name for o in binds]
        assert all(o.counterexample for o in binds), binds
        errs = [d for d in result.diagnostics if d.error_code == "E503"]
        assert len(errs) == 2, [d.description for d in result.diagnostics]
        assert all("tuple destructure" in d.description for d in errs), [
            d.description for d in errs]

    def test_destructure_refined_projectable_violated(self) -> None:
        """``let Tuple<@Pos387,@Pos387> = Tuple(@Int.0, @Int.1)`` → 2× E505 via
        the projectable ``for i, target in refined_narrowing`` loop."""
        result = _verify("""
type Pos387 = { @Int | @Int.0 > 0 };
private fn dest_ref_neg_387(@Int, @Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let Tuple<@Pos387, @Pos387> = Tuple(@Int.0, @Int.1);
  @Pos387.0 + @Pos387.1
}
""")
        binds = [o for o in result.obligations if o.kind == "refine_bind"]
        assert len(binds) == 2, [(o.kind, o.status) for o in result.obligations]
        assert all(o.status == "violated" for o in binds), [
            o.status for o in binds]
        assert all(o.error_code == "E505" for o in binds), [
            o.error_code for o in binds]
        assert all(o.fn_name == "dest_ref_neg_387" for o in binds), [
            o.fn_name for o in binds]

    def test_destructure_asymmetric_projection_index_soundness(self) -> None:
        """SOUNDNESS — the De Bruijn projection index.  An asymmetric tuple
        ``Tuple<@Nat, @Int>`` from ``Tuple(@Pos387.0, @Int.0)``: only component
        0 narrows (into @Nat), and it VERIFIES because component 0's source
        ``@Pos387`` is ``> 0``.  If the accessor index ``(idx, 0)`` were mutated
        to ``(idx, 1)`` it would project the unconstrained ``@Int`` component
        and the obligation would VIOLATE; an off-by-one the other way would
        mis-source the fact.  Exactly ONE nat_bind, verified."""
        result = _verify("""
type Pos387 = { @Int | @Int.0 > 0 };
private fn dest_asym_387(@Pos387, @Int -> @Nat)
  requires(true) ensures(true) effects(pure)
{
  let Tuple<@Nat, @Int> = Tuple(@Pos387.0, @Int.0);
  @Nat.0
}
""")
        assert [d for d in result.diagnostics if d.severity == "error"] == [], [
            d.description for d in result.diagnostics if d.severity == "error"]
        binds = [o for o in result.obligations if o.kind == "nat_bind"]
        assert len(binds) == 1, [(o.kind, o.status) for o in result.obligations]
        o = binds[0]
        assert o.status == "verified", o.status
        assert o.error_code == "", o.error_code
        assert o.fn_name == "dest_asym_387", o.fn_name

    def test_destructure_unprojectable_guarded_tier3(self) -> None:
        """``let Tuple<@Nat,@Nat> = mk()`` where ``mk`` returns ``Tuple<Int,Int>``
        via a CALL (opaque return the SMT layer can't project as a datatype) →
        the ``sort is None`` branch: 2 GUARDED Tier-3 nat_bind obligations
        (codegen runtime-guards the destructure).  Pins ``tier3``/``tier3_runtime
        += 1`` ×2 and that they are NOT errors."""
        result = _verify("""
private fn mk_387(@Unit -> @Tuple<Int, Int>)
  requires(true) ensures(true) effects(pure)
{ Tuple(1, 2) }
private fn dest_t3_387(@Unit -> @Nat)
  requires(true) ensures(true) effects(pure)
{
  let Tuple<@Nat, @Nat> = mk_387(());
  @Nat.0 + @Nat.1
}
""")
        assert [d for d in result.diagnostics if d.severity == "error"] == [], [
            d.description for d in result.diagnostics if d.severity == "error"]
        binds = [o for o in result.obligations
                 if o.kind == "nat_bind" and o.fn_name == "dest_t3_387"]
        assert len(binds) == 2, [(o.kind, o.status) for o in result.obligations]
        assert all(o.status == "tier3" for o in binds), [
            o.status for o in binds]
        # tier3_runtime starts at 0, so 2 guarded sites pin `+= 1` (vs `= 1`).
        assert result.summary.tier3_runtime == 2, result.summary.tier3_runtime

    def test_destructure_no_narrowing_no_obligation(self) -> None:
        """``let Tuple<@Int,@Int> = Tuple(...)`` — neither component narrows
        (target @Int == source @Int), so NO nat_bind/refine_bind obligation
        fires.  Pins the ``not _is_nat_type(target)`` / narrowing guard: a
        mutation that obligates a non-narrowing component would emit a bogus
        E503 here."""
        result = _verify("""
private fn dest_none_387(@Int, @Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let Tuple<@Int, @Int> = Tuple(@Int.0, @Int.1);
  @Int.0 + @Int.1
}
""")
        proj = [o for o in result.obligations
                if o.kind in ("nat_bind", "refine_bind")]
        assert proj == [], [(o.kind, o.status) for o in proj]

    # --- _obligate_subpattern_narrowings: opaque (unprojectable) scrutinee ---
    # A `match f() { Some(@Nat) -> ... }` whose scrutinee is a function-call
    # return: the SMT layer can't project it as a datatype (sort/idx is None),
    # so the narrowing falls to the opaque tail branch rather than a term check.

    def test_opaque_nat_subpattern_guarded_tier3(self) -> None:
        """Opaque scrutinee (call return) ``Some(@Nat)`` on ``Option<Int>`` →
        the unprojectable nat tail (3887-3898): a GUARDED Tier-3 nat_bind
        (codegen guards the sub-pattern bind at run time).  Pins ``tier3`` +
        ``tier3_runtime`` and that it is NOT an error."""
        result = _verify("""
private fn srcopt_387(@Unit -> @Option<Int>)
  requires(true) ensures(true) effects(pure)
{ Some(1) }
private fn sp_opaque_nat_387(@Unit -> @Nat)
  requires(true) ensures(true) effects(pure)
{ match srcopt_387(()) { Some(@Nat) -> @Nat.0, None -> 0 } }
""")
        assert [d for d in result.diagnostics if d.severity == "error"] == [], [
            d.description for d in result.diagnostics if d.severity == "error"]
        binds = [o for o in result.obligations
                 if o.kind == "nat_bind" and o.fn_name == "sp_opaque_nat_387"]
        assert len(binds) == 1, [(o.kind, o.status) for o in result.obligations]
        o = binds[0]
        assert o.status == "tier3", o.status
        assert result.summary.tier3_runtime == 1, result.summary.tier3_runtime

    def test_opaque_refined_subpattern_unguarded_tier3(self) -> None:
        """Opaque scrutinee ``Some(@Pos387)`` on ``Option<Int>`` → the
        unprojectable refined tail (3864-3870): an UNGUARDED Tier-3 refine_bind
        (E506 warning, ``tier3_unguarded``, excluded from totals — refined
        narrowings have no codegen runtime guard).  Distinguishes the
        ``guarded=False`` refined opaque path from the ``guarded=True`` nat one:
        a mutation flipping the flag would mis-claim a runtime guard."""
        result = _verify("""
type Pos387 = { @Int | @Int.0 > 0 };
private fn srcopt2_387(@Unit -> @Option<Int>)
  requires(true) ensures(true) effects(pure)
{ Some(1) }
private fn sp_opaque_ref_387(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ match srcopt2_387(()) { Some(@Pos387) -> @Pos387.0, None -> 1 } }
""")
        assert [d for d in result.diagnostics if d.severity == "error"] == [], [
            d.description for d in result.diagnostics if d.severity == "error"]
        binds = [o for o in result.obligations
                 if o.kind == "refine_bind" and o.fn_name == "sp_opaque_ref_387"]
        assert len(binds) == 1, [(o.kind, o.status) for o in result.obligations]
        o = binds[0]
        assert o.status == "tier3_unguarded", o.status
        assert o.error_code == "E506", o.error_code
        warns = [d for d in result.diagnostics if d.error_code == "E506"]
        assert len(warns) == 1, [d.description for d in result.diagnostics]
        # Unguarded refined Tier-3 does NOT increment tier3_runtime (R7).
        assert result.summary.tier3_runtime == 0, result.summary.tier3_runtime


class TestVerifierGates387:
    """#387: pin the verifier's *soundness-gate* predicates and the
    generic-instantiation aggregation/meet logic — the code that decides
    WHETHER an obligation fires, and how per-instantiation verdicts collapse.

    These are the highest-value mutation targets: a wrong boolean from a typing
    predicate silently skips (or spuriously fires) a `value >= 0` / refinement
    obligation, and a wrong meet folds a reachable counterexample into a false
    Tier-1.  Each test is a DIFFERENTIAL — the predicate's wrong answer changes
    the obligation SET (a `nat_sub`/`nat_bind`/`refine_bind` appears or
    vanishes), its KIND/CODE, or its STATUS.

    Observable surface (per the #387 convention): `ProofObligation` fields via
    `==` (mutmut wraps string literals as ``"XX"+s+"XX"`` so substring ``in``
    does NOT kill a string mutation — kinds/codes/statuses/fn_name use ``==``)
    and exact tuples on `result.summary`.  Distinct ``_387`` fn names catch a
    ``fn_name → None`` mutation; inputs are chosen so the right answer can't
    coincide with a fallback default.
    """

    @staticmethod
    def _subs(result: VerifyResult) -> list:
        return [o for o in result.obligations if o.kind == "nat_sub"]

    @staticmethod
    def _binds(result: VerifyResult) -> list:
        return [o for o in result.obligations if o.kind == "nat_bind"]

    @staticmethod
    def _refbinds(result: VerifyResult) -> list:
        return [o for o in result.obligations if o.kind == "refine_bind"]

    # =================================================================
    # _is_nat_typed / _has_nat_origin  (4402-4543)
    # Gate the #520 `@Nat - @Nat` underflow obligation (kind nat_sub,
    # E502) at _walk_for_primitive_op_obligations:2097-2101.  The
    # obligation fires iff op==SUB AND both operands _is_nat_typed AND
    # (either _has_nat_origin).  A wrong boolean flips the obligation's
    # EXISTENCE — the cleanest differential.
    # =================================================================

    def test_nat_slot_subtraction_is_obligated(self) -> None:
        """``@Nat.0 - @Nat.1`` (both SlotRefs, @Nat-typed + @Nat-origin) →
        exactly one ``nat_sub`` E502 (unguarded → violated, with CE).  Pins the
        baseline gate: ``_is_nat_typed(SlotRef)`` / ``_has_nat_origin(SlotRef)``
        both keyed on ``type_name == "Nat"`` (line 4431/4494).  A mutation
        flipping either SlotRef branch drops the obligation (false Tier-1)."""
        result = _verify("""
private fn slotsub_neg_387(@Nat, @Nat -> @Nat)
  requires(true) ensures(true) effects(pure)
{ @Nat.0 - @Nat.1 }
""")
        subs = self._subs(result)
        assert len(subs) == 1, [(o.kind, o.status) for o in result.obligations]
        o = subs[0]
        assert o.kind == "nat_sub", o.kind
        assert o.status == "violated", o.status
        assert o.error_code == "E502", o.error_code
        assert o.fn_name == "slotsub_neg_387", o.fn_name
        assert o.counterexample, o.counterexample

    def test_int_slot_subtraction_not_obligated(self) -> None:
        """``@Int.0 - @Int.1 → @Int`` carries NO ``nat_sub`` — the negative
        partner of the gate.  ``_is_nat_typed(@Int.0)`` must be False (its
        ``type_name`` is ``Int`` not ``Nat``), so the ``and`` at 2098-2099
        short-circuits.  A mutation making ``_is_nat_typed`` return True for an
        @Int SlotRef would spuriously fire E502 on well-defined signed
        arithmetic."""
        result = _verify("""
private fn intsub_387(@Int, @Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 - @Int.1 }
""")
        assert self._subs(result) == [], [
            (o.kind, o.status) for o in result.obligations]
        assert [d for d in result.diagnostics if d.severity == "error"] == [], [
            d.error_code for d in result.diagnostics if d.severity == "error"]

    def test_pure_literal_subtraction_origin_gate_skips(self) -> None:
        """``0 - 1`` consumed at @Int: both operands are @Nat-TYPED (non-negative
        IntLits, ``_is_nat_typed`` line 4434 ``value >= 0``) but NEITHER has
        @Nat *origin* (``_has_nat_origin`` returns False for IntLit — it has no
        IntLit branch), so the ``(_has_nat_origin OR _has_nat_origin)`` conjunct
        at 2100-2101 is False and NO obligation fires.  This is the #520
        deliberate pure-literal exemption: a mutation deleting the origin
        conjunct would spuriously E502 every ``0 - 1`` sentinel in the
        corpus."""
        result = _verify("""
private fn litsub_387(@Unit -> @Int)
  requires(true) ensures(@Int.result < 0) effects(pure)
{ 0 - 1 }
""")
        assert self._subs(result) == [], [
            (o.kind, o.status) for o in result.obligations]
        assert [d for d in result.diagnostics if d.severity == "error"] == [], [
            d.error_code for d in result.diagnostics if d.severity == "error"]

    def test_literal_minus_natslot_origin_or_branch(self) -> None:
        """``0 - @Nat.0``: left IntLit has no @Nat origin, right SlotRef does.
        The gate fires only because ``_has_nat_origin`` uses ``left OR right``
        (line 4528-4529).  A mutation ``or → and`` makes ``(False and True) =
        False`` and the obligation vanishes — so this pins the OR specifically,
        not just "some operand has origin".  Unguarded → violated E502 with a
        CE (``@Nat.0 = 1`` gives ``-1``)."""
        result = _verify("""
private fn litnat_387(@Nat -> @Nat)
  requires(true) ensures(true) effects(pure)
{ 0 - @Nat.0 }
""")
        subs = self._subs(result)
        assert len(subs) == 1, [(o.kind, o.status) for o in result.obligations]
        o = subs[0]
        assert o.status == "violated", o.status
        assert o.error_code == "E502", o.error_code
        assert o.fn_name == "litnat_387", o.fn_name
        assert o.counterexample, o.counterexample

    def test_natslot_minus_literal_origin_or_left(self) -> None:
        """``@Nat.0 - 1``: left SlotRef has @Nat origin, right IntLit does not.
        The mirror of the previous test — pins the LEFT disjunct of the OR.
        Guarded by ``@Nat.0 >= 1`` so it verifies, isolating the gate's
        existence (one ``nat_sub``, verified) from the discharge."""
        result = _verify("""
private fn natlit_387(@Nat -> @Nat)
  requires(@Nat.0 >= 1) ensures(true) effects(pure)
{ @Nat.0 - 1 }
""")
        subs = self._subs(result)
        assert len(subs) == 1, [(o.kind, o.status) for o in result.obligations]
        o = subs[0]
        assert o.status == "verified", o.status
        assert o.error_code == "", o.error_code
        assert o.fn_name == "natlit_387", o.fn_name
        assert o.counterexample is None, o.counterexample

    def test_is_nat_typed_recurses_arithmetic_operand(self) -> None:
        """``(@Nat.0 + @Nat.1) - @Nat.0``: the LEFT operand of the SUB is itself
        a BinaryExpr.  The gate fires only if ``_is_nat_typed`` RECURSES into
        the ADD (line 4443-4444, ``left AND right``) and reports @Nat.  Drop the
        BinaryExpr recursion (return False) and the SUB's left operand reads as
        non-@Nat, killing the obligation.  Guarded (sum >= @Nat.0 always) →
        verified."""
        result = _verify("""
private fn natarith_387(@Nat, @Nat -> @Nat)
  requires(true) ensures(true) effects(pure)
{ (@Nat.0 + @Nat.1) - @Nat.0 }
""")
        subs = self._subs(result)
        assert len(subs) == 1, [(o.kind, o.status) for o in result.obligations]
        assert subs[0].status == "verified", subs[0].status
        assert subs[0].fn_name == "natarith_387", subs[0].fn_name

    def test_is_nat_typed_int_addend_blocks_obligation(self) -> None:
        """``(@Nat.0 + @Int.0) - @Nat.1 → @Int``: the ADD has an @Int operand so
        is @Int-typed, the SUB result is @Int, and NO ``nat_sub`` fires.  Pins
        the ``and`` in ``_is_nat_typed``'s BinaryExpr branch (4443-4444): a
        mutation ``and → or`` would call the mixed ADD @Nat-typed, then
        spuriously obligate the @Int subtraction."""
        result = _verify("""
private fn mixedarith_387(@Nat, @Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ (@Nat.0 + @Int.0) - @Nat.1 }
""")
        assert self._subs(result) == [], [
            (o.kind, o.status) for o in result.obligations]
        assert [d for d in result.diagnostics if d.severity == "error"] == [], [
            d.error_code for d in result.diagnostics if d.severity == "error"]

    def test_is_nat_typed_recurses_block_tail(self) -> None:
        """``{ @Nat.0 - @Nat.1 }`` as the function body: the SUB sits inside a
        Block.  Pins ``_is_nat_typed``'s Block branch (4451-4452, recurse on
        ``expr.expr``) AND the walker's Block recursion — the obligation fires
        only if both descend.  Unguarded → violated E502."""
        result = _verify("""
private fn blocksub_387(@Nat, @Nat -> @Nat)
  requires(true) ensures(true) effects(pure)
{ { @Nat.0 - @Nat.1 } }
""")
        subs = self._subs(result)
        assert len(subs) == 1, [(o.kind, o.status) for o in result.obligations]
        assert subs[0].status == "violated", subs[0].status
        assert subs[0].error_code == "E502", subs[0].error_code

    def test_has_nat_origin_recurses_index_element(self) -> None:
        """``arr[0] - arr[1]`` on ``@Array<Nat>`` (length >= 2): array indexing
        carries @Nat provenance only because ``_has_nat_origin``'s IndexExpr
        branch (4518-4526) consults the resolved ELEMENT type — it cannot
        recurse on the ``@Array`` operand, which is not itself @Nat.  Drop that
        branch and the underflow is silently skipped (CR #756).  Both indices
        in-bounds → the obligation is the genuine value comparison (violated:
        ``arr[0] < arr[1]`` is possible)."""
        result = _verify("""
public fn arrsub_387(@Array<Nat> -> @Nat)
  requires(array_length(@Array<Nat>.0) >= 2)
  ensures(true) effects(pure)
{ @Array<Nat>.0[0] - @Array<Nat>.0[1] }
""")
        subs = self._subs(result)
        assert len(subs) == 1, [(o.kind, o.status) for o in result.obligations]
        assert subs[0].status == "violated", subs[0].status
        assert subs[0].error_code == "E502", subs[0].error_code
        assert subs[0].fn_name == "arrsub_387", subs[0].fn_name

    # =================================================================
    # _narrows_into_nat / _has_underflow_leaf  (4545-4598)
    # Gate the #552 binding-site `value >= 0` obligation (kind
    # nat_bind, E503).  _narrows_into_nat = (NOT _is_nat_typed(v))
    # OR _has_underflow_leaf(v).  Differential: nat_bind appears or
    # vanishes.
    # =================================================================

    def test_int_narrow_into_nat_let_is_obligated(self) -> None:
        """``let @Nat = @Int.0``: value is NOT @Nat-typed, so
        ``_narrows_into_nat`` returns True via its FIRST clause
        (``not _is_nat_typed``, 4564-4565) → one ``nat_bind`` E503 (unguarded →
        violated, CE).  A mutation negating that clause drops the narrowing
        check entirely (false Tier-1 on every @Int→@Nat bind)."""
        result = _verify("""
private fn letnarrow_387(@Int -> @Nat)
  requires(true) ensures(true) effects(pure)
{ let @Nat = @Int.0; @Nat.0 }
""")
        binds = self._binds(result)
        assert len(binds) == 1, [(o.kind, o.status) for o in result.obligations]
        o = binds[0]
        assert o.kind == "nat_bind", o.kind
        assert o.status == "violated", o.status
        assert o.error_code == "E503", o.error_code
        assert o.fn_name == "letnarrow_387", o.fn_name
        assert o.counterexample, o.counterexample

    def test_nat_narrow_into_nat_let_not_obligated(self) -> None:
        """``let @Nat = @Nat.0``: value IS @Nat-typed AND has no underflow leaf,
        so ``_narrows_into_nat`` returns False — NO ``nat_bind``.  The negative
        partner: a mutation forcing ``_narrows_into_nat`` True (e.g. dropping
        the ``_is_nat_typed`` guard) would spuriously E503 a Nat→Nat bind."""
        result = _verify("""
private fn natbind_387(@Nat -> @Nat)
  requires(true) ensures(true) effects(pure)
{ let @Nat = @Nat.0; @Nat.0 }
""")
        assert self._binds(result) == [], [
            (o.kind, o.status) for o in result.obligations]
        assert [d for d in result.diagnostics if d.severity == "error"] == [], [
            d.error_code for d in result.diagnostics if d.severity == "error"]

    def test_underflow_leaf_pure_literal_sub_into_nat(self) -> None:
        """``let @Nat = 0 - 1``: the value is @Nat-TYPED (both literals
        non-negative) yet can be negative.  Only ``_has_underflow_leaf`` (the
        SECOND clause of ``_narrows_into_nat``, 4566) catches it: it sees a SUB
        with no @Nat origin (4583-4585) and returns True → one ``nat_bind`` E503
        violated.  Drop ``_has_underflow_leaf`` and this @Nat-typed-but-negative
        bind escapes (the exact #520→#552 hand-off, false Tier-1)."""
        result = _verify("""
private fn ufl_let_387(@Unit -> @Nat)
  requires(true) ensures(true) effects(pure)
{ let @Nat = 0 - 1; @Nat.0 }
""")
        binds = self._binds(result)
        assert len(binds) == 1, [(o.kind, o.status) for o in result.obligations]
        o = binds[0]
        assert o.status == "violated", o.status
        assert o.error_code == "E503", o.error_code
        assert o.fn_name == "ufl_let_387", o.fn_name
        assert o.counterexample, o.counterexample
        # No `nat_sub` co-fires: the SUB has no @Nat origin (#520 exempt),
        # so #552 owns this site exclusively.
        assert self._subs(result) == [], [
            (o.kind, o.status) for o in result.obligations]

    def test_no_underflow_leaf_nonneg_addition_into_nat(self) -> None:
        """``let @Nat = 1 + 2``: @Nat-typed with NO subtraction anywhere, so
        ``_has_underflow_leaf`` returns False and ``_narrows_into_nat`` is False
        — NO obligation.  Pins the SUB-specific guard in ``_has_underflow_leaf``
        (4583): a mutation that returns True for a non-SUB BinaryExpr would
        spuriously E503 a constant addition."""
        result = _verify("""
private fn noleaf_387(@Unit -> @Nat)
  requires(true) ensures(true) effects(pure)
{ let @Nat = 1 + 2; @Nat.0 }
""")
        assert self._binds(result) == [], [
            (o.kind, o.status) for o in result.obligations]
        assert [d for d in result.diagnostics if d.severity == "error"] == [], [
            d.error_code for d in result.diagnostics if d.severity == "error"]

    def test_underflow_leaf_recurses_block(self) -> None:
        """``let @Nat = { 0 - 1 }``: the underflowing SUB is wrapped in a Block.
        Pins ``_has_underflow_leaf``'s Block branch (4588-4589, recurse on
        ``value.expr``) — drop it and the wrapped pure-literal underflow is no
        longer caught.  One ``nat_bind`` E503 violated."""
        result = _verify("""
private fn ufl_block_387(@Unit -> @Nat)
  requires(true) ensures(true) effects(pure)
{ let @Nat = { 0 - 1 }; @Nat.0 }
""")
        binds = self._binds(result)
        assert len(binds) == 1, [(o.kind, o.status) for o in result.obligations]
        assert binds[0].status == "violated", binds[0].status
        assert binds[0].error_code == "E503", binds[0].error_code

    def test_underflow_leaf_recurses_if_branch(self) -> None:
        """``let @Nat = if c then { 5 } else { 0 - 1 }``: the underflow lives in
        the ELSE branch.  Pins ``_has_underflow_leaf``'s IfExpr branch
        (4590-4594, ``then OR else``) — the value is @Nat-typed (both branches
        @Nat) but the else can be negative.  One ``nat_bind`` E503 violated;
        drop the IfExpr recursion (or its else disjunct) and it escapes."""
        result = _verify("""
private fn ufl_if_387(@Bool -> @Nat)
  requires(true) ensures(true) effects(pure)
{ let @Nat = if @Bool.0 then { 5 } else { 0 - 1 }; @Nat.0 }
""")
        binds = self._binds(result)
        assert len(binds) == 1, [(o.kind, o.status) for o in result.obligations]
        assert binds[0].status == "violated", binds[0].status
        assert binds[0].error_code == "E503", binds[0].error_code
        assert binds[0].fn_name == "ufl_if_387", binds[0].fn_name

    # =================================================================
    # _narrows_into_refined  (4600-4637)
    # Gate the #746 refinement binding obligation (kind refine_bind,
    # E505).  Fires unless the source already carries the target's
    # EXACT (base AND predicate) refinement (the R3 exemption).
    # =================================================================

    def test_int_narrow_into_refined_is_obligated(self) -> None:
        """``let @Pos387 = @Int.0`` (``@Pos387 = {@Int | @Int.0 > 0}``): the
        source is bare @Int with no refinement, so ``_narrows_into_refined``
        returns True (no source_parts match) → one ``refine_bind`` E505
        (violated: @Int.0 may be <= 0, CE).  The baseline refinement gate."""
        result = _verify("""
type Pos387 = { @Int | @Int.0 > 0 };
private fn refnarrow_387(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ let @Pos387 = @Int.0; @Pos387.0 }
""")
        binds = self._refbinds(result)
        assert len(binds) == 1, [(o.kind, o.status) for o in result.obligations]
        o = binds[0]
        assert o.kind == "refine_bind", o.kind
        assert o.status == "violated", o.status
        assert o.error_code == "E505", o.error_code
        assert o.fn_name == "refnarrow_387", o.fn_name
        assert o.counterexample, o.counterexample

    def test_same_refinement_bind_is_r3_exempt(self) -> None:
        """``let @Pos387 = @Pos387.0``: source and target share base AND
        predicate, so the R3 exemption (4633-4636) returns False — NO
        ``refine_bind``.  The negative partner: a mutation deleting the R3
        early-return (always obligate) would E505 an already-discharged
        refinement, a false positive on sound code."""
        result = _verify("""
type Pos387 = { @Int | @Int.0 > 0 };
private fn refexempt_387(@Pos387 -> @Int)
  requires(true) ensures(true) effects(pure)
{ let @Pos387 = @Pos387.0; @Pos387.0 }
""")
        assert self._refbinds(result) == [], [
            (o.kind, o.status) for o in result.obligations]
        assert [d for d in result.diagnostics if d.severity == "error"] == [], [
            d.error_code for d in result.diagnostics if d.severity == "error"]

    def test_different_predicate_not_r3_exempt(self) -> None:
        """``let @Pos387 = @Gt5_387.0`` (source ``> 5``, target ``> 0``): the
        bases match (both @Int) but the PREDICATES differ, so the R3 exemption
        does NOT apply — the obligation fires and is DISCHARGED (``> 5`` implies
        ``> 0``) → one ``refine_bind`` VERIFIED.  Pins the predicate half of the
        R3 ``and`` (4634): a mutation matching on base alone would wrongly exempt
        this and the obligation would vanish (status flips to absent)."""
        result = _verify("""
type Gt5_387 = { @Int | @Int.0 > 5 };
type Pos387 = { @Int | @Int.0 > 0 };
private fn refdiff_387(@Gt5_387 -> @Int)
  requires(true) ensures(true) effects(pure)
{ let @Pos387 = @Gt5_387.0; @Pos387.0 }
""")
        binds = self._refbinds(result)
        assert len(binds) == 1, [(o.kind, o.status) for o in result.obligations]
        o = binds[0]
        assert o.status == "verified", o.status
        assert o.error_code == "", o.error_code
        assert o.fn_name == "refdiff_387", o.fn_name

    # =================================================================
    # _check_generic_refined_return  (3387-3493)
    # Discharge a CONCRETE refined return on an UNINSTANTIATED generic
    # (forall<T>).  Reached via the uninstantiated-generic branch of
    # _verify_fn (1234-1238).  kind refine_bind, E505.
    # =================================================================

    def test_generic_refined_return_violated(self) -> None:
        """Uninstantiated ``forall<T> fn g(@T -> @Pos387) { 0 }``: the concrete
        refined return is T-independent, discharged at Tier 1, and ``0`` violates
        ``> 0`` → one ``refine_bind`` E505 violated (CE).  Pins the violated
        branch (3480-3489): kind/code/CE and the ``total -= 1`` (the error is not
        a counted verdict, so total = requires + ensures = 2)."""
        result = _verify("""
type Pos387 = { @Int | @Int.0 > 0 };
private forall<T>
fn gret_bad_387(@T -> @Pos387)
  requires(true) ensures(true) effects(pure)
{ 0 }
""")
        binds = self._refbinds(result)
        assert len(binds) == 1, [(o.kind, o.status) for o in result.obligations]
        o = binds[0]
        assert o.kind == "refine_bind", o.kind
        assert o.status == "violated", o.status
        assert o.error_code == "E505", o.error_code
        assert o.fn_name == "gret_bad_387", o.fn_name
        assert o.counterexample, o.counterexample
        s = result.summary
        assert (s.tier1_verified, s.tier3_runtime, s.total) == (2, 0, 2), (
            s.tier1_verified, s.tier3_runtime, s.total)

    def test_generic_refined_return_verified(self) -> None:
        """Uninstantiated ``forall<T> fn g(@T -> @Pos387) { 5 }``: ``5`` proves
        ``> 0`` → one ``refine_bind`` VERIFIED.  Pins the verified branch
        (3476-3479): status ``verified``, empty code, no CE, and the
        ``tier1_verified += 1`` + ``total += 1`` (total = requires + refine_bind
        + ensures = 3).  Together with the violated test this brackets the
        check_valid verdict routing."""
        result = _verify("""
type Pos387 = { @Int | @Int.0 > 0 };
private forall<T>
fn gret_ok_387(@T -> @Pos387)
  requires(true) ensures(true) effects(pure)
{ 5 }
""")
        assert [d for d in result.diagnostics if d.severity == "error"] == [], [
            d.description for d in result.diagnostics if d.severity == "error"]
        binds = self._refbinds(result)
        assert len(binds) == 1, [(o.kind, o.status) for o in result.obligations]
        o = binds[0]
        assert o.status == "verified", o.status
        assert o.error_code == "", o.error_code
        assert o.fn_name == "gret_ok_387", o.fn_name
        assert o.counterexample is None, o.counterexample
        s = result.summary
        assert (s.tier1_verified, s.tier3_runtime, s.total) == (3, 0, 3), (
            s.tier1_verified, s.tier3_runtime, s.total)

    # =================================================================
    # _aggregate_generic_instances / _emit_aggregated_diagnostic
    # (1002-1162)  — collapse per-instantiation obligations at one
    # source site to a single met obligation (#732).  Reached by a
    # forall<T> instantiated at >=2 concrete types.
    # =================================================================

    def test_generic_instances_aggregate_violated_to_one(self) -> None:
        """``forall<T> fn g(@T,@Nat,@Nat -> @Nat) { @Nat.0 - @Nat.1 }``
        instantiated at Int AND Bool: the unguarded SUB violates in BOTH
        instantiations, but ``_aggregate_generic_instances`` collapses the two
        per-instance obligations at the one source site to a SINGLE met
        obligation.  Pins the de-dup (exactly one ``nat_sub``, not two) and the
        ``violated`` meet; ``_emit_aggregated_diagnostic`` produces ONE E502."""
        result = _verify("""
private forall<T>
fn gsub_bad_387(@T, @Nat, @Nat -> @Nat)
  requires(true) ensures(true) effects(pure)
{ @Nat.0 - @Nat.1 }

public fn use_int_bad_387(@Int -> @Nat)
  requires(true) ensures(true) effects(pure)
{ gsub_bad_387(@Int.0, 3, 1) }

public fn use_bool_bad_387(@Bool -> @Nat)
  requires(true) ensures(true) effects(pure)
{ gsub_bad_387(@Bool.0, 5, 2) }
""")
        subs = [o for o in result.obligations
                if o.kind == "nat_sub" and o.fn_name == "gsub_bad_387"]
        assert len(subs) == 1, [(o.kind, o.fn_name, o.status)
                                for o in result.obligations]
        assert subs[0].status == "violated", subs[0].status
        errs = [d for d in result.diagnostics if d.error_code == "E502"]
        assert len(errs) == 1, [d.description for d in result.diagnostics]
        # The aggregated diagnostic names the generic and BOTH instantiations
        # (sorted): pins _emit_aggregated_diagnostic's prefix + label set.
        d = errs[0]
        assert d.description.startswith(
            "In generic function 'gsub_bad_387' instantiated at "
            "gsub_bad_387<Bool>, gsub_bad_387<Int>: "), d.description

    def test_generic_instances_aggregate_verified_counts_once(self) -> None:
        """Same generic but GUARDED (``requires(@Nat.0 >= @Nat.1)``): the SUB
        verifies in both instantiations and the meet is ``verified`` → exactly
        one ``nat_sub`` verified, NO diagnostic.  Pins the verified branch of
        ``_aggregate_generic_instances`` (1065-1067: ``tier1_verified += 1`` and
        ``total += 1`` ONCE, not per-instance).  The negative partner to the
        violated aggregation — together they pin the meet's two extreme
        verdicts feeding the summary."""
        result = _verify("""
private forall<T>
fn gsub_ok_387(@T, @Nat, @Nat -> @Nat)
  requires(@Nat.0 >= @Nat.1) ensures(true) effects(pure)
{ @Nat.0 - @Nat.1 }

public fn use_int_ok_387(@Int -> @Nat)
  requires(true) ensures(true) effects(pure)
{ gsub_ok_387(@Int.0, 3, 1) }

public fn use_bool_ok_387(@Bool -> @Nat)
  requires(true) ensures(true) effects(pure)
{ gsub_ok_387(@Bool.0, 5, 2) }
""")
        assert [d for d in result.diagnostics if d.severity == "error"] == [], [
            d.description for d in result.diagnostics if d.severity == "error"]
        subs = [o for o in result.obligations
                if o.kind == "nat_sub" and o.fn_name == "gsub_ok_387"]
        assert len(subs) == 1, [(o.kind, o.fn_name, o.status)
                                for o in result.obligations]
        assert subs[0].status == "verified", subs[0].status

    # =================================================================
    # _meet_status  (1164-1175) — worst-case status across
    # instantiations, with timeout folded into tier3.  Pure static
    # method: tested directly so each ordered branch has a surgical
    # differential (integration can't easily mix tier3_unguarded with
    # tier3 across instantiations).
    # =================================================================

    def test_meet_status_violated_dominates(self) -> None:
        """``violated`` is the worst case — it must win over every other status.
        Pins the FIRST branch (1169-1170).  A mutation deleting it would let a
        reachable counterexample be downgraded to tier3/verified — the exact
        false-Tier-1 the meet exists to prevent."""
        from vera.verifier import ContractVerifier
        m = ContractVerifier._meet_status
        assert m(["verified", "violated", "tier3"]) == "violated"
        assert m(["tier3_unguarded", "violated"]) == "violated"
        assert m(["violated"]) == "violated"

    def test_meet_status_tier3_unguarded_over_tier3(self) -> None:
        """``tier3_unguarded`` outranks ``tier3``/``verified`` (1171-1172).
        Pins the ORDER: a mutation swapping this below the tier3 check would
        report ``tier3`` for a mix that includes an UNGUARDED runtime obligation,
        losing the "no codegen guard" distinction (a refined narrowing has no
        runtime guard, so mislabeling it tier3 implies a guard that isn't
        there)."""
        from vera.verifier import ContractVerifier
        m = ContractVerifier._meet_status
        assert m(["verified", "tier3_unguarded", "tier3"]) == "tier3_unguarded"
        assert m(["tier3", "tier3_unguarded"]) == "tier3_unguarded"

    def test_meet_status_tier3_from_tier3_or_timeout(self) -> None:
        """The tier3 branch (1173-1174) folds BOTH ``tier3`` and ``timeout``
        into ``tier3`` (the mirror-friendly vocabulary).  Two assertions pin the
        two disjuncts independently: a mutation deleting the ``timeout`` disjunct
        would mis-report a timed-out instantiation as ``verified``."""
        from vera.verifier import ContractVerifier
        m = ContractVerifier._meet_status
        assert m(["verified", "tier3"]) == "tier3"
        assert m(["verified", "timeout"]) == "tier3"

    def test_meet_status_all_verified(self) -> None:
        """All instantiations ``verified`` → ``verified`` (the 1175 fallthrough).
        The negative partner: a mutation hard-coding an earlier branch's return
        would mislabel a fully-proven generic as tier3/violated."""
        from vera.verifier import ContractVerifier
        m = ContractVerifier._meet_status
        assert m(["verified", "verified", "verified"]) == "verified"
        assert m(["verified"]) == "verified"


class TestSmtTranslation387:
    """#387: pin the Z3-translation layer (``vera/smt.py``) differentially.

    ``smt.py`` is never called directly by a test — it is the Z3 layer the
    verifier reaches *through* ``_verify(source)``.  So every test here is a
    DIFFERENTIAL: a Vera program whose verification *outcome* (an obligation's
    ``.status`` / ``.error_code``, the summary counters, or a counterexample's
    content) depends on ``smt`` translating an operator / built-in, solving
    sat↔unsat, or extracting a model correctly.  For each test the docstring
    names the targeted ``smt`` function and the mutation it would catch: "if
    ``smt``'s F mutated to M, THIS assertion flips" is what makes it a kill
    rather than a mere pass.

    Lever (the ``ensures``-over-body postcondition is Tier 3 in this verifier,
    so it is NOT the lever): the **call-site precondition check** (``call_pre``
    / E501) runs a callee ``requires`` predicate through
    ``check_valid`` → ``_extract_counterexample``, with the actual-argument
    expression translated by ``translate_expr`` / the built-in dispatch.  A
    callee whose ``requires`` bound (``>= 0``, ``<= 10`` …) holds for the real
    semantics of the argument expression but NOT for a mutated one therefore
    flips ``verified`` ↔ ``violated`` exactly on the mutation.  The Tier-1
    obligation walkers (``nat_sub`` E502, ``nat_bind`` E503, ``div_zero`` E526,
    ``index_bounds`` E527) give the same lever without a callee.

    Assertions use ``==`` on obligation fields/codes/statuses, ``==`` on the
    exact summary tuple, and ``==`` on counterexample dict items — never
    substring ``in`` on a message (mutmut wraps string literals as ``"XX"+s+
    "XX"`` so substring assertions don't kill string mutations).  Distinct
    ``_387`` names defeat a ``fn_name → None`` mutation.
    """

    # Reusable callee skeletons.  Each imposes a single primitive bound so the
    # caller's argument-expression translation is the only thing under test.
    _NEEDS_GE0 = """
private fn needs_ge0_s387(@Int -> @Int)
  requires(@Int.0 >= 0) ensures(true) effects(pure)
{ @Int.0 }
"""
    _NEEDS_LE10 = """
private fn needs_le10_s387(@Int -> @Int)
  requires(@Int.0 <= 10) ensures(true) effects(pure)
{ @Int.0 }
"""
    _NEEDS_TRUE = """
private fn needs_true_s387(@Bool -> @Int)
  requires(@Bool.0) ensures(true) effects(pure)
{ 0 }
"""

    @staticmethod
    def _viol(result: VerifyResult) -> list:
        return [o for o in result.obligations if o.status == "violated"]

    @staticmethod
    def _by_fn_kind(result: VerifyResult, fn: str, kind: str):
        ms = [o for o in result.obligations
              if o.fn_name == fn and o.kind == kind]
        assert len(ms) == 1, [(o.fn_name, o.kind, o.status) for o in result.obligations]
        return ms[0]

    # =================================================================
    # translate_expr / _translate_binary — arithmetic + comparison ops.
    # The call-precondition lever: a callee `requires(@Int.0 >= 100)` is
    # discharged iff the actual argument translates with the right op.
    # =================================================================

    def test_arith_add_satisfies_precondition(self) -> None:
        """``@Int.0 + @Int.1`` as an actual arg to ``requires(@Int.0 >= 0)``
        with both params constrained ``>= 0`` VERIFIES (sum of two nonneg is
        nonneg) — pins ``_translate_binary`` ADD.  A mutation of ``+`` to ``-``
        would make ``@Int.0 - @Int.1`` possibly negative → E501.  Uses Nat
        params so the premise is carried."""
        result = _verify(self._NEEDS_GE0 + """
private fn add_arg_s387(@Nat, @Nat -> @Int)
  requires(true) ensures(true) effects(pure)
{ needs_ge0_s387(@Nat.0 + @Nat.1) }
""")
        assert [d for d in result.diagnostics if d.severity == "error"] == [], [
            d.description for d in result.diagnostics if d.severity == "error"]
        o = self._by_fn_kind(result, "add_arg_s387", "requires")
        assert o.status == "verified", o.status

    def test_arith_sub_violates_precondition_with_ce(self) -> None:
        """``@Nat.0 - @Nat.1`` (Nat subtraction) fed to ``requires(@Int.0 >= 0)``
        is NOT provably nonneg (it can underflow into the integers) → E501
        ``call_pre`` violated.  Pins ``_translate_binary`` SUB *and*
        ``_extract_counterexample``: the CE names BOTH operands.  A mutation of
        ``-`` to ``+`` would discharge the bound (nonneg) and lose the
        error."""
        result = _verify(self._NEEDS_GE0 + """
private fn sub_arg_s387(@Nat, @Nat -> @Int)
  requires(true) ensures(true) effects(pure)
{ needs_ge0_s387(@Nat.0 - @Nat.1) }
""")
        o = self._by_fn_kind(result, "sub_arg_s387", "call_pre")
        assert o.status == "violated", o.status
        assert o.error_code == "E501", o.error_code
        assert o.counterexample is not None, o.counterexample
        assert "@Nat.0" in o.counterexample, o.counterexample
        assert "@Nat.1" in o.counterexample, o.counterexample

    def test_comparison_lt_path_condition_discharges(self) -> None:
        """A branch guard ``if @Int.0 < 10 then needs_le10(@Int.0) else 0``
        discharges the callee ``requires(@Int.0 <= 10)`` in the then-branch —
        pins ``_translate_binary`` LT feeding ``_path_conditions``.  The else
        branch passes a literal in range.  A mutation of ``<`` to ``>`` would
        flip the guard so the then-branch sees ``@Int.0 > 10`` and the bound
        ``<= 10`` would fail."""
        result = _verify(self._NEEDS_LE10 + """
private fn lt_guard_s387(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ if @Int.0 < 10 then { needs_le10_s387(@Int.0) } else { 0 } }
""")
        assert [d for d in result.diagnostics if d.severity == "error"] == [], [
            d.description for d in result.diagnostics if d.severity == "error"]
        o = self._by_fn_kind(result, "lt_guard_s387", "requires")
        assert o.status == "verified", o.status

    # =================================================================
    # _translate_call (built-ins): abs / min / max — `If(...)` shapes.
    # Each pairs a verify (real semantics satisfy the bound) with a
    # violate (real semantics break it but the swapped op would pass).
    # =================================================================

    def test_builtin_abs_nonneg_satisfies_precondition(self) -> None:
        """``abs(@Int.0)`` fed to ``requires(@Int.0 >= 0)`` VERIFIES — pins the
        ``abs`` built-in ``If(arg >= 0, arg, -arg)``.  A mutation of the ``-arg``
        branch (to ``arg``) makes ``abs`` the identity, so a negative argument
        would violate the bound."""
        result = _verify(self._NEEDS_GE0 + """
private fn abs_ok_s387(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ needs_ge0_s387(abs(@Int.0)) }
""")
        assert [d for d in result.diagnostics if d.severity == "error"] == [], [
            d.description for d in result.diagnostics if d.severity == "error"]
        o = self._by_fn_kind(result, "abs_ok_s387", "requires")
        assert o.status == "verified", o.status

    def test_builtin_min_upper_bound_satisfies_and_lower_violates(self) -> None:
        """``min(@Int.0, 10)`` is always ``<= 10`` (satisfies ``requires(@Int.0
        <= 10)``) but NOT always ``>= 0`` (violates ``requires(@Int.0 >= 0)``,
        CE ``@Int.0 = -1``).  The pair pins ``min`` = ``If(a <= b, a, b)``: a
        mutation of ``<=`` to ``>=`` turns ``min`` into ``max``, which would
        flip BOTH verdicts (``max(x,10) >= 10`` discharges the lower bound and
        can exceed the upper)."""
        ok = _verify(self._NEEDS_LE10 + """
private fn min_le_s387(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ needs_le10_s387(min(@Int.0, 10)) }
""")
        assert [d for d in ok.diagnostics if d.severity == "error"] == [], [
            d.description for d in ok.diagnostics if d.severity == "error"]
        assert self._by_fn_kind(ok, "min_le_s387", "requires").status == "verified"

        neg = _verify(self._NEEDS_GE0 + """
private fn min_ge_s387(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ needs_ge0_s387(min(@Int.0, 10)) }
""")
        o = self._by_fn_kind(neg, "min_ge_s387", "call_pre")
        assert o.status == "violated", o.status
        assert o.error_code == "E501", o.error_code
        assert o.counterexample == {"@Int.0": "-1", "@result": "0"}, o.counterexample

    def test_builtin_max_lower_bound_satisfies_and_upper_violates(self) -> None:
        """Mirror of ``min``: ``max(@Int.0, 0)`` is always ``>= 0`` (satisfies
        the lower bound) but NOT always ``<= 10`` (violates the upper, CE
        ``@Int.0 = 11``).  Pins ``max`` = ``If(a >= b, a, b)``: the ``>=``→``<=``
        mutation turns it into ``min`` and flips both verdicts."""
        ok = _verify(self._NEEDS_GE0 + """
private fn max_ge_s387(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ needs_ge0_s387(max(@Int.0, 0)) }
""")
        assert [d for d in ok.diagnostics if d.severity == "error"] == [], [
            d.description for d in ok.diagnostics if d.severity == "error"]
        assert self._by_fn_kind(ok, "max_ge_s387", "requires").status == "verified"

        neg = _verify(self._NEEDS_LE10 + """
private fn max_le_s387(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ needs_le10_s387(max(@Int.0, 0)) }
""")
        o = self._by_fn_kind(neg, "max_le_s387", "call_pre")
        assert o.status == "violated", o.status
        assert o.error_code == "E501", o.error_code
        assert o.counterexample == {"@Int.0": "11", "@result": "0"}, o.counterexample

    # =================================================================
    # _translate_call (built-ins): array_length / string_length —
    # uninterpreted fns with an asserted `result >= 0` axiom.
    # =================================================================

    def test_builtin_array_length_nonneg_axiom(self) -> None:
        """``array_length(@Array<Int>.0)`` fed to ``requires(@Int.0 >= 0)``
        VERIFIES SOLELY because the built-in asserts ``result >= 0`` to the
        solver — pins that ``self.solver.add(result >= 0)`` in the
        ``array_length`` branch (an uninterpreted length fn is otherwise
        unconstrained, so dropping the axiom flips this to E501)."""
        result = _verify(self._NEEDS_GE0 + """
private fn arrlen_s387(@Array<Int> -> @Int)
  requires(true) ensures(true) effects(pure)
{ needs_ge0_s387(array_length(@Array<Int>.0)) }
""")
        assert [d for d in result.diagnostics if d.severity == "error"] == [], [
            d.description for d in result.diagnostics if d.severity == "error"]
        o = self._by_fn_kind(result, "arrlen_s387", "requires")
        assert o.status == "verified", o.status

    def test_builtin_string_length_nonneg_via_z3_length(self) -> None:
        """``string_length(@String.0)`` fed to ``requires(@Int.0 >= 0)``
        VERIFIES — pins the ``string_length`` branch (``z3.Length`` for the Seq
        sort, plus the ``result >= 0`` axiom).  Z3's ``Length`` is nonneg by
        theory, so a String literal/var length is always ``>= 0``; a mutation
        dropping the axiom or the Seq-sort guard would lose the discharge."""
        result = _verify(self._NEEDS_GE0 + """
private fn strlen_s387(@String -> @Int)
  requires(true) ensures(true) effects(pure)
{ needs_ge0_s387(string_length(@String.0)) }
""")
        assert [d for d in result.diagnostics if d.severity == "error"] == [], [
            d.description for d in result.diagnostics if d.severity == "error"]
        o = self._by_fn_kind(result, "strlen_s387", "requires")
        assert o.status == "verified", o.status

    def test_builtin_string_contains_self_is_true(self) -> None:
        """``string_contains(@String.0, @String.0)`` fed to ``requires(@Bool.0)``
        VERIFIES — a string contains itself (``z3.Contains(s, s)`` is valid).
        Pins the ``string_contains`` → ``z3.Contains`` mapping: a mutation
        swapping the argument order is masked here (self-contains), but a
        mutation to ``PrefixOf``/``SuffixOf`` with swapped args, or returning an
        unconstrained Bool, would drop the discharge."""
        result = _verify(self._NEEDS_TRUE + """
private fn contains_s387(@String -> @Int)
  requires(true) ensures(true) effects(pure)
{ needs_true_s387(string_contains(@String.0, @String.0)) }
""")
        assert [d for d in result.diagnostics if d.severity == "error"] == [], [
            d.description for d in result.diagnostics if d.severity == "error"]
        o = self._by_fn_kind(result, "contains_s387", "requires")
        assert o.status == "verified", o.status

    # =================================================================
    # check_valid — the sat/unsat → verified/violated mapping, and
    # _extract_counterexample — model → dict[str,str].
    # =================================================================

    def test_check_valid_verified_branch(self) -> None:
        """A provably-valid precondition (``@Nat.0 >= 0`` passed a Nat) maps to
        ``verified`` — pins ``check_valid``'s ``unsat → SmtResult(verified)``
        arm.  Carried by ``declare_nat``'s ``>= 0`` premise."""
        result = _verify(self._NEEDS_GE0 + """
private fn cv_ok_s387(@Nat -> @Int)
  requires(true) ensures(true) effects(pure)
{ needs_ge0_s387(@Nat.0) }
""")
        assert [d for d in result.diagnostics if d.severity == "error"] == [], [
            d.description for d in result.diagnostics if d.severity == "error"]
        o = self._by_fn_kind(result, "cv_ok_s387", "requires")
        assert o.status == "verified", o.status

    def test_check_valid_violated_branch_carries_counterexample(self) -> None:
        """A refutable precondition (``@Int.0 >= 0`` passed an unconstrained
        Int) maps to ``violated`` WITH a counterexample — pins ``check_valid``'s
        ``sat → SmtResult(violated, ce)`` arm AND the model-before-pop ordering
        (a witness, not a base-context default).  CE is the forced witness
        ``@Int.0 = -1``."""
        result = _verify(self._NEEDS_GE0 + """
private fn cv_neg_s387(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ needs_ge0_s387(@Int.0) }
""")
        o = self._by_fn_kind(result, "cv_neg_s387", "call_pre")
        assert o.status == "violated", o.status
        assert o.error_code == "E501", o.error_code
        assert o.counterexample == {"@Int.0": "-1", "@result": "0"}, o.counterexample

    def test_extract_counterexample_enumerates_all_vars(self) -> None:
        """``needs_big(@Int.0 + @Int.1)`` against ``requires(@Int.0 >= 100)``
        violates with a CE naming BOTH operands — pins
        ``_extract_counterexample`` iterating EVERY entry of ``self._vars`` (a
        mutation iterating a subset, or skipping the loop body, would drop one
        slot key)."""
        result = _verify("""
private fn needs_big_s387(@Int -> @Int)
  requires(@Int.0 >= 100) ensures(true) effects(pure)
{ 0 }
private fn ce_two_s387(@Int, @Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ needs_big_s387(@Int.0 + @Int.1) }
""")
        o = self._by_fn_kind(result, "ce_two_s387", "call_pre")
        assert o.status == "violated", o.status
        assert o.counterexample is not None, o.counterexample
        assert "@Int.0" in o.counterexample, o.counterexample
        assert "@Int.1" in o.counterexample, o.counterexample

    # =================================================================
    # _translate_call_with_info — precondition checking + arity.
    # (The postcondition-assumption loop is not differentially reachable
    # from the verifier surface: an assumed ensures does not propagate
    # to discharge a *downstream* call precondition, so it has no test
    # here — see the agent report's residual note.)
    # =================================================================

    def test_callee_precondition_propagates_to_caller(self) -> None:
        """The caller passes a possibly-negative value to a helper that
        ``requires(@Int.0 >= 0)`` → the precondition check fires as the caller's
        ``call_pre`` E501 (not the callee's).  Pins ``_translate_call_with_info``
        precondition-checking: the violation is attributed to the CALL SITE
        (``fn_name == "fwd_neg_s387"``, ``callee_name`` recorded separately)."""
        result = _verify("""
private fn sink_ge0_s387(@Int -> @Int)
  requires(@Int.0 >= 0) ensures(true) effects(pure)
{ @Int.0 }
private fn fwd_neg_s387(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ sink_ge0_s387(@Int.0) }
""")
        o = self._by_fn_kind(result, "fwd_neg_s387", "call_pre")
        assert o.status == "violated", o.status
        assert o.error_code == "E501", o.error_code
        assert o.fn_name == "fwd_neg_s387", o.fn_name
        # The callee verifies its own (trivial) contracts independently.
        sink = self._by_fn_kind(result, "sink_ge0_s387", "requires")
        assert sink.status == "verified", sink.status

    # =================================================================
    # _pattern_condition / _translate_match — path-condition narrowing.
    # The matched arm asserts `scrutinee == <pattern value>`; a call
    # precondition inside the arm is discharged iff that holds.
    # =================================================================

    def test_bool_pattern_true_arm_discharges_precondition(self) -> None:
        """In ``match b { true -> needs_true(b), false -> 0 }`` the true-arm
        path condition ``b == true`` discharges ``requires(@Bool.0)`` — pins
        ``_pattern_condition`` ``BoolPattern → scrutinee == BoolVal(True)`` and
        ``_translate_match`` pushing it into ``_path_conditions``."""
        result = _verify(self._NEEDS_TRUE + """
private fn bool_t_s387(@Bool -> @Int)
  requires(true) ensures(true) effects(pure)
{ match @Bool.0 { true -> needs_true_s387(@Bool.0), false -> 0 } }
""")
        assert [d for d in result.diagnostics if d.severity == "error"] == [], [
            d.description for d in result.diagnostics if d.severity == "error"]
        o = self._by_fn_kind(result, "bool_t_s387", "requires")
        assert o.status == "verified", o.status

    def test_bool_pattern_false_arm_violates_with_ce(self) -> None:
        """The mirror: in the FALSE arm, ``needs_true(b)`` is unsatisfiable
        because the path condition is ``b == false`` → E501 with CE
        ``@Bool.0 = False``.  If ``_pattern_condition`` mutated the BoolPattern
        value (or used the wrong recognizer) the two arms would swap verdicts."""
        result = _verify(self._NEEDS_TRUE + """
private fn bool_f_s387(@Bool -> @Int)
  requires(true) ensures(true) effects(pure)
{ match @Bool.0 { false -> needs_true_s387(@Bool.0), true -> 0 } }
""")
        o = self._by_fn_kind(result, "bool_f_s387", "call_pre")
        assert o.status == "violated", o.status
        assert o.error_code == "E501", o.error_code
        assert o.counterexample == {"@Bool.0": "False", "@result": "0"}, o.counterexample

    def test_int_pattern_arm_narrows_scrutinee(self) -> None:
        """In ``match n { 5 -> needs_ge3(n), _ -> 0 }`` the literal arm's path
        condition ``n == 5`` discharges ``requires(@Int.0 >= 3)`` — pins
        ``_pattern_condition`` ``IntPattern → scrutinee == IntVal(5)``."""
        result = _verify("""
private fn needs_ge3_s387(@Int -> @Int)
  requires(@Int.0 >= 3) ensures(true) effects(pure)
{ 0 }
private fn int5_s387(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ match @Int.0 { 5 -> needs_ge3_s387(@Int.0), @Int -> 0 } }
""")
        assert [d for d in result.diagnostics if d.severity == "error"] == [], [
            d.description for d in result.diagnostics if d.severity == "error"]
        o = self._by_fn_kind(result, "int5_s387", "requires")
        assert o.status == "verified", o.status

    def test_int_pattern_wrong_value_arm_violates_with_ce(self) -> None:
        """The mirror: the ``1`` arm's path condition ``n == 1`` does NOT satisfy
        ``>= 3`` → E501 with CE ``@Int.0 = 1`` (the IntVal the pattern pinned).
        A mutation of the pattern literal would change the CE value."""
        result = _verify("""
private fn needs_ge3b_s387(@Int -> @Int)
  requires(@Int.0 >= 3) ensures(true) effects(pure)
{ 0 }
private fn int1_s387(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ match @Int.0 { 1 -> needs_ge3b_s387(@Int.0), @Int -> 0 } }
""")
        o = self._by_fn_kind(result, "int1_s387", "call_pre")
        assert o.status == "violated", o.status
        assert o.counterexample == {"@Int.0": "1", "@result": "0"}, o.counterexample

    # =================================================================
    # _translate_nullary_ctor / _pattern_condition (recognizer) /
    # _get_or_create_adt_sort — custom-ADT nullary match dispatch.
    # =================================================================

    def test_custom_adt_nullary_match_verifies(self) -> None:
        """A custom 3-constructor ADT (``Red|Green|Blue``) matched with nullary
        recognizers, where one arm discharges a nonneg bound via
        ``array_length`` — pins ``_translate_nullary_ctor`` + the
        ``_pattern_condition`` NullaryPattern recognizer + ADT-sort creation
        (``_get_or_create_adt_sort``).  Reachability: a malformed sort or a
        wrong recognizer would make the match untranslatable (whole obligation
        drops to Tier 3)."""
        result = _verify("""
private data Color_s387 { Red, Green, Blue }
private fn needs_ge0col_s387(@Int -> @Int)
  requires(@Int.0 >= 0) ensures(true) effects(pure)
{ 0 }
private fn col_s387(@Color_s387 -> @Int)
  requires(true) ensures(true) effects(pure)
{ match @Color_s387.0 {
    Red -> needs_ge0col_s387(array_length([7])),
    Green -> 0,
    Blue -> 0 } }
""")
        assert [d for d in result.diagnostics if d.severity == "error"] == [], [
            d.description for d in result.diagnostics if d.severity == "error"]
        o = self._by_fn_kind(result, "col_s387", "requires")
        assert o.status == "verified", o.status

    # =================================================================
    # get_rank_fn — structural rank axioms for recursive-ADT decreases.
    # =================================================================

    def test_recursive_decreases_verified_via_rank_fn(self) -> None:
        """A structurally-recursive ``len`` over ``Cons(T, L<T>)`` with
        ``decreases(@L<Int>.0)`` VERIFIES — pins ``get_rank_fn``'s structural
        axiom ``is_Cons(x) ⟹ rank(tail(x)) < rank(x)`` (without it the recursive
        call on the tail can't be shown to decrease → not ``verified``)."""
        result = _verify("""
private data L_s387<T> { Nil, Cons(T, L_s387<T>) }
private fn len_s387(@L_s387<Int> -> @Nat)
  requires(true) ensures(true) decreases(@L_s387<Int>.0) effects(pure)
{ match @L_s387<Int>.0 {
    Nil -> 0,
    Cons(@Int, @L_s387<Int>) -> 1 + len_s387(@L_s387<Int>.0) } }
""")
        assert [d for d in result.diagnostics if d.severity == "error"] == [], [
            d.description for d in result.diagnostics if d.severity == "error"]
        o = self._by_fn_kind(result, "len_s387", "decreases")
        assert o.status == "verified", o.status

    def test_nondecreasing_recursion_is_not_verified(self) -> None:
        """The mirror: recursing on the SAME metric ``bad(@Nat.0)`` does NOT
        decrease, so the ``decreases`` obligation is NOT ``verified`` (Tier 3,
        E525).  Distinguishes ``get_rank_fn``/numeric-decrease from a mutation
        that always reports the metric as decreasing."""
        result = _verify("""
private fn bad_s387(@Nat -> @Nat)
  requires(true) ensures(true) decreases(@Nat.0) effects(pure)
{ if @Nat.0 == 0 then { 0 } else { bad_s387(@Nat.0) } }
""")
        o = self._by_fn_kind(result, "bad_s387", "decreases")
        assert o.status != "verified", o.status
        assert o.status == "tier3", o.status

    # =================================================================
    # _get_or_create_tuple_sort — non-literal tuple destructure makes
    # the components projectable so each narrows independently.
    # =================================================================

    def test_nonliteral_tuple_destructure_obligates_each_field(self) -> None:
        """``let Tuple<@Nat,@Nat> = mk(@Int.0)`` where ``mk`` returns
        ``@Tuple<Int,Int>`` produces TWO ``nat_bind`` (E503) obligations — one
        per projected component.  Pins ``_get_or_create_tuple_sort``: it builds
        a Tuple datatype with a field+accessor per component so each projection
        narrows.  If Tuple fell back to a scalar ``Int``, the per-field
        projections would not exist and the obligation count would change."""
        result = _verify("""
private fn mk_s387(@Int -> @Tuple<Int, Int>)
  requires(true) ensures(true) effects(pure)
{ Tuple(@Int.0, @Int.0) }
private fn use_tup_s387(@Int -> @Nat)
  requires(true) ensures(true) effects(pure)
{ let Tuple<@Nat, @Nat> = mk_s387(@Int.0); @Nat.0 }
""")
        binds = [o for o in result.obligations
                 if o.fn_name == "use_tup_s387" and o.kind == "nat_bind"]
        assert len(binds) == 2, [(o.kind, o.status) for o in result.obligations]
        for o in binds:
            assert o.status == "violated", o.status
            assert o.error_code == "E503", o.error_code

    # =================================================================
    # _get_index_fn / _get_element_sort_for_array / _get_length_fn —
    # array index-bounds machinery.
    # =================================================================

    def test_index_bounds_guarded_verifies(self) -> None:
        """``arr[i]`` guarded by ``requires(i >= 0 && i < array_length(arr))``
        makes the ``index_bounds`` (E527) obligation VERIFIED — pins the array
        machinery (``_get_length_fn`` for ``array_length``, ``_get_index_fn`` /
        ``_get_element_sort_for_array`` for the index translation) AND the
        ``&&``/``<`` translation in the guard.  Without the length fn correctly
        modelling the bound, the index check would not discharge."""
        result = _verify("""
private fn idx_ok_s387(@Array<Int>, @Int -> @Int)
  requires(@Int.0 >= 0 && @Int.0 < array_length(@Array<Int>.0))
  ensures(true) effects(pure)
{ @Array<Int>.0[@Int.0] }
""")
        assert [d for d in result.diagnostics if d.severity == "error"] == [], [
            d.description for d in result.diagnostics if d.severity == "error"]
        o = self._by_fn_kind(result, "idx_ok_s387", "index_bounds")
        assert o.status == "verified", o.status

    def test_index_bounds_unguarded_is_tier3(self) -> None:
        """The mirror: an unguarded ``arr[i]`` cannot prove ``0 <= i <
        length(arr)`` → ``index_bounds`` is Tier 3 (runtime check), not
        verified.  Distinguishes the real bound check from a mutation that
        vacuously discharges it."""
        result = _verify("""
private fn idx_raw_s387(@Array<Int>, @Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Array<Int>.0[@Int.0] }
""")
        o = self._by_fn_kind(result, "idx_raw_s387", "index_bounds")
        assert o.status == "tier3", o.status

    # =================================================================
    # div_zero (E526) / nat_sub (E502) — Tier-1 walker obligations that
    # exercise translate_expr's DIV and SUB plus counterexample content.
    # =================================================================

    def test_div_zero_unguarded_violates(self) -> None:
        """``@Int.1 / @Int.0`` with no guard on the divisor → ``div_zero`` (E526)
        violated.  Pins translate_expr DIV reaching the verifier's divisor
        walker; guarding the divisor (next test) flips it to verified."""
        result = _verify("""
private fn div_raw_s387(@Int, @Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.1 / @Int.0 }
""")
        o = self._by_fn_kind(result, "div_raw_s387", "div_zero")
        assert o.status == "violated", o.status
        assert o.error_code == "E526", o.error_code

    def test_div_zero_guarded_verifies(self) -> None:
        """``@Int.1 / @Int.0`` with ``requires(@Int.0 != 0)`` → ``div_zero``
        verified.  Pins the ``!=`` (NEQ) translation feeding the divisor guard:
        a mutation of NEQ to EQ would make the guard ``@Int.0 == 0`` and the
        divisor obligation would no longer discharge."""
        result = _verify("""
private fn div_ok_s387(@Int, @Int -> @Int)
  requires(@Int.0 != 0) ensures(true) effects(pure)
{ @Int.1 / @Int.0 }
""")
        assert [d for d in result.diagnostics if d.severity == "error"] == [], [
            d.description for d in result.diagnostics if d.severity == "error"]
        o = self._by_fn_kind(result, "div_ok_s387", "div_zero")
        assert o.status == "verified", o.status

    def test_nat_sub_underflow_violates_with_both_slots_in_ce(self) -> None:
        """``@Nat.1 - @Nat.0`` can underflow → ``nat_sub`` (E502) violated, with a
        counterexample naming BOTH Nat operands.  Pins translate_expr SUB on the
        Nat-subtraction walker AND ``_extract_counterexample`` enumerating each
        ``_vars`` entry."""
        result = _verify("""
private fn natsub_s387(@Nat, @Nat -> @Nat)
  requires(true) ensures(true) effects(pure)
{ @Nat.1 - @Nat.0 }
""")
        o = self._by_fn_kind(result, "natsub_s387", "nat_sub")
        assert o.status == "violated", o.status
        assert o.error_code == "E502", o.error_code
        assert o.counterexample is not None, o.counterexample
        assert "@Nat.0" in o.counterexample, o.counterexample
        assert "@Nat.1" in o.counterexample, o.counterexample
