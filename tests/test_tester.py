"""Tests for vera.tester — contract-driven test engine."""

from __future__ import annotations

from vera.parser import parse
from vera.tester import test as run_test
from vera.tester import TestResult, FunctionTestResult
from vera.transform import transform
from vera.checker import typecheck


# =====================================================================
# Helpers
# =====================================================================


def _test(source: str, trials: int = 10, fn_name: str | None = None) -> TestResult:
    """Parse, type-check, and test a Vera source string."""
    tree = parse(source, file="<test>")
    program = transform(tree)
    errors = typecheck(program, source=source, file="<test>")
    assert not errors, f"Type errors: {errors[0].description}"
    return run_test(
        program, source=source, file="<test>", trials=trials, fn_name=fn_name,
    )


def _fn_result(result: TestResult, name: str) -> FunctionTestResult:
    """Find a function result by name."""
    for f in result.functions:
        if f.fn_name == name:
            return f
    raise KeyError(f"Function {name!r} not found in results")


# =====================================================================
# Tier 1 (verified) functions
# =====================================================================


class TestTier1:
    """Functions whose contracts are fully proved should be reported as verified."""

    def test_simple_verified(self) -> None:
        """An absolute_value-like function with provable contracts."""
        source = """\
public fn abs_val(@Int -> @Int)
  requires(true)
  ensures(@Int.result >= 0)
  effects(pure)
{
  if @Int.0 >= 0 then { @Int.0 } else { 0 - @Int.0 }
}
"""
        result = _test(source)
        f = _fn_result(result, "abs_val")
        assert f.category == "verified"
        assert f.trials_run == 0
        assert result.summary.verified == 1

    def test_safe_divide_verified(self) -> None:
        """safe_divide has a Tier 1 postcondition."""
        source = """\
public fn safe_divide(@Int, @Int -> @Int)
  requires(@Int.1 != 0)
  ensures(@Int.result == @Int.0 / @Int.1)
  effects(pure)
{
  @Int.0 / @Int.1
}
"""
        result = _test(source)
        f = _fn_result(result, "safe_divide")
        assert f.category == "verified"
        assert f.trials_run == 0


# =====================================================================
# Tier 3 (tested) functions
# =====================================================================


class TestTier3:
    """Functions with runtime-checked contracts should be tested."""

    def test_tier3_passing(self) -> None:
        """A function with an unverifiable decreases(0) should be tested.

        Mutual recursion is now verified (Tier 1), so we use a
        non-recursive function with decreases(0) which stays Tier 3.
        """
        source = """\
public fn identity(@Nat -> @Nat)
  requires(true)
  ensures(true)
  decreases(0)
  effects(pure)
{
  @Nat.0
}
"""
        result = _test(source, trials=10)
        f = _fn_result(result, "identity")
        assert f.category == "tested"
        assert f.trials_passed > 0
        assert f.trials_failed == 0
        assert result.summary.tested == 1
        assert result.summary.passed == 1

    def test_tier3_failing(self) -> None:
        """A function whose contract is violated for some inputs."""
        # This function claims result >= 0, but for negative inputs
        # it returns the input itself (which is negative).
        source = """\
public fn buggy(@Int -> @Int)
  requires(true)
  ensures(@Int.result >= 0)
  decreases(0)
  effects(pure)
{
  @Int.0
}
"""
        result = _test(source, trials=20)
        f = _fn_result(result, "buggy")
        assert f.category == "tested"
        assert f.trials_failed > 0
        assert result.summary.failed == 1


# =====================================================================
# Skipped functions
# =====================================================================


class TestSkipped:
    """Functions that cannot be tested should be skipped."""

    def test_generic_function(self) -> None:
        """Generic functions are skipped (type vars not Z3-encodable)."""
        source = """\
public forall<T> fn identity(@T -> @T)
  requires(true)
  ensures(true)
  effects(pure)
{
  @T.0
}
"""
        result = _test(source)
        f = _fn_result(result, "identity")
        assert f.category == "skipped"
        assert "generic" in f.reason.lower()

    def test_string_parameter(self) -> None:
        """String params are now supported — function is tested, not skipped.

        Uses decreases(0) to force Tier 3 classification so the function
        is exercised with generated inputs rather than proved statically.
        """
        source = """\
public fn greet(@String -> @Int)
  requires(true)
  ensures(@Int.result >= 0)
  decreases(0)
  effects(pure)
{
  0
}
"""
        result = _test(source)
        f = _fn_result(result, "greet")
        assert f.category == "tested"

    def test_float_parameter(self) -> None:
        """Float64 params are now supported — function is tested, not skipped.

        Uses decreases(0) to force Tier 3 classification.
        """
        source = """\
public fn scale(@Float64 -> @Float64)
  requires(true)
  ensures(true)
  decreases(0)
  effects(pure)
{
  @Float64.0
}
"""
        result = _test(source)
        f = _fn_result(result, "scale")
        assert f.category == "tested"

    def test_trivial_contracts(self) -> None:
        """Functions with only trivial contracts are skipped."""
        source = """\
public fn trivial(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Int.0
}
"""
        result = _test(source)
        f = _fn_result(result, "trivial")
        assert f.category == "skipped"
        assert "trivial" in f.reason.lower()

    def test_private_function_excluded(self) -> None:
        """Private functions are not tested."""
        source = """\
private fn helper(@Int -> @Int)
  requires(true)
  ensures(@Int.result >= 0)
  effects(pure)
{
  if @Int.0 >= 0 then { @Int.0 } else { 0 - @Int.0 }
}

public fn main(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  helper(@Int.0)
}
"""
        result = _test(source)
        names = [f.fn_name for f in result.functions]
        assert "helper" not in names


# =====================================================================
# Input generation
# =====================================================================


class TestInputGeneration:
    """Verify Z3-based input generation respects contracts."""

    def test_narrow_precondition(self) -> None:
        """Requires constraining inputs should produce valid inputs only."""
        source = """\
public fn small_range(@Int -> @Int)
  requires(@Int.0 >= 0 && @Int.0 <= 10)
  ensures(@Int.result >= 0)
  decreases(0)
  effects(pure)
{
  @Int.0
}
"""
        result = _test(source, trials=20)
        f = _fn_result(result, "small_range")
        assert f.category == "tested"
        # All trials should pass — inputs within [0, 10] satisfy ensures
        assert f.trials_failed == 0
        # Should get at most 11 unique inputs (0..10)
        assert f.trials_run <= 11

    def test_bool_exhaustion(self) -> None:
        """Bool parameters have at most 2 values."""
        source = """\
public fn bool_fn(@Bool -> @Int)
  requires(true)
  ensures(@Int.result >= 0)
  decreases(0)
  effects(pure)
{
  if @Bool.0 then { 1 } else { 0 }
}
"""
        result = _test(source, trials=50)
        f = _fn_result(result, "bool_fn")
        assert f.category == "tested"
        # Only 2 possible inputs for Bool
        assert f.trials_run <= 2

    def test_nat_nonnegative(self) -> None:
        """Nat parameters should all be >= 0."""
        source = """\
public fn nat_fn(@Nat -> @Nat)
  requires(@Nat.0 <= 100)
  ensures(@Nat.result >= 0)
  decreases(0)
  effects(pure)
{
  @Nat.0
}
"""
        result = _test(source, trials=20)
        f = _fn_result(result, "nat_fn")
        assert f.category == "tested"
        assert f.trials_failed == 0


# =====================================================================
# --fn filter
# =====================================================================


class TestFnFilter:
    """The fn_name parameter should filter to a single function."""

    def test_filter_one_function(self) -> None:
        source = """\
public fn add1(@Int -> @Int)
  requires(true)
  ensures(@Int.result == @Int.0 + 1)
  effects(pure)
{
  @Int.0 + 1
}

public fn add2(@Int -> @Int)
  requires(true)
  ensures(@Int.result == @Int.0 + 2)
  effects(pure)
{
  @Int.0 + 2
}
"""
        result = _test(source, fn_name="add1")
        names = [f.fn_name for f in result.functions]
        assert "add1" in names
        assert "add2" not in names


# =====================================================================
# Summary counts
# =====================================================================


class TestSummaryAggregation:
    """Verify the summary aggregates are correct."""

    def test_mixed_program(self) -> None:
        """A program with verified, tested, and skipped functions."""
        source = """\
public fn proved(@Int -> @Int)
  requires(true)
  ensures(@Int.result == @Int.0 + 1)
  effects(pure)
{
  @Int.0 + 1
}

public fn tested_fn(@Nat -> @Nat)
  requires(true)
  ensures(true)
  decreases(0)
  effects(pure)
{
  @Nat.0
}

public forall<T> fn generic_fn(@T -> @T)
  requires(true) ensures(true) effects(pure)
{ @T.0 }
"""
        result = _test(source, trials=10)
        s = result.summary
        # proved → verified (Tier 1)
        assert s.verified >= 1
        # tested_fn → tested (Tier 3 due to unverifiable decreases(0))
        assert s.tested >= 1
        # generic_fn → skipped
        assert s.skipped >= 1
