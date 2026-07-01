"""Tests for vera.codegen — numeric (math builtins, numeric type conversions, Float64 predicates and constants).

Split from tests/test_codegen.py (#419). Shared helpers live in tests/codegen_helpers.py.
"""
from __future__ import annotations

import re


from vera.codegen import (
    execute,
)

from tests.codegen_helpers import (
    _compile_ok,
    _run,
    _run_float,
    _run_io,
)


# =====================================================================
# Numeric math builtins (#199)
# =====================================================================


class TestAbs:
    """abs(@Int -> @Nat) — absolute value."""

    def test_positive(self) -> None:
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Nat = abs(42);
  @Nat.0
}
"""
        assert _run(src) == 42

    def test_negative(self) -> None:
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Nat = abs(-42);
  @Nat.0
}
"""
        assert _run(src) == 42

    def test_zero(self) -> None:
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Nat = abs(0);
  @Nat.0
}
"""
        assert _run(src) == 0


class TestMinMax:
    """min/max(@Int, @Int -> @Int) — minimum/maximum."""

    def test_min_basic(self) -> None:
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  min(3, 7)
}
"""
        assert _run(src) == 3

    def test_min_negative(self) -> None:
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  min(-5, 3)
}
"""
        assert _run(src) == -5

    def test_min_equal(self) -> None:
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  min(4, 4)
}
"""
        assert _run(src) == 4

    def test_max_basic(self) -> None:
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  max(3, 7)
}
"""
        assert _run(src) == 7

    def test_max_negative(self) -> None:
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  max(-5, 3)
}
"""
        assert _run(src) == 3

    def test_max_equal(self) -> None:
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  max(4, 4)
}
"""
        assert _run(src) == 4


class TestFloorCeilRound:
    """floor/ceil/round(@Float64 -> @Int)."""

    def test_floor_positive(self) -> None:
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  floor(3.7)
}
"""
        assert _run(src) == 3

    def test_floor_negative(self) -> None:
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  floor(-1.5)
}
"""
        assert _run(src) == -2

    def test_floor_exact(self) -> None:
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  floor(5.0)
}
"""
        assert _run(src) == 5

    def test_ceil_positive(self) -> None:
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  ceil(3.2)
}
"""
        assert _run(src) == 4

    def test_ceil_negative(self) -> None:
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  ceil(-1.5)
}
"""
        assert _run(src) == -1

    def test_ceil_exact(self) -> None:
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  ceil(5.0)
}
"""
        assert _run(src) == 5

    def test_round_up(self) -> None:
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  round(3.7)
}
"""
        assert _run(src) == 4

    def test_round_down(self) -> None:
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  round(3.2)
}
"""
        assert _run(src) == 3

    def test_round_half_even(self) -> None:
        # WASM f64.nearest uses banker's rounding (IEEE 754 roundTiesToEven)
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  round(2.5)
}
"""
        assert _run(src) == 2

    def test_round_negative(self) -> None:
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  round(-1.5)
}
"""
        assert _run(src) == -2


class TestSqrt:
    """sqrt(@Float64 -> @Float64)."""

    def test_basic(self) -> None:
        src = """
public fn f(-> @Float64) requires(true) ensures(true) effects(pure) {
  sqrt(4.0)
}
"""
        assert _run_float(src) == 2.0

    def test_zero(self) -> None:
        src = """
public fn f(-> @Float64) requires(true) ensures(true) effects(pure) {
  sqrt(0.0)
}
"""
        assert _run_float(src) == 0.0

    def test_one(self) -> None:
        src = """
public fn f(-> @Float64) requires(true) ensures(true) effects(pure) {
  sqrt(1.0)
}
"""
        assert _run_float(src) == 1.0

    def test_non_perfect(self) -> None:
        import math
        src = """
public fn f(-> @Float64) requires(true) ensures(true) effects(pure) {
  sqrt(2.0)
}
"""
        assert abs(_run_float(src) - math.sqrt(2.0)) < 1e-10


class TestPow:
    """pow(@Float64, @Int -> @Float64)."""

    def test_basic(self) -> None:
        src = """
public fn f(-> @Float64) requires(true) ensures(true) effects(pure) {
  pow(2.0, 10)
}
"""
        assert _run_float(src) == 1024.0

    def test_zero_exponent(self) -> None:
        src = """
public fn f(-> @Float64) requires(true) ensures(true) effects(pure) {
  pow(5.0, 0)
}
"""
        assert _run_float(src) == 1.0

    def test_one_exponent(self) -> None:
        src = """
public fn f(-> @Float64) requires(true) ensures(true) effects(pure) {
  pow(3.0, 1)
}
"""
        assert _run_float(src) == 3.0

    def test_square(self) -> None:
        src = """
public fn f(-> @Float64) requires(true) ensures(true) effects(pure) {
  pow(7.0, 2)
}
"""
        assert _run_float(src) == 49.0

    def test_negative_exponent(self) -> None:
        src = """
public fn f(-> @Float64) requires(true) ensures(true) effects(pure) {
  pow(2.0, -1)
}
"""
        assert _run_float(src) == 0.5


class TestMathBuiltins:
    """Tests for math built-ins (#467).

    Fifteen functions across four groups:
    - Logarithmic (host-imported): ``log``, ``log2``, ``log10``
    - Trigonometric (host-imported): ``sin``, ``cos``, ``tan``,
      ``asin``, ``acos``, ``atan``, ``atan2``
    - Constants (inlined as ``f64.const``): ``pi``, ``e``
    - Utilities (inlined WAT): ``sign``, ``clamp``, ``float_clamp``

    Tests focus on exact identities (``log(e()) == 1``, ``sin(0)
    == 0``), boundary / domain edge cases, and WAT
    import-gating — the 10 host-imported ops must appear in
    ``result.wat`` only when used.
    """

    def test_log_identities(self) -> None:
        """log(e()) == 1; log2(2) == 1; log10(10) == 1."""
        source = """\
public fn main(-> @Float64)
  requires(true) ensures(true) effects(pure)
{
  log(e()) + log2(2.0) + log10(10.0)
}
"""
        result = _compile_ok(source)
        # Only the three log imports, no trig imports emitted.
        # Use regex with a trailing non-digit requirement so the
        # substring ``$vera.log`` doesn't false-match on
        # ``$vera.log2`` or ``$vera.log10``.
        assert re.search(r"\$vera\.log(?!\d)", result.wat)
        assert "$vera.log2" in result.wat
        assert "$vera.log10" in result.wat
        assert "$vera.sin" not in result.wat
        assert "$vera.atan2" not in result.wat
        # Each identity = 1.0; sum = 3.0.
        v = execute(result, fn_name="main").value
        assert abs(v - 3.0) < 1e-10, f"expected ≈3.0, got {v}"

    def test_sin_cos_tan_at_zero(self) -> None:
        """sin(0) == 0, cos(0) == 1, tan(0) == 0."""
        source = """\
public fn main(-> @Float64)
  requires(true) ensures(true) effects(pure)
{
  sin(0.0) + cos(0.0) + tan(0.0)
}
"""
        result = _compile_ok(source)
        assert "$vera.sin" in result.wat
        assert "$vera.cos" in result.wat
        assert "$vera.tan" in result.wat
        assert "$vera.log" not in result.wat
        v = execute(result, fn_name="main").value
        # 0 + 1 + 0 = 1
        assert abs(v - 1.0) < 1e-10

    def test_inverse_trig_at_known_points(self) -> None:
        """asin(0)==0, acos(1)==0, atan2(0.5, 1.0) == atan(0.5).

        Each expression exercises a distinct host import.  The final
        identity uses *asymmetric* arguments — `atan2(0.5, 1.0)`
        equals `atan(0.5/1.0) = atan(0.5)` only when the POSIX
        `atan2(y, x)` argument order is respected.  A swapped
        implementation that treated the Vera call as `atan2(x, y)`
        internally would compute `atan(1.0/0.5) = atan(2.0)`, which
        differs from `atan(0.5)` by about 0.6 radians and fails the
        assertion immediately.  Symmetric inputs (`atan2(1, 1)`)
        would mask this bug.
        """
        source = """\
public fn main(-> @Float64)
  requires(true) ensures(true) effects(pure)
{
  asin(0.0) + acos(1.0) + (atan2(0.5, 1.0) - atan(0.5))
}
"""
        result = _compile_ok(source)
        assert "$vera.asin" in result.wat
        assert "$vera.acos" in result.wat
        assert "$vera.atan" in result.wat
        assert "$vera.atan2" in result.wat
        v = execute(result, fn_name="main").value
        # asin(0) = 0, acos(1) = 0,
        # atan2(0.5, 1.0) - atan(0.5) = 0 in exact arithmetic (POSIX
        # argument order).  The host implementations round
        # independently, so the final sum is within one ULP of zero
        # rather than bit-exact — still small enough to catch a
        # swapped `atan2(x, y)` implementation, which would miss by
        # roughly 0.6 radians.
        assert abs(v) < 1e-15, (
            f"inverse-trig identity broken (possible swapped atan2 args): {v}"
        )

    def test_pi_and_e_constants(self) -> None:
        """pi() and e() return known high-precision constants.

        Values must round-trip to 17 digits so Python and browser
        runtimes produce identical results.  pi() is inlined as
        ``f64.const 3.141592653589793`` — no host call, no import.
        """
        import math
        source_pi = """\
public fn main(-> @Float64)
  requires(true) ensures(true) effects(pure)
{ pi() }
"""
        source_e = """\
public fn main(-> @Float64)
  requires(true) ensures(true) effects(pure)
{ e() }
"""
        pi_result = _compile_ok(source_pi)
        e_result = _compile_ok(source_e)
        # Inlined — no host import should be emitted.
        assert "$vera.pi" not in pi_result.wat
        assert "$vera.e" not in e_result.wat
        assert execute(pi_result, fn_name="main").value == math.pi
        assert execute(e_result, fn_name="main").value == math.e

    def test_sign(self) -> None:
        """sign(x) returns -1 for negative, 0 for zero, 1 for positive.

        Covers all three branches of the inline
        ``(x > 0) - (x < 0)`` encoding.  No host import needed.
        """
        for x, expected in [(-42, -1), (-1, -1), (0, 0), (1, 1), (9999, 1)]:
            source = f"""\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{{ sign({x}) }}
"""
            result = _compile_ok(source)
            assert "$vera.sign" not in result.wat  # inlined
            v = execute(result, fn_name="main").value
            assert v == expected, f"sign({x}): expected {expected}, got {v}"

    def test_clamp_int(self) -> None:
        """clamp(v, lo, hi) = min(max(v, lo), hi).

        Covers the three branches (below lo / in range / above hi)
        plus the signed-integer handling that clamp's `gt_s`/`lt_s`
        comparisons depend on.  `clamp(-10, -5, 5) == -5` checks
        negative inputs work.
        """
        cases = [
            # (v, lo, hi, expected)
            (5, 0, 10, 5),      # within range → v
            (-3, 0, 10, 0),     # below lo → lo
            (15, 0, 10, 10),    # above hi → hi
            (-10, -5, 5, -5),   # negative range, below
            (100, -5, 5, 5),    # negative range, above
            (7, 7, 7, 7),       # singleton (lo == hi == v)
            (0, 0, 0, 0),       # zero singleton
            # Inverted bounds (lo > hi): the min(max()) formulation
            # pins to ``hi`` regardless of ``v``.  Callers passing
            # ``lo > hi`` are outside the contract, but we document
            # the fallthrough behavior so changes to the WAT
            # sequence get caught.
            (5, 10, 0, 0),      # v in [hi, lo] → hi
            (-5, 10, 0, 0),     # v below hi → hi
            (100, 10, 0, 0),    # v above lo → hi
        ]
        for v, lo, hi, expected in cases:
            source = f"""\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{{ clamp({v}, {lo}, {hi}) }}
"""
            result = _compile_ok(source)
            got = execute(result, fn_name="main").value
            assert got == expected, (
                f"clamp({v}, {lo}, {hi}): expected {expected}, got {got}"
            )

    def test_float_clamp(self) -> None:
        """float_clamp covers floating-point clamp semantics.

        Uses ``f64.max`` / ``f64.min`` natively (no host call).
        Worth testing: out-of-range, in-range, and that the
        ordering isn't flipped by IEEE-754 quirks.
        """
        cases = [
            (0.5, 0.0, 1.0, 0.5),
            (3.5, 0.0, 1.0, 1.0),
            (-3.5, 0.0, 1.0, 0.0),
            (-1.5, -2.0, -1.0, -1.5),  # negative in-range
            # Inverted bounds (lo > hi): mirrors the integer case —
            # ``f64.min(f64.max(v, lo), hi) == hi`` whenever lo > hi.
            (0.5, 1.0, 0.0, 0.0),
            (-1.0, 1.0, 0.0, 0.0),
            (5.0, 1.0, 0.0, 0.0),
        ]
        for v, lo, hi, expected in cases:
            source = f"""\
public fn main(-> @Float64)
  requires(true) ensures(true) effects(pure)
{{ float_clamp({v}, {lo}, {hi}) }}
"""
            result = _compile_ok(source)
            got = execute(result, fn_name="main").value
            assert got == expected, (
                f"float_clamp({v}, {lo}, {hi}): expected {expected}, got {got}"
            )

    def test_math_domain_nan(self) -> None:
        """Out-of-domain inputs return NaN under the Python wasmtime target.

        Mirrors the browser-side ``test_domain_edges_nan`` parity check
        so the two runtimes can be compared directly.  The Python host
        wrapper in ``vera/codegen/api.py::_math_unary_host`` catches
        ``math.log``'s ``ValueError`` and returns ``float("nan")``;
        without that translation this test would trap with a host-
        callback error and fail loudly rather than producing NaN.
        """
        import math as _math

        cases = [
            ("log(-1.0)",  "log"),
            ("asin(2.0)",  "asin"),
            ("acos(2.0)",  "acos"),
        ]
        for expr, _op in cases:
            source = f"""\
public fn main(-> @Float64)
  requires(true) ensures(true) effects(pure)
{{ {expr} }}
"""
            result = _compile_ok(source)
            v = execute(result, fn_name="main").value
            assert _math.isnan(v), f"{expr}: expected NaN, got {v}"

    def test_math_ops_gated_when_unused(self) -> None:
        """A module that uses no math builtins emits no math imports.

        Regression for the gating: if ``_math_ops_used`` was ever
        populated unconditionally, every compiled module would
        import all 10 host functions — a 10% size bloat for
        programs that don't use them.  Compile a trivial pure
        program and assert none of the 10 math imports appear.
        """
        source = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ 42 }
"""
        result = _compile_ok(source)
        for op in (
            "log", "log2", "log10", "sin", "cos", "tan",
            "asin", "acos", "atan", "atan2",
        ):
            assert f"$vera.{op}" not in result.wat, (
                f"${op} import leaked into unrelated program"
            )


# =====================================================================
# Numeric type conversions (issue #208)
# =====================================================================


class TestIntToFloat:
    """int_to_float(@Int -> @Float64)."""

    def test_positive(self) -> None:
        src = """
public fn f(-> @Float64) requires(true) ensures(true) effects(pure) {
  int_to_float(42)
}
"""
        assert _run_float(src) == 42.0

    def test_negative(self) -> None:
        src = """
public fn f(-> @Float64) requires(true) ensures(true) effects(pure) {
  int_to_float(0 - 7)
}
"""
        assert _run_float(src) == -7.0

    def test_zero(self) -> None:
        src = """
public fn f(-> @Float64) requires(true) ensures(true) effects(pure) {
  int_to_float(0)
}
"""
        assert _run_float(src) == 0.0


class TestFloatToInt:
    """float_to_int(@Float64 -> @Int) — truncation toward zero."""

    def test_positive_truncate(self) -> None:
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  float_to_int(3.7)
}
"""
        assert _run(src) == 3

    def test_negative_truncate(self) -> None:
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  float_to_int(0.0 - 3.7)
}
"""
        assert _run(src) == -3

    def test_exact(self) -> None:
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  float_to_int(5.0)
}
"""
        assert _run(src) == 5

    def test_zero(self) -> None:
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  float_to_int(0.0)
}
"""
        assert _run(src) == 0


class TestNatToInt:
    """nat_to_int(@Nat -> @Int) — identity (both i64)."""

    def test_basic(self) -> None:
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  nat_to_int(abs(42))
}
"""
        assert _run(src) == 42

    def test_zero(self) -> None:
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  nat_to_int(abs(0))
}
"""
        assert _run(src) == 0

    def test_large(self) -> None:
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  nat_to_int(abs(999999))
}
"""
        assert _run(src) == 999999


class TestIntToNat:
    """int_to_nat(@Int -> @Option<Nat>) — checked narrowing."""

    def test_positive(self) -> None:
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  match int_to_nat(42) {
    Some(@Nat) -> nat_to_int(@Nat.0),
    None -> 0 - 1
  }
}
"""
        assert _run(src) == 42

    def test_zero(self) -> None:
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  match int_to_nat(0) {
    Some(@Nat) -> nat_to_int(@Nat.0),
    None -> 0 - 1
  }
}
"""
        assert _run(src) == 0

    def test_negative_returns_none(self) -> None:
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  match int_to_nat(0 - 5) {
    Some(@Nat) -> nat_to_int(@Nat.0),
    None -> 0 - 1
  }
}
"""
        assert _run(src) == -1

    def test_large_positive(self) -> None:
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  match int_to_nat(1000000) {
    Some(@Nat) -> nat_to_int(@Nat.0),
    None -> 0 - 1
  }
}
"""
        assert _run(src) == 1000000


class TestByteToInt:
    """byte_to_int(@Byte -> @Int) — zero extension."""

    def test_basic(self) -> None:
        src = """
public fn f(@Byte -> @Int) requires(true) ensures(true) effects(pure) {
  byte_to_int(@Byte.0)
}
"""
        assert _run(src, fn="f", args=[65]) == 65

    def test_zero(self) -> None:
        src = """
public fn f(@Byte -> @Int) requires(true) ensures(true) effects(pure) {
  byte_to_int(@Byte.0)
}
"""
        assert _run(src, fn="f", args=[0]) == 0

    def test_max(self) -> None:
        src = """
public fn f(@Byte -> @Int) requires(true) ensures(true) effects(pure) {
  byte_to_int(@Byte.0)
}
"""
        assert _run(src, fn="f", args=[255]) == 255


class TestIntToByte:
    """int_to_byte(@Int -> @Option<Byte>) — checked narrowing."""

    def test_valid(self) -> None:
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  match int_to_byte(65) {
    Some(@Byte) -> byte_to_int(@Byte.0),
    None -> 0 - 1
  }
}
"""
        assert _run(src) == 65

    def test_zero(self) -> None:
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  match int_to_byte(0) {
    Some(@Byte) -> byte_to_int(@Byte.0),
    None -> 0 - 1
  }
}
"""
        assert _run(src) == 0

    def test_max_byte(self) -> None:
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  match int_to_byte(255) {
    Some(@Byte) -> byte_to_int(@Byte.0),
    None -> 0 - 1
  }
}
"""
        assert _run(src) == 255

    def test_negative_returns_none(self) -> None:
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  match int_to_byte(0 - 1) {
    Some(@Byte) -> byte_to_int(@Byte.0),
    None -> 0 - 1
  }
}
"""
        assert _run(src) == -1

    def test_overflow_returns_none(self) -> None:
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  match int_to_byte(256) {
    Some(@Byte) -> byte_to_int(@Byte.0),
    None -> 0 - 1
  }
}
"""
        assert _run(src) == -1


class TestTypeConversionRoundTrip:
    """Round-trip and composition tests for type conversions."""

    def test_int_float_roundtrip(self) -> None:
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  float_to_int(int_to_float(42))
}
"""
        assert _run(src) == 42

    def test_nat_int_roundtrip(self) -> None:
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  match int_to_nat(nat_to_int(abs(7))) {
    Some(@Nat) -> nat_to_int(@Nat.0),
    None -> 0 - 1
  }
}
"""
        assert _run(src) == 7

    def test_byte_int_roundtrip(self) -> None:
        src = """
public fn f(@Byte -> @Int) requires(true) ensures(true) effects(pure) {
  match int_to_byte(byte_to_int(@Byte.0)) {
    Some(@Byte) -> byte_to_int(@Byte.0),
    None -> 0 - 1
  }
}
"""
        assert _run(src, fn="f", args=[100]) == 100

    def test_nat_to_float(self) -> None:
        """Chain nat_to_int then int_to_float."""
        src = """
public fn f(-> @Float64) requires(true) ensures(true) effects(pure) {
  int_to_float(nat_to_int(abs(10)))
}
"""
        assert _run_float(src) == 10.0


# =====================================================================
# Float64 predicates and constants (#212)
# =====================================================================


class TestFloatIsNan:
    """End-to-end tests for float_is_nan builtin."""

    def test_regular_float_not_nan(self) -> None:
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  if float_is_nan(1.5) then { 1 } else { 0 }
}
"""
        assert _run(src) == 0

    def test_nan_is_nan(self) -> None:
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  if float_is_nan(nan()) then { 1 } else { 0 }
}
"""
        assert _run(src) == 1

    def test_infinity_not_nan(self) -> None:
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  if float_is_nan(infinity()) then { 1 } else { 0 }
}
"""
        assert _run(src) == 0

    def test_zero_not_nan(self) -> None:
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  if float_is_nan(0.0) then { 1 } else { 0 }
}
"""
        assert _run(src) == 0


class TestFloatIsInfinite:
    """End-to-end tests for float_is_infinite builtin."""

    def test_regular_float_not_infinite(self) -> None:
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  if float_is_infinite(1.5) then { 1 } else { 0 }
}
"""
        assert _run(src) == 0

    def test_positive_infinity(self) -> None:
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  if float_is_infinite(infinity()) then { 1 } else { 0 }
}
"""
        assert _run(src) == 1

    def test_negative_infinity(self) -> None:
        """Negate infinity to get -inf, still infinite."""
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  if float_is_infinite(0.0 - infinity()) then { 1 } else { 0 }
}
"""
        assert _run(src) == 1

    def test_nan_not_infinite(self) -> None:
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  if float_is_infinite(nan()) then { 1 } else { 0 }
}
"""
        assert _run(src) == 0

    def test_zero_not_infinite(self) -> None:
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  if float_is_infinite(0.0) then { 1 } else { 0 }
}
"""
        assert _run(src) == 0


class TestNanConstant:
    """End-to-end tests for nan() builtin."""

    def test_nan_returns_float(self) -> None:
        import math
        src = """
public fn f(-> @Float64) requires(true) ensures(true) effects(pure) {
  nan()
}
"""
        result = _run_float(src)
        assert math.isnan(result)

    def test_nan_not_equal_to_itself(self) -> None:
        """NaN != NaN is the defining property of NaN."""
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  if nan() == nan() then { 1 } else { 0 }
}
"""
        assert _run(src) == 0


class TestInfinityConstant:
    """End-to-end tests for infinity() builtin."""

    def test_infinity_returns_float(self) -> None:
        import math
        src = """
public fn f(-> @Float64) requires(true) ensures(true) effects(pure) {
  infinity()
}
"""
        result = _run_float(src)
        assert math.isinf(result) and result > 0

    def test_negative_infinity(self) -> None:
        import math
        src = """
public fn f(-> @Float64) requires(true) ensures(true) effects(pure) {
  0.0 - infinity()
}
"""
        result = _run_float(src)
        assert math.isinf(result) and result < 0


class TestFloatPredicateRoundTrips:
    """Composition and round-trip tests for float predicates."""

    def test_float_is_nan_of_nan(self) -> None:
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  if float_is_nan(nan()) then { 1 } else { 0 }
}
"""
        assert _run(src) == 1

    def test_float_is_infinite_of_infinity(self) -> None:
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  if float_is_infinite(infinity()) then { 1 } else { 0 }
}
"""
        assert _run(src) == 1

    def test_float_is_nan_after_arithmetic(self) -> None:
        """nan + anything = nan."""
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  if float_is_nan(nan() + 1.0) then { 1 } else { 0 }
}
"""
        assert _run(src) == 1

    def test_float_is_infinite_after_arithmetic(self) -> None:
        """infinity + 1 = infinity."""
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  if float_is_infinite(infinity() + 1.0) then { 1 } else { 0 }
}
"""
        assert _run(src) == 1


class TestToStringInt64Min475:
    """`#475` finding 9: `int_to_string(INT64_MIN)` correct.

    Pre-fix, `_translate_to_string` extracted digits via signed
    `i64.le_s 0` as the loop break, which on the first iteration
    of negation `-INT64_MIN` overflows back to `INT64_MIN` (still
    `< 0`) and prints partial garbage.

    Post-fix, the loop break uses unsigned `i64.eqz` after digit
    extraction with `i64.div_u` / `i64.rem_u`, so the unsigned
    bit pattern walks down to zero correctly.
    """

    def test_int64_min_to_string(self) -> None:
        """`int_to_string(-9223372036854775808)` → exact decimal."""
        src = """
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print(int_to_string(-9223372036854775808))
}
"""
        assert _run_io(src).strip() == "-9223372036854775808"

    def test_negative_basic(self) -> None:
        """Sanity: `int_to_string(-42)` → '-42'."""
        src = """
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print(int_to_string(-42))
}
"""
        assert _run_io(src).strip() == "-42"


class TestFloatToStringCarry475:
    """`#475` finding 10: `float_to_string` handles fraction-rounding carry.

    Pre-fix, the integer part was written first, then the
    fractional `frac_val = round((f - floor(f)) * 1_000_000)`
    was computed.  When the fraction rounded up to exactly
    1_000_000, the integer part was already on the page — output
    `1.000000` instead of `2.000000`.

    Post-fix, frac_val is computed first; when it equals 1_000_000
    we increment ival and reset frac_val to 0 before emitting any
    digits.
    """

    def test_carry_propagates(self) -> None:
        """`1.9999996 → "2.0"` (frac rounds up to 1_000_000, trailing zeros trimmed).

        Pre-fix this printed "1.0" — the integer part was emitted
        before the carry was detected, so the rounded-up fraction
        couldn't propagate.
        """
        src = """
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print(float_to_string(1.9999996))
}
"""
        assert _run_io(src).strip() == "2.0"

    def test_normal_fraction(self) -> None:
        """Baseline: `1.5 → "1.5"` (trailing zeros trimmed by format)."""
        src = """
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print(float_to_string(1.5))
}
"""
        assert _run_io(src).strip() == "1.5"

    def test_full_six_decimals_when_significant(self) -> None:
        """When fraction has 6 significant digits, all are kept."""
        src = """
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print(float_to_string(0.123456))
}
"""
        assert _run_io(src).strip() == "0.123456"
