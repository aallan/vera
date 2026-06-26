"""Runtime overflow-trap codegen tests for #798 (Stage 3).

Stage 2 made the verifier emit an ``int_overflow`` obligation at every
``@Int`` / ``@Nat`` ``+`` / ``-`` / ``*`` site (``@Nat`` subtraction is the
separate ``nat_sub`` underflow, excluded).  Stage 3 (this file) makes the
codegen emit a runtime guard at *exactly* those sites so ``vera run`` /
``vera compile`` programs trap on overflow instead of silently wrapping at the
i64 / u64 boundary.

The trap is a bare ``unreachable`` (Option A in the design doc — matches the
#520 ``nat_sub`` and #552 nat-bind precedent), so it classifies as
``kind="unreachable"`` today.  A precise ``"overflow"`` trap kind via a host
import is a deliberate follow-up.

Written test-first: every ``*_traps`` test FAILS on the pre-Stage-3 codegen
(the op wraps silently → no trap → ``execute`` returns a value), and every
``*_no_trap`` test passes both before and after (safe arithmetic is unchanged).

Constants:
    I64_MAX = 9223372036854775807   ( 2^63 - 1 )
    I64_MIN = -9223372036854775808  (-2^63 )
    U64_MAX = 18446744073709551615  ( 2^64 - 1 )
"""

from __future__ import annotations

import tempfile
from pathlib import Path

import pytest
import wasmtime

from vera.checker import typecheck_with_artifacts
from vera.codegen import compile as codegen_compile
from vera.codegen import execute
from vera.parser import parse_to_ast

I64_MAX = 9223372036854775807
I64_MIN = -9223372036854775808
U64_MAX = 18446744073709551615


def _compile_with_types(source: str):
    """Compile via the same artifact-threaded path as ``cmd_run``.

    The overflow guard's Int/Nat classifier consults the checker's resolved
    type table (``expr_semantic_types``), so codegen must be handed it — a bare
    ``transform -> compile`` (no typecheck) would leave the table empty and the
    classifier blind, exactly the gap the verifier<->codegen differential pins.
    """
    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".vera", delete=False, encoding="utf-8",
    ) as f:
        f.write(source)
        path = f.name
    try:
        ast = parse_to_ast(source)
        diags, arts = typecheck_with_artifacts(ast, source, file=path)
        errors = [d for d in diags if d.severity == "error"]
        assert not errors, f"typecheck errors: {[d.description for d in errors]}"
        result = codegen_compile(
            ast, source=source, file=path,
            expr_semantic_types=arts.expr_semantic_types,
        )
        errs = [d for d in result.diagnostics if d.severity == "error"]
        assert not errs, f"codegen errors: {[d.description for d in errs]}"
        return result
    finally:
        Path(path).unlink(missing_ok=True)


_MASK64 = (1 << 64) - 1


def _run(source: str, fn: str, args: list[int]) -> int:
    result = _compile_with_types(source)
    exec_result = execute(result, fn_name=fn, args=args)
    assert exec_result.value is not None
    return exec_result.value


def _assert_traps(source: str, fn: str, args: list[int]) -> None:
    """Assert running ``fn(args)`` traps at the WASM level (overflow guard)."""
    result = _compile_with_types(source)
    with pytest.raises(
        (wasmtime.WasmtimeError, wasmtime.Trap, RuntimeError)
    ):
        execute(result, fn_name=fn, args=args)


def _assert_no_trap(source: str, fn: str, args: list[int], expect: int) -> None:
    # wasmtime returns i64 results signed; a @Nat value above 2^63 comes back
    # negative.  Compare modulo 2^64 so the unsigned intent is checked without
    # caring how the host marshals the sign bit.
    assert _run(source, fn, args) & _MASK64 == expect & _MASK64


# Dynamic-operand fixtures: args reach the runtime guard (the verifier honestly
# defers to Tier 3, so the guard is what fires — not a verify-time E528).
_INT_ADD = """
public fn add(@Int, @Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.1 + @Int.0 }
"""

_INT_SUB = """
public fn sub(@Int, @Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.1 - @Int.0 }
"""

_INT_MUL = """
public fn mul(@Int, @Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.1 * @Int.0 }
"""

_NAT_ADD = """
public fn add(@Nat, @Nat -> @Nat)
  requires(true) ensures(true) effects(pure)
{ @Nat.1 + @Nat.0 }
"""

_NAT_MUL = """
public fn mul(@Nat, @Nat -> @Nat)
  requires(true) ensures(true) effects(pure)
{ @Nat.1 * @Nat.0 }
"""


# Literal-LEFT @Int: the site is classified on the EXPRESSION's resolved type
# (@Int / i64), not the literal's @Nat self-type — so the overflow is caught
# (#798 RISK-6 fix).
_INT_LITERAL_LEFT = """
public fn f(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ 5 + @Int.0 }
"""


class TestLiteralLeftIntOverflow798:
    """A positive-literal LEFT operand of an @Int add is guarded at the i64
    range — the literal's own @Nat self-type must not widen the site to u64."""

    def test_literal_left_int_add_traps_at_i64_range(self) -> None:
        # 5 + I64_MAX = 2^63 + 4 overflows i64 → must trap.  Were the site
        # mis-classified @Nat (u64), 2^63+4 would be "in range" and slip through.
        _assert_traps(_INT_LITERAL_LEFT, "f", [I64_MAX])

    def test_literal_left_small_sum_no_trap(self) -> None:
        _assert_no_trap(_INT_LITERAL_LEFT, "f", [10], 15)


class TestIntAddOverflow798:
    """@Int ADD traps on i64 overflow; safe sums pass through."""

    def test_max_plus_one_traps(self) -> None:
        _assert_traps(_INT_ADD, "add", [I64_MAX, 1])

    def test_max_plus_max_traps(self) -> None:
        _assert_traps(_INT_ADD, "add", [I64_MAX, I64_MAX])

    def test_min_plus_neg_one_traps(self) -> None:
        _assert_traps(_INT_ADD, "add", [I64_MIN, -1])

    def test_max_plus_zero_no_trap(self) -> None:
        _assert_no_trap(_INT_ADD, "add", [I64_MAX, 0], I64_MAX)

    def test_small_sum_no_trap(self) -> None:
        _assert_no_trap(_INT_ADD, "add", [5, 3], 8)

    def test_min_plus_max_is_neg_one_no_trap(self) -> None:
        # Operands differ in sign → cannot overflow → must NOT trap.
        _assert_no_trap(_INT_ADD, "add", [I64_MIN, I64_MAX], -1)


class TestIntSubOverflow798:
    """@Int SUB is order-sensitive; the guard pins minuend - subtrahend."""

    def test_min_minus_one_traps(self) -> None:
        # add args are (first=@Int.1, second=@Int.0); body is @Int.1 - @Int.0,
        # so sub(a, b) computes a - b.
        _assert_traps(_INT_SUB, "sub", [I64_MIN, 1])

    def test_max_minus_neg_one_traps(self) -> None:
        _assert_traps(_INT_SUB, "sub", [I64_MAX, -1])

    def test_zero_minus_min_traps(self) -> None:
        # 0 - I64_MIN = 2^63, overflows.
        _assert_traps(_INT_SUB, "sub", [0, I64_MIN])

    def test_min_minus_min_is_zero_no_trap(self) -> None:
        _assert_no_trap(_INT_SUB, "sub", [I64_MIN, I64_MIN], 0)

    def test_max_minus_max_is_zero_no_trap(self) -> None:
        _assert_no_trap(_INT_SUB, "sub", [I64_MAX, I64_MAX], 0)

    def test_small_diff_no_trap(self) -> None:
        _assert_no_trap(_INT_SUB, "sub", [5, 3], 2)


class TestIntMulOverflow798:
    """@Int MUL is the dangerous one — INT_MIN/-1 and 0 special cases."""

    def test_min_times_neg_one_traps(self) -> None:
        # The special case: I64_MIN * -1 = 2^63 overflows.  MUST trap and MUST
        # NOT surface as a native i64.div_s INT_MIN/-1 trap.
        _assert_traps(_INT_MUL, "mul", [I64_MIN, -1])

    def test_neg_one_times_min_traps(self) -> None:
        # Symmetric operand order — both must trap.
        _assert_traps(_INT_MUL, "mul", [-1, I64_MIN])

    def test_max_times_two_traps(self) -> None:
        _assert_traps(_INT_MUL, "mul", [I64_MAX, 2])

    def test_min_times_two_traps(self) -> None:
        _assert_traps(_INT_MUL, "mul", [I64_MIN, 2])

    def test_two_pow_32_squared_traps(self) -> None:
        _assert_traps(_INT_MUL, "mul", [2**32, 2**32])

    def test_zero_times_min_no_trap(self) -> None:
        # The a==0 branch — without it, r/a is 0/0 → div-by-zero (wrong trap).
        _assert_no_trap(_INT_MUL, "mul", [0, I64_MIN], 0)

    def test_min_times_zero_no_trap(self) -> None:
        _assert_no_trap(_INT_MUL, "mul", [I64_MIN, 0], 0)

    def test_one_times_max_no_trap(self) -> None:
        _assert_no_trap(_INT_MUL, "mul", [1, I64_MAX], I64_MAX)

    def test_neg_one_times_max_no_trap(self) -> None:
        # -1 * I64_MAX = I64_MIN + 1, in range.
        _assert_no_trap(_INT_MUL, "mul", [-1, I64_MAX], I64_MIN + 1)

    def test_min_times_one_no_trap(self) -> None:
        _assert_no_trap(_INT_MUL, "mul", [I64_MIN, 1], I64_MIN)

    def test_two_pow_31_squared_no_trap(self) -> None:
        # 2^31 * 2^31 = 2^62, in range.
        _assert_no_trap(_INT_MUL, "mul", [2**31, 2**31], 2**62)

    def test_small_product_no_trap(self) -> None:
        _assert_no_trap(_INT_MUL, "mul", [3, 5], 15)


class TestNatAddOverflow798:
    """@Nat ADD traps on u64 carry-out."""

    def test_max_plus_one_traps(self) -> None:
        _assert_traps(_NAT_ADD, "add", [U64_MAX, 1])

    def test_max_plus_max_traps(self) -> None:
        _assert_traps(_NAT_ADD, "add", [U64_MAX, U64_MAX])

    def test_half_plus_half_traps(self) -> None:
        _assert_traps(_NAT_ADD, "add", [2**63, 2**63])

    def test_max_plus_zero_no_trap(self) -> None:
        _assert_no_trap(_NAT_ADD, "add", [U64_MAX, 0], U64_MAX)

    def test_small_sum_no_trap(self) -> None:
        _assert_no_trap(_NAT_ADD, "add", [5, 3], 8)

    def test_half_plus_half_minus_one_no_trap(self) -> None:
        # 2^63 + (2^63 - 1) = U64_MAX, exact.
        _assert_no_trap(_NAT_ADD, "add", [2**63, 2**63 - 1], U64_MAX)


class TestNatMulOverflow798:
    """@Nat MUL traps on u64 overflow; the a==0 branch dodges div-by-zero."""

    def test_max_times_two_traps(self) -> None:
        _assert_traps(_NAT_MUL, "mul", [U64_MAX, 2])

    def test_two_pow_32_squared_traps(self) -> None:
        _assert_traps(_NAT_MUL, "mul", [2**32, 2**32])

    def test_max_times_max_traps(self) -> None:
        _assert_traps(_NAT_MUL, "mul", [U64_MAX, U64_MAX])

    def test_zero_times_max_no_trap(self) -> None:
        # The a==0 branch — without it, 0/0 div-by-zero (wrong trap).
        _assert_no_trap(_NAT_MUL, "mul", [0, U64_MAX], 0)

    def test_one_times_max_no_trap(self) -> None:
        _assert_no_trap(_NAT_MUL, "mul", [1, U64_MAX], U64_MAX)

    def test_two_pow_32_times_below_no_trap(self) -> None:
        # 2^32 * (2^32 - 1) < 2^64.
        _assert_no_trap(_NAT_MUL, "mul", [2**32, 2**32 - 1], 2**32 * (2**32 - 1))

    def test_max_times_one_no_trap(self) -> None:
        _assert_no_trap(_NAT_MUL, "mul", [U64_MAX, 1], U64_MAX)


# =====================================================================
# RISK A — MUL round-trip soundness (design RISK 5)
# =====================================================================


def _traps(result, fn: str, args: list[int]) -> bool:
    """Run a precompiled module; return True iff it trapped (any WASM fault)."""
    try:
        execute(result, fn_name=fn, args=args)
        return False
    except (wasmtime.WasmtimeError, wasmtime.Trap, RuntimeError):
        return True


class TestMulRoundTripDifferential798:
    """The MUL division round-trip must trap on EXACTLY the overflowing
    products — no more, no less — checked against Python's exact ``*``.

    The single most error-prone line in the change (design RISK 5): if the
    round-trip ever disagrees with the true product's range, the MUL guard is
    unsound.  Compile each ``mul`` once, then sweep thousands of pseudo-random
    operand pairs (plus the hand-picked boundary values) and assert
    ``codegen-traps(a*b) <=> (a*b outside the i64 / u64 range)``.
    """

    _BOUNDARIES_SIGNED = [
        0, 1, -1, 2, -2, I64_MAX, I64_MIN, I64_MAX - 1, I64_MIN + 1,
        2**31, -(2**31), 2**32, -(2**32), 2**62, -(2**62),
    ]
    _BOUNDARIES_UNSIGNED = [
        0, 1, 2, 3, U64_MAX, U64_MAX - 1, 2**32, 2**32 - 1, 2**63, 2**63 - 1,
        2**31, 2**16,
    ]

    def test_int_mul_matches_python_exact(self) -> None:
        import random
        rng = random.Random(0x5EED798)
        result = _compile_with_types(_INT_MUL)
        # mul(a, b) computes @Int.1 * @Int.0 = first * second = a * b.
        pairs: list[tuple[int, int]] = []
        for a in self._BOUNDARIES_SIGNED:
            for b in self._BOUNDARIES_SIGNED:
                pairs.append((a, b))
        for _ in range(4000):
            pairs.append((
                rng.randint(I64_MIN, I64_MAX),
                rng.randint(I64_MIN, I64_MAX),
            ))
        mismatches: list[tuple[int, int, bool, bool]] = []
        for a, b in pairs:
            trapped = _traps(result, "mul", [a, b])
            overflows = not (I64_MIN <= a * b <= I64_MAX)
            if trapped != overflows:
                mismatches.append((a, b, trapped, overflows))
        assert not mismatches, (
            f"@Int MUL guard disagrees with Python exact product on "
            f"{len(mismatches)} of {len(pairs)} pairs (a, b, trapped, "
            f"overflows): {mismatches[:10]}"
        )

    def test_nat_mul_matches_python_exact(self) -> None:
        import random
        rng = random.Random(0xC0FFEE798)
        result = _compile_with_types(_NAT_MUL)
        pairs: list[tuple[int, int]] = []
        for a in self._BOUNDARIES_UNSIGNED:
            for b in self._BOUNDARIES_UNSIGNED:
                pairs.append((a, b))
        for _ in range(4000):
            pairs.append((
                rng.randint(0, U64_MAX),
                rng.randint(0, U64_MAX),
            ))
        mismatches: list[tuple[int, int, bool, bool]] = []
        for a, b in pairs:
            trapped = _traps(result, "mul", [a, b])
            overflows = a * b > U64_MAX
            if trapped != overflows:
                mismatches.append((a, b, trapped, overflows))
        assert not mismatches, (
            f"@Nat MUL guard disagrees with Python exact product on "
            f"{len(mismatches)} of {len(pairs)} pairs (a, b, trapped, "
            f"overflows): {mismatches[:10]}"
        )

    def test_int_add_matches_python_exact(self) -> None:
        import random
        rng = random.Random(0xADD798)
        result = _compile_with_types(_INT_ADD)
        pairs = [(a, b) for a in self._BOUNDARIES_SIGNED
                 for b in self._BOUNDARIES_SIGNED]
        for _ in range(3000):
            pairs.append((rng.randint(I64_MIN, I64_MAX),
                          rng.randint(I64_MIN, I64_MAX)))
        mismatches = []
        for a, b in pairs:
            trapped = _traps(result, "add", [a, b])
            overflows = not (I64_MIN <= a + b <= I64_MAX)
            if trapped != overflows:
                mismatches.append((a, b, trapped, overflows))
        assert not mismatches, mismatches[:10]

    def test_int_sub_matches_python_exact(self) -> None:
        import random
        rng = random.Random(0x5B798)
        result = _compile_with_types(_INT_SUB)
        # sub(a, b) = @Int.1 - @Int.0 = first - second = a - b.
        pairs = [(a, b) for a in self._BOUNDARIES_SIGNED
                 for b in self._BOUNDARIES_SIGNED]
        for _ in range(3000):
            pairs.append((rng.randint(I64_MIN, I64_MAX),
                          rng.randint(I64_MIN, I64_MAX)))
        mismatches = []
        for a, b in pairs:
            trapped = _traps(result, "sub", [a, b])
            overflows = not (I64_MIN <= a - b <= I64_MAX)
            if trapped != overflows:
                mismatches.append((a, b, trapped, overflows))
        assert not mismatches, mismatches[:10]

    def test_nat_add_matches_python_exact(self) -> None:
        import random
        rng = random.Random(0xADD_4A7)
        result = _compile_with_types(_NAT_ADD)
        pairs = [(a, b) for a in self._BOUNDARIES_UNSIGNED
                 for b in self._BOUNDARIES_UNSIGNED]
        for _ in range(3000):
            pairs.append((rng.randint(0, U64_MAX), rng.randint(0, U64_MAX)))
        mismatches = []
        for a, b in pairs:
            trapped = _traps(result, "add", [a, b])
            overflows = a + b > U64_MAX
            if trapped != overflows:
                mismatches.append((a, b, trapped, overflows))
        assert not mismatches, mismatches[:10]
