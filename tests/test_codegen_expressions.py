"""Tests for vera.codegen — expressions (literals, slot refs, arithmetic, comparison, boolean logic, control flow, function calls, pipe).

Split from tests/test_codegen.py (#419). Shared helpers live in tests/codegen_helpers.py.
"""
from __future__ import annotations

from vera.codegen import (
    execute,
)

from tests.codegen_helpers import (
    _compile_ok,
    _run,
    _run_float,
)


# =====================================================================
# 5a: Literals
# =====================================================================


class TestIntLit:
    def test_zero(self) -> None:
        assert _run("public fn f(-> @Int) requires(true) ensures(true) effects(pure) { 0 }") == 0

    def test_positive(self) -> None:
        assert _run("public fn f(-> @Int) requires(true) ensures(true) effects(pure) { 42 }") == 42

    def test_negative(self) -> None:
        assert _run("public fn f(-> @Int) requires(true) ensures(true) effects(pure) { -1 }") == -1

    def test_large(self) -> None:
        assert _run(
            "public fn f(-> @Int) requires(true) ensures(true) effects(pure) "
            "{ 9999999999 }"
        ) == 9999999999


class TestBoolLit:
    def test_true(self) -> None:
        assert _run("public fn f(-> @Bool) requires(true) ensures(true) effects(pure) { true }") == 1

    def test_false(self) -> None:
        assert _run("public fn f(-> @Bool) requires(true) ensures(true) effects(pure) { false }") == 0


class TestFloatLit:
    def test_zero(self) -> None:
        assert _run_float(
            "public fn f(-> @Float64) requires(true) ensures(true) effects(pure) { 0.0 }"
        ) == 0.0

    def test_positive(self) -> None:
        result = _run_float(
            "public fn f(-> @Float64) requires(true) ensures(true) effects(pure) { 3.14 }"
        )
        assert abs(result - 3.14) < 1e-10

    def test_one(self) -> None:
        assert _run_float(
            "public fn f(-> @Float64) requires(true) ensures(true) effects(pure) { 1.0 }"
        ) == 1.0


class TestFloatSlotRef:
    def test_identity_float64(self) -> None:
        """Float64 identity function: param in, same value out."""
        source = (
            "public fn id(@Float64 -> @Float64) requires(true) ensures(true) "
            "effects(pure) { @Float64.0 }"
        )
        result = _compile_ok(source)
        exec_result = execute(result, fn_name="id", args=[7.5])
        assert exec_result.value == 7.5

    def test_two_float_params(self) -> None:
        """@Float64.0 = most recent (second), @Float64.1 = first."""
        source = (
            "public fn second(@Float64, @Float64 -> @Float64) requires(true) "
            "ensures(true) effects(pure) { @Float64.0 }"
        )
        result = _compile_ok(source)
        exec_result = execute(result, fn_name="second", args=[1.5, 2.5])
        assert exec_result.value == 2.5

    def test_float_param_arithmetic(self) -> None:
        """Float64 param used in arithmetic."""
        source = (
            "public fn add_one(@Float64 -> @Float64) requires(true) ensures(true) "
            "effects(pure) { @Float64.0 + 1.0 }"
        )
        result = _compile_ok(source)
        exec_result = execute(result, fn_name="add_one", args=[2.5])
        assert exec_result.value == 3.5


class TestFloatArithmetic:
    def test_add(self) -> None:
        assert _run_float(
            "public fn f(-> @Float64) requires(true) ensures(true) effects(pure) "
            "{ 1.5 + 2.5 }"
        ) == 4.0

    def test_sub(self) -> None:
        assert _run_float(
            "public fn f(-> @Float64) requires(true) ensures(true) effects(pure) "
            "{ 5.0 - 2.5 }"
        ) == 2.5

    def test_mul(self) -> None:
        assert _run_float(
            "public fn f(-> @Float64) requires(true) ensures(true) effects(pure) "
            "{ 3.0 * 2.5 }"
        ) == 7.5

    def test_div(self) -> None:
        assert _run_float(
            "public fn f(-> @Float64) requires(true) ensures(true) effects(pure) "
            "{ 7.5 / 2.5 }"
        ) == 3.0

    def test_nested(self) -> None:
        """(1.0 + 2.0) * 3.0 = 9.0"""
        assert _run_float(
            "public fn f(-> @Float64) requires(true) ensures(true) effects(pure) "
            "{ (1.0 + 2.0) * 3.0 }"
        ) == 9.0

    def test_mod(self) -> None:
        """7.5 % 2.5 = 0.0 (exact division)."""
        assert _run_float(
            "public fn f(-> @Float64) requires(true) ensures(true) effects(pure) "
            "{ 7.5 % 2.5 }"
        ) == 0.0

    def test_mod_remainder(self) -> None:
        """10.0 % 3.0 = 1.0."""
        assert _run_float(
            "public fn f(-> @Float64) requires(true) ensures(true) effects(pure) "
            "{ 10.0 % 3.0 }"
        ) == 1.0

    def test_mod_negative(self) -> None:
        """-7.0 % 3.0 = -1.0 (truncation toward zero, matching fmod)."""
        assert _run_float(
            "public fn f(-> @Float64) requires(true) ensures(true) effects(pure) "
            "{ -7.0 % 3.0 }"
        ) == -1.0

    def test_mod_with_params(self) -> None:
        """Float mod with slot-ref operands (not just literals)."""
        source = (
            "public fn fmod(@Float64, @Float64 -> @Float64) requires(true) "
            "ensures(true) effects(pure) { @Float64.1 % @Float64.0 }"
        )
        result = _compile_ok(source)
        # @Float64.1 = first arg (10.0), @Float64.0 = second arg (3.0)
        exec_result = execute(result, fn_name="fmod", args=[10.0, 3.0])
        assert exec_result.value == 1.0


class TestFloatComparison:
    def test_eq_true(self) -> None:
        assert _run(
            "public fn f(-> @Bool) requires(true) ensures(true) effects(pure) "
            "{ 1.5 == 1.5 }"
        ) == 1

    def test_eq_false(self) -> None:
        assert _run(
            "public fn f(-> @Bool) requires(true) ensures(true) effects(pure) "
            "{ 1.5 == 2.5 }"
        ) == 0

    def test_neq(self) -> None:
        assert _run(
            "public fn f(-> @Bool) requires(true) ensures(true) effects(pure) "
            "{ 1.5 != 2.5 }"
        ) == 1

    def test_lt(self) -> None:
        assert _run(
            "public fn f(-> @Bool) requires(true) ensures(true) effects(pure) "
            "{ 1.5 < 2.5 }"
        ) == 1

    def test_gt(self) -> None:
        assert _run(
            "public fn f(-> @Bool) requires(true) ensures(true) effects(pure) "
            "{ 2.5 > 1.5 }"
        ) == 1

    def test_le(self) -> None:
        assert _run(
            "public fn f(-> @Bool) requires(true) ensures(true) effects(pure) "
            "{ 1.5 <= 1.5 }"
        ) == 1

    def test_ge(self) -> None:
        assert _run(
            "public fn f(-> @Bool) requires(true) ensures(true) effects(pure) "
            "{ 2.5 >= 1.5 }"
        ) == 1


class TestFloatNeg:
    def test_neg_literal(self) -> None:
        assert _run_float(
            "public fn f(-> @Float64) requires(true) ensures(true) effects(pure) "
            "{ -3.5 }"
        ) == -3.5

    def test_neg_expr(self) -> None:
        assert _run_float(
            "public fn f(-> @Float64) requires(true) ensures(true) effects(pure) "
            "{ -(1.0 + 2.5) }"
        ) == -3.5


class TestFloatIfExpr:
    def test_if_float_result(self) -> None:
        """If expression returning Float64."""
        source = """\
public fn f(-> @Float64)
  requires(true) ensures(true) effects(pure)
{ if true then { 1.5 } else { 2.5 } }
"""
        assert _run_float(source) == 1.5

    def test_if_float_else(self) -> None:
        source = """\
public fn f(-> @Float64)
  requires(true) ensures(true) effects(pure)
{ if false then { 1.5 } else { 2.5 } }
"""
        assert _run_float(source) == 2.5


class TestFloatLet:
    def test_let_float(self) -> None:
        """Let binding with Float64 type."""
        source = """\
public fn f(-> @Float64)
  requires(true) ensures(true) effects(pure)
{
  let @Float64 = 1.5 + 2.5;
  @Float64.0
}
"""
        assert _run_float(source) == 4.0

    def test_let_float_chain(self) -> None:
        """Multiple let bindings with Float64."""
        source = """\
public fn f(-> @Float64)
  requires(true) ensures(true) effects(pure)
{
  let @Float64 = 3.0;
  let @Float64 = @Float64.0 * 2.0;
  @Float64.0
}
"""
        assert _run_float(source) == 6.0


class TestFloatCompileResult:
    def test_wat_has_f64(self) -> None:
        """WAT output contains f64 instructions."""
        result = _compile_ok(
            "public fn f(-> @Float64) requires(true) ensures(true) effects(pure) { 3.14 }"
        )
        assert "f64.const" in result.wat

    def test_float_fn_exported(self) -> None:
        """Float64 functions are exported (no longer skipped)."""
        result = _compile_ok(
            "public fn f(-> @Float64) requires(true) ensures(true) effects(pure) { 1.0 }"
        )
        assert "f" in result.exports


class TestCompileResult:
    def test_wat_not_empty(self) -> None:
        result = _compile_ok("public fn f(-> @Int) requires(true) ensures(true) effects(pure) { 42 }")
        assert "(module" in result.wat
        assert "i64.const 42" in result.wat

    def test_wasm_bytes_not_empty(self) -> None:
        result = _compile_ok("public fn f(-> @Int) requires(true) ensures(true) effects(pure) { 42 }")
        assert len(result.wasm_bytes) > 0

    def test_exports_list(self) -> None:
        result = _compile_ok("public fn f(-> @Int) requires(true) ensures(true) effects(pure) { 42 }")
        assert "f" in result.exports

    def test_ok_property(self) -> None:
        result = _compile_ok("public fn f(-> @Int) requires(true) ensures(true) effects(pure) { 42 }")
        assert result.ok is True


# =====================================================================
# 5b: Slot references + arithmetic
# =====================================================================


class TestSlotRef:
    def test_identity_int(self) -> None:
        """fn id(@Int -> @Int) { @Int.0 }"""
        assert _run(
            "public fn id(@Int -> @Int) requires(true) ensures(true) effects(pure) "
            "{ @Int.0 }",
            fn="id", args=[7],
        ) == 7

    def test_identity_bool(self) -> None:
        assert _run(
            "public fn id(@Bool -> @Bool) requires(true) ensures(true) effects(pure) "
            "{ @Bool.0 }",
            fn="id", args=[1],
        ) == 1

    def test_two_params_same_type(self) -> None:
        """@Int.0 = second param, @Int.1 = first param."""
        assert _run(
            "public fn first(@Int, @Int -> @Int) requires(true) ensures(true) "
            "effects(pure) { @Int.1 }",
            fn="first", args=[10, 20],
        ) == 10

    def test_second_param(self) -> None:
        assert _run(
            "public fn second(@Int, @Int -> @Int) requires(true) ensures(true) "
            "effects(pure) { @Int.0 }",
            fn="second", args=[10, 20],
        ) == 20


class TestArithmetic:
    def test_add(self) -> None:
        assert _run(
            "public fn add(@Int, @Int -> @Int) requires(true) ensures(true) "
            "effects(pure) { @Int.1 + @Int.0 }",
            fn="add", args=[3, 4],
        ) == 7

    def test_sub(self) -> None:
        assert _run(
            "public fn sub(@Int, @Int -> @Int) requires(true) ensures(true) "
            "effects(pure) { @Int.1 - @Int.0 }",
            fn="sub", args=[10, 3],
        ) == 7

    def test_mul(self) -> None:
        assert _run(
            "public fn mul(@Int, @Int -> @Int) requires(true) ensures(true) "
            "effects(pure) { @Int.1 * @Int.0 }",
            fn="mul", args=[6, 7],
        ) == 42

    def test_div(self) -> None:
        assert _run(
            "public fn div(@Int, @Int -> @Int) requires(@Int.0 != 0) ensures(true) "
            "effects(pure) { @Int.1 / @Int.0 }",
            fn="div", args=[10, 3],
        ) == 3

    def test_mod(self) -> None:
        assert _run(
            "public fn rem(@Int, @Int -> @Int) requires(@Int.0 != 0) ensures(true) "
            "effects(pure) { @Int.1 % @Int.0 }",
            fn="rem", args=[10, 3],
        ) == 1

    def test_nested_arithmetic(self) -> None:
        """(a + b) * (a - b)"""
        assert _run(
            "public fn f(@Int, @Int -> @Int) requires(true) ensures(true) "
            "effects(pure) { (@Int.1 + @Int.0) * (@Int.1 - @Int.0) }",
            fn="f", args=[5, 3],
        ) == (5 + 3) * (5 - 3)


class TestComparison:
    def test_eq_true(self) -> None:
        assert _run(
            "public fn f(@Int, @Int -> @Bool) requires(true) ensures(true) "
            "effects(pure) { @Int.1 == @Int.0 }",
            fn="f", args=[5, 5],
        ) == 1

    def test_eq_false(self) -> None:
        assert _run(
            "public fn f(@Int, @Int -> @Bool) requires(true) ensures(true) "
            "effects(pure) { @Int.1 == @Int.0 }",
            fn="f", args=[5, 6],
        ) == 0

    def test_neq(self) -> None:
        assert _run(
            "public fn f(@Int, @Int -> @Bool) requires(true) ensures(true) "
            "effects(pure) { @Int.1 != @Int.0 }",
            fn="f", args=[5, 6],
        ) == 1

    def test_lt(self) -> None:
        assert _run(
            "public fn f(@Int, @Int -> @Bool) requires(true) ensures(true) "
            "effects(pure) { @Int.1 < @Int.0 }",
            fn="f", args=[3, 5],
        ) == 1

    def test_gt(self) -> None:
        assert _run(
            "public fn f(@Int, @Int -> @Bool) requires(true) ensures(true) "
            "effects(pure) { @Int.1 > @Int.0 }",
            fn="f", args=[5, 3],
        ) == 1

    def test_le(self) -> None:
        assert _run(
            "public fn f(@Int, @Int -> @Bool) requires(true) ensures(true) "
            "effects(pure) { @Int.1 <= @Int.0 }",
            fn="f", args=[5, 5],
        ) == 1

    def test_ge(self) -> None:
        assert _run(
            "public fn f(@Int, @Int -> @Bool) requires(true) ensures(true) "
            "effects(pure) { @Int.1 >= @Int.0 }",
            fn="f", args=[5, 3],
        ) == 1


class TestBooleanLogic:
    def test_and(self) -> None:
        assert _run(
            "public fn f(@Bool, @Bool -> @Bool) requires(true) ensures(true) "
            "effects(pure) { @Bool.1 && @Bool.0 }",
            fn="f", args=[1, 1],
        ) == 1

    def test_and_false(self) -> None:
        assert _run(
            "public fn f(@Bool, @Bool -> @Bool) requires(true) ensures(true) "
            "effects(pure) { @Bool.1 && @Bool.0 }",
            fn="f", args=[1, 0],
        ) == 0

    def test_or(self) -> None:
        assert _run(
            "public fn f(@Bool, @Bool -> @Bool) requires(true) ensures(true) "
            "effects(pure) { @Bool.1 || @Bool.0 }",
            fn="f", args=[0, 1],
        ) == 1

    def test_not(self) -> None:
        assert _run(
            "public fn f(@Bool -> @Bool) requires(true) ensures(true) "
            "effects(pure) { !@Bool.0 }",
            fn="f", args=[1],
        ) == 0

    def test_implies_true(self) -> None:
        """false ==> anything is true."""
        assert _run(
            "public fn f(@Bool, @Bool -> @Bool) requires(true) ensures(true) "
            "effects(pure) { @Bool.1 ==> @Bool.0 }",
            fn="f", args=[0, 0],
        ) == 1

    def test_implies_false(self) -> None:
        """true ==> false is false."""
        assert _run(
            "public fn f(@Bool, @Bool -> @Bool) requires(true) ensures(true) "
            "effects(pure) { @Bool.1 ==> @Bool.0 }",
            fn="f", args=[1, 0],
        ) == 0


class TestUnaryOps:
    def test_neg(self) -> None:
        assert _run(
            "public fn neg(@Int -> @Int) requires(true) ensures(true) "
            "effects(pure) { -@Int.0 }",
            fn="neg", args=[5],
        ) == -5

    def test_neg_negative(self) -> None:
        assert _run(
            "public fn neg(@Int -> @Int) requires(true) ensures(true) "
            "effects(pure) { -@Int.0 }",
            fn="neg", args=[-3],
        ) == 3

    def test_not_true(self) -> None:
        assert _run(
            "public fn f(@Bool -> @Bool) requires(true) ensures(true) "
            "effects(pure) { !@Bool.0 }",
            fn="f", args=[1],
        ) == 0

    def test_not_false(self) -> None:
        assert _run(
            "public fn f(@Bool -> @Bool) requires(true) ensures(true) "
            "effects(pure) { !@Bool.0 }",
            fn="f", args=[0],
        ) == 1


# =====================================================================
# 5c: Control flow + let bindings
# =====================================================================


class TestIfExpr:
    def test_if_true(self) -> None:
        source = """\
public fn f(@Bool -> @Int)
  requires(true) ensures(true) effects(pure)
{ if @Bool.0 then { 1 } else { 0 } }
"""
        assert _run(source, fn="f", args=[1]) == 1

    def test_if_false(self) -> None:
        source = """\
public fn f(@Bool -> @Int)
  requires(true) ensures(true) effects(pure)
{ if @Bool.0 then { 1 } else { 0 } }
"""
        assert _run(source, fn="f", args=[0]) == 0

    def test_absolute_value(self) -> None:
        source = """\
public fn absolute_value(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ if @Int.0 >= 0 then { @Int.0 } else { -@Int.0 } }
"""
        assert _run(source, fn="absolute_value", args=[5]) == 5
        assert _run(source, fn="absolute_value", args=[-5]) == 5
        assert _run(source, fn="absolute_value", args=[0]) == 0

    def test_nested_if(self) -> None:
        source = """\
public fn clamp(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  if @Int.0 < 0 then { 0 }
  else { if @Int.0 > 100 then { 100 } else { @Int.0 } }
}
"""
        assert _run(source, fn="clamp", args=[-10]) == 0
        assert _run(source, fn="clamp", args=[50]) == 50
        assert _run(source, fn="clamp", args=[200]) == 100

    def test_if_bool_result(self) -> None:
        source = """\
public fn is_positive(@Int -> @Bool)
  requires(true) ensures(true) effects(pure)
{ if @Int.0 > 0 then { true } else { false } }
"""
        assert _run(source, fn="is_positive", args=[5]) == 1
        assert _run(source, fn="is_positive", args=[-1]) == 0


class TestLetBindings:
    def test_simple_let(self) -> None:
        source = """\
public fn f(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Int = @Int.0 + 1;
  @Int.0
}
"""
        assert _run(source, fn="f", args=[5]) == 6

    def test_multiple_lets(self) -> None:
        source = """\
public fn f(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Int = @Int.0 + 1;
  let @Int = @Int.0 * 2;
  @Int.0
}
"""
        assert _run(source, fn="f", args=[5]) == 12

    def test_let_with_original(self) -> None:
        """After let @Int, the original param is @Int.1."""
        source = """\
public fn f(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Int = @Int.0 * 2;
  @Int.0 + @Int.1
}
"""
        assert _run(source, fn="f", args=[5]) == 15  # 10 + 5

    def test_let_different_types(self) -> None:
        source = """\
public fn f(@Int -> @Bool)
  requires(true) ensures(true) effects(pure)
{
  let @Bool = @Int.0 > 0;
  @Bool.0
}
"""
        assert _run(source, fn="f", args=[5]) == 1
        assert _run(source, fn="f", args=[-1]) == 0

    def test_let_in_if_branches(self) -> None:
        source = """\
public fn f(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Int = if @Int.0 > 0 then { @Int.0 } else { -@Int.0 };
  @Int.0 + 1
}
"""
        assert _run(source, fn="f", args=[5]) == 6
        assert _run(source, fn="f", args=[-3]) == 4


# =====================================================================
# 5d: Function calls + recursion
# =====================================================================


class TestFnCall:
    def test_call_simple(self) -> None:
        source = """\
public fn double(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 * 2 }

public fn f(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ double(@Int.0) }
"""
        assert _run(source, fn="f", args=[5]) == 10

    def test_call_chain(self) -> None:
        source = """\
public fn inc(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 + 1 }

public fn double_inc(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ inc(inc(@Int.0)) }
"""
        assert _run(source, fn="double_inc", args=[5]) == 7

    def test_multiple_args(self) -> None:
        source = """\
public fn add(@Int, @Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.1 + @Int.0 }

public fn f(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ add(@Int.0, @Int.0) }
"""
        assert _run(source, fn="f", args=[5]) == 10


class TestRecursion:
    def test_factorial(self) -> None:
        source = """\
public fn factorial(@Nat -> @Nat)
  requires(@Nat.0 >= 0)
  ensures(true)
  decreases(@Nat.0)
  effects(pure)
{
  if @Nat.0 <= 1 then { 1 }
  else { @Nat.0 * factorial(@Nat.0 - 1) }
}
"""
        assert _run(source, fn="factorial", args=[0]) == 1
        assert _run(source, fn="factorial", args=[1]) == 1
        assert _run(source, fn="factorial", args=[5]) == 120
        assert _run(source, fn="factorial", args=[10]) == 3628800

    def test_fibonacci(self) -> None:
        source = """\
public fn fib(@Nat -> @Nat)
  requires(@Nat.0 >= 0)
  ensures(true)
  decreases(@Nat.0)
  effects(pure)
{
  if @Nat.0 <= 1 then { @Nat.0 }
  else { fib(@Nat.0 - 1) + fib(@Nat.0 - 2) }
}
"""
        assert _run(source, fn="fib", args=[0]) == 0
        assert _run(source, fn="fib", args=[1]) == 1
        assert _run(source, fn="fib", args=[10]) == 55


# =====================================================================
# 5d-pipe: Pipe operator compilation
# =====================================================================


class TestPipeOperator:
    """Pipe operator |> desugars to function call in codegen."""

    def test_pipe_basic(self) -> None:
        source = """\
public fn inc(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 + 1 }

public fn main(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 |> inc() }
"""
        assert _run(source, fn="main", args=[42]) == 43

    def test_pipe_chain(self) -> None:
        source = """\
public fn inc(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 + 1 }

public fn main(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 |> inc() |> inc() }
"""
        assert _run(source, fn="main", args=[10]) == 12

    def test_pipe_multi_arg(self) -> None:
        source = """\
public fn add(@Int, @Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 + @Int.1 }

public fn main(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 |> add(10) }
"""
        assert _run(source, fn="main", args=[42]) == 52


# =====================================================================
# Bool comparison codegen (i32 path)
# =====================================================================


class TestBoolComparison:
    """Bool comparisons should use i32 ops, not i64."""

    def test_bool_eq_true(self) -> None:
        assert _run(
            "public fn f(@Bool, @Bool -> @Bool) requires(true) ensures(true) "
            "effects(pure) { @Bool.1 == @Bool.0 }",
            fn="f", args=[1, 1],
        ) == 1

    def test_bool_eq_false(self) -> None:
        assert _run(
            "public fn f(@Bool, @Bool -> @Bool) requires(true) ensures(true) "
            "effects(pure) { @Bool.1 == @Bool.0 }",
            fn="f", args=[1, 0],
        ) == 0

    def test_bool_neq(self) -> None:
        assert _run(
            "public fn f(@Bool, @Bool -> @Bool) requires(true) ensures(true) "
            "effects(pure) { @Bool.1 != @Bool.0 }",
            fn="f", args=[1, 0],
        ) == 1

    def test_bool_comparison_uses_i32(self) -> None:
        """Verify WAT uses i32.eq for Bool == Bool, not i64.eq."""
        result = _compile_ok(
            "public fn f(@Bool, @Bool -> @Bool) requires(true) ensures(true) "
            "effects(pure) { @Bool.1 == @Bool.0 }"
        )
        assert "i32.eq" in result.wat
        # Should NOT use i64.eq for Bool operands
        assert "i64.eq" not in result.wat
