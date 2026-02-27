"""Tests for vera.codegen — WASM code generation.

Test helpers follow the established pattern:
    _compile(source) → CompileResult
    _compile_ok(source) → CompileResult (assert no errors)
    _run(source, fn, args) → int result
    _run_io(source, fn, args) → captured stdout string
    _run_trap(source, fn, args) → assert WASM trap
"""

from __future__ import annotations

import pytest
import wasmtime

from vera.codegen import (
    CompileResult,
    ConstructorLayout,
    ExecuteResult,
    _align_up,
    _wasm_type_align,
    _wasm_type_size,
    compile,
    execute,
)
from vera.parser import parse_file
from vera.transform import transform


# =====================================================================
# Helpers
# =====================================================================


def _compile(source: str) -> CompileResult:
    """Compile a Vera source string to WASM."""
    # Write to a temp source and parse
    import tempfile
    from pathlib import Path

    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".vera", delete=False
    ) as f:
        f.write(source)
        f.flush()
        path = f.name

    tree = parse_file(path)
    ast = transform(tree)
    return compile(ast, source=source, file=path)


def _compile_ok(source: str) -> CompileResult:
    """Compile and assert no errors."""
    result = _compile(source)
    errors = [d for d in result.diagnostics if d.severity == "error"]
    assert not errors, f"Unexpected errors: {errors}"
    return result


def _run(source: str, fn: str | None = None, args: list[int] | None = None) -> int:
    """Compile, execute, and return the integer result."""
    result = _compile_ok(source)
    exec_result = execute(result, fn_name=fn, args=args)
    assert exec_result.value is not None, "Expected a return value"
    return exec_result.value


def _run_float(
    source: str, fn: str | None = None, args: list[int | float] | None = None
) -> float:
    """Compile, execute, and return the float result."""
    result = _compile_ok(source)
    exec_result = execute(result, fn_name=fn, args=args)
    assert exec_result.value is not None, "Expected a return value"
    assert isinstance(exec_result.value, float), (
        f"Expected float, got {type(exec_result.value).__name__}"
    )
    return exec_result.value


def _run_io(
    source: str, fn: str | None = None, args: list[int] | None = None
) -> str:
    """Compile, execute, and return captured stdout."""
    result = _compile_ok(source)
    exec_result = execute(result, fn_name=fn, args=args)
    return exec_result.stdout


def _run_trap(
    source: str, fn: str | None = None, args: list[int] | None = None
) -> None:
    """Compile, execute, and assert a WASM trap."""
    result = _compile_ok(source)
    with pytest.raises((wasmtime.WasmtimeError, wasmtime.Trap)):
        execute(result, fn_name=fn, args=args)


# =====================================================================
# 5a: Literals
# =====================================================================


class TestIntLit:
    def test_zero(self) -> None:
        assert _run("private fn f(-> @Int) requires(true) ensures(true) effects(pure) { 0 }") == 0

    def test_positive(self) -> None:
        assert _run("private fn f(-> @Int) requires(true) ensures(true) effects(pure) { 42 }") == 42

    def test_negative(self) -> None:
        assert _run("private fn f(-> @Int) requires(true) ensures(true) effects(pure) { -1 }") == -1

    def test_large(self) -> None:
        assert _run(
            "private fn f(-> @Int) requires(true) ensures(true) effects(pure) "
            "{ 9999999999 }"
        ) == 9999999999


class TestBoolLit:
    def test_true(self) -> None:
        assert _run("private fn f(-> @Bool) requires(true) ensures(true) effects(pure) { true }") == 1

    def test_false(self) -> None:
        assert _run("private fn f(-> @Bool) requires(true) ensures(true) effects(pure) { false }") == 0


class TestFloatLit:
    def test_zero(self) -> None:
        assert _run_float(
            "private fn f(-> @Float64) requires(true) ensures(true) effects(pure) { 0.0 }"
        ) == 0.0

    def test_positive(self) -> None:
        result = _run_float(
            "private fn f(-> @Float64) requires(true) ensures(true) effects(pure) { 3.14 }"
        )
        assert abs(result - 3.14) < 1e-10

    def test_one(self) -> None:
        assert _run_float(
            "private fn f(-> @Float64) requires(true) ensures(true) effects(pure) { 1.0 }"
        ) == 1.0


class TestFloatSlotRef:
    def test_identity_float64(self) -> None:
        """Float64 identity function: param in, same value out."""
        source = (
            "private fn id(@Float64 -> @Float64) requires(true) ensures(true) "
            "effects(pure) { @Float64.0 }"
        )
        result = _compile_ok(source)
        exec_result = execute(result, fn_name="id", args=[7.5])
        assert exec_result.value == 7.5

    def test_two_float_params(self) -> None:
        """@Float64.0 = most recent (second), @Float64.1 = first."""
        source = (
            "private fn second(@Float64, @Float64 -> @Float64) requires(true) "
            "ensures(true) effects(pure) { @Float64.0 }"
        )
        result = _compile_ok(source)
        exec_result = execute(result, fn_name="second", args=[1.5, 2.5])
        assert exec_result.value == 2.5

    def test_float_param_arithmetic(self) -> None:
        """Float64 param used in arithmetic."""
        source = (
            "private fn add_one(@Float64 -> @Float64) requires(true) ensures(true) "
            "effects(pure) { @Float64.0 + 1.0 }"
        )
        result = _compile_ok(source)
        exec_result = execute(result, fn_name="add_one", args=[2.5])
        assert exec_result.value == 3.5


class TestFloatArithmetic:
    def test_add(self) -> None:
        assert _run_float(
            "private fn f(-> @Float64) requires(true) ensures(true) effects(pure) "
            "{ 1.5 + 2.5 }"
        ) == 4.0

    def test_sub(self) -> None:
        assert _run_float(
            "private fn f(-> @Float64) requires(true) ensures(true) effects(pure) "
            "{ 5.0 - 2.5 }"
        ) == 2.5

    def test_mul(self) -> None:
        assert _run_float(
            "private fn f(-> @Float64) requires(true) ensures(true) effects(pure) "
            "{ 3.0 * 2.5 }"
        ) == 7.5

    def test_div(self) -> None:
        assert _run_float(
            "private fn f(-> @Float64) requires(true) ensures(true) effects(pure) "
            "{ 7.5 / 2.5 }"
        ) == 3.0

    def test_nested(self) -> None:
        """(1.0 + 2.0) * 3.0 = 9.0"""
        assert _run_float(
            "private fn f(-> @Float64) requires(true) ensures(true) effects(pure) "
            "{ (1.0 + 2.0) * 3.0 }"
        ) == 9.0

    def test_mod(self) -> None:
        """7.5 % 2.5 = 0.0 (exact division)."""
        assert _run_float(
            "private fn f(-> @Float64) requires(true) ensures(true) effects(pure) "
            "{ 7.5 % 2.5 }"
        ) == 0.0

    def test_mod_remainder(self) -> None:
        """10.0 % 3.0 = 1.0."""
        assert _run_float(
            "private fn f(-> @Float64) requires(true) ensures(true) effects(pure) "
            "{ 10.0 % 3.0 }"
        ) == 1.0

    def test_mod_negative(self) -> None:
        """-7.0 % 3.0 = -1.0 (truncation toward zero, matching fmod)."""
        assert _run_float(
            "private fn f(-> @Float64) requires(true) ensures(true) effects(pure) "
            "{ -7.0 % 3.0 }"
        ) == -1.0

    def test_mod_with_params(self) -> None:
        """Float mod with slot-ref operands (not just literals)."""
        source = (
            "private fn fmod(@Float64, @Float64 -> @Float64) requires(true) "
            "ensures(true) effects(pure) { @Float64.1 % @Float64.0 }"
        )
        result = _compile_ok(source)
        # @Float64.1 = first arg (10.0), @Float64.0 = second arg (3.0)
        exec_result = execute(result, fn_name="fmod", args=[10.0, 3.0])
        assert exec_result.value == 1.0


class TestFloatComparison:
    def test_eq_true(self) -> None:
        assert _run(
            "private fn f(-> @Bool) requires(true) ensures(true) effects(pure) "
            "{ 1.5 == 1.5 }"
        ) == 1

    def test_eq_false(self) -> None:
        assert _run(
            "private fn f(-> @Bool) requires(true) ensures(true) effects(pure) "
            "{ 1.5 == 2.5 }"
        ) == 0

    def test_neq(self) -> None:
        assert _run(
            "private fn f(-> @Bool) requires(true) ensures(true) effects(pure) "
            "{ 1.5 != 2.5 }"
        ) == 1

    def test_lt(self) -> None:
        assert _run(
            "private fn f(-> @Bool) requires(true) ensures(true) effects(pure) "
            "{ 1.5 < 2.5 }"
        ) == 1

    def test_gt(self) -> None:
        assert _run(
            "private fn f(-> @Bool) requires(true) ensures(true) effects(pure) "
            "{ 2.5 > 1.5 }"
        ) == 1

    def test_le(self) -> None:
        assert _run(
            "private fn f(-> @Bool) requires(true) ensures(true) effects(pure) "
            "{ 1.5 <= 1.5 }"
        ) == 1

    def test_ge(self) -> None:
        assert _run(
            "private fn f(-> @Bool) requires(true) ensures(true) effects(pure) "
            "{ 2.5 >= 1.5 }"
        ) == 1


class TestFloatNeg:
    def test_neg_literal(self) -> None:
        assert _run_float(
            "private fn f(-> @Float64) requires(true) ensures(true) effects(pure) "
            "{ -3.5 }"
        ) == -3.5

    def test_neg_expr(self) -> None:
        assert _run_float(
            "private fn f(-> @Float64) requires(true) ensures(true) effects(pure) "
            "{ -(1.0 + 2.5) }"
        ) == -3.5


class TestFloatIfExpr:
    def test_if_float_result(self) -> None:
        """If expression returning Float64."""
        source = """\
private fn f(-> @Float64)
  requires(true) ensures(true) effects(pure)
{ if true then { 1.5 } else { 2.5 } }
"""
        assert _run_float(source) == 1.5

    def test_if_float_else(self) -> None:
        source = """\
private fn f(-> @Float64)
  requires(true) ensures(true) effects(pure)
{ if false then { 1.5 } else { 2.5 } }
"""
        assert _run_float(source) == 2.5


class TestFloatLet:
    def test_let_float(self) -> None:
        """Let binding with Float64 type."""
        source = """\
private fn f(-> @Float64)
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
private fn f(-> @Float64)
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
            "private fn f(-> @Float64) requires(true) ensures(true) effects(pure) { 3.14 }"
        )
        assert "f64.const" in result.wat

    def test_float_fn_exported(self) -> None:
        """Float64 functions are exported (no longer skipped)."""
        result = _compile_ok(
            "private fn f(-> @Float64) requires(true) ensures(true) effects(pure) { 1.0 }"
        )
        assert "f" in result.exports


class TestCompileResult:
    def test_wat_not_empty(self) -> None:
        result = _compile_ok("private fn f(-> @Int) requires(true) ensures(true) effects(pure) { 42 }")
        assert "(module" in result.wat
        assert "i64.const 42" in result.wat

    def test_wasm_bytes_not_empty(self) -> None:
        result = _compile_ok("private fn f(-> @Int) requires(true) ensures(true) effects(pure) { 42 }")
        assert len(result.wasm_bytes) > 0

    def test_exports_list(self) -> None:
        result = _compile_ok("private fn f(-> @Int) requires(true) ensures(true) effects(pure) { 42 }")
        assert "f" in result.exports

    def test_ok_property(self) -> None:
        result = _compile_ok("private fn f(-> @Int) requires(true) ensures(true) effects(pure) { 42 }")
        assert result.ok is True


# =====================================================================
# 5b: Slot references + arithmetic
# =====================================================================


class TestSlotRef:
    def test_identity_int(self) -> None:
        """fn id(@Int -> @Int) { @Int.0 }"""
        assert _run(
            "private fn id(@Int -> @Int) requires(true) ensures(true) effects(pure) "
            "{ @Int.0 }",
            fn="id", args=[7],
        ) == 7

    def test_identity_bool(self) -> None:
        assert _run(
            "private fn id(@Bool -> @Bool) requires(true) ensures(true) effects(pure) "
            "{ @Bool.0 }",
            fn="id", args=[1],
        ) == 1

    def test_two_params_same_type(self) -> None:
        """@Int.0 = second param, @Int.1 = first param."""
        assert _run(
            "private fn first(@Int, @Int -> @Int) requires(true) ensures(true) "
            "effects(pure) { @Int.1 }",
            fn="first", args=[10, 20],
        ) == 10

    def test_second_param(self) -> None:
        assert _run(
            "private fn second(@Int, @Int -> @Int) requires(true) ensures(true) "
            "effects(pure) { @Int.0 }",
            fn="second", args=[10, 20],
        ) == 20


class TestArithmetic:
    def test_add(self) -> None:
        assert _run(
            "private fn add(@Int, @Int -> @Int) requires(true) ensures(true) "
            "effects(pure) { @Int.1 + @Int.0 }",
            fn="add", args=[3, 4],
        ) == 7

    def test_sub(self) -> None:
        assert _run(
            "private fn sub(@Int, @Int -> @Int) requires(true) ensures(true) "
            "effects(pure) { @Int.1 - @Int.0 }",
            fn="sub", args=[10, 3],
        ) == 7

    def test_mul(self) -> None:
        assert _run(
            "private fn mul(@Int, @Int -> @Int) requires(true) ensures(true) "
            "effects(pure) { @Int.1 * @Int.0 }",
            fn="mul", args=[6, 7],
        ) == 42

    def test_div(self) -> None:
        assert _run(
            "private fn div(@Int, @Int -> @Int) requires(@Int.0 != 0) ensures(true) "
            "effects(pure) { @Int.1 / @Int.0 }",
            fn="div", args=[10, 3],
        ) == 3

    def test_mod(self) -> None:
        assert _run(
            "private fn rem(@Int, @Int -> @Int) requires(@Int.0 != 0) ensures(true) "
            "effects(pure) { @Int.1 % @Int.0 }",
            fn="rem", args=[10, 3],
        ) == 1

    def test_nested_arithmetic(self) -> None:
        """(a + b) * (a - b)"""
        assert _run(
            "private fn f(@Int, @Int -> @Int) requires(true) ensures(true) "
            "effects(pure) { (@Int.1 + @Int.0) * (@Int.1 - @Int.0) }",
            fn="f", args=[5, 3],
        ) == (5 + 3) * (5 - 3)


class TestComparison:
    def test_eq_true(self) -> None:
        assert _run(
            "private fn f(@Int, @Int -> @Bool) requires(true) ensures(true) "
            "effects(pure) { @Int.1 == @Int.0 }",
            fn="f", args=[5, 5],
        ) == 1

    def test_eq_false(self) -> None:
        assert _run(
            "private fn f(@Int, @Int -> @Bool) requires(true) ensures(true) "
            "effects(pure) { @Int.1 == @Int.0 }",
            fn="f", args=[5, 6],
        ) == 0

    def test_neq(self) -> None:
        assert _run(
            "private fn f(@Int, @Int -> @Bool) requires(true) ensures(true) "
            "effects(pure) { @Int.1 != @Int.0 }",
            fn="f", args=[5, 6],
        ) == 1

    def test_lt(self) -> None:
        assert _run(
            "private fn f(@Int, @Int -> @Bool) requires(true) ensures(true) "
            "effects(pure) { @Int.1 < @Int.0 }",
            fn="f", args=[3, 5],
        ) == 1

    def test_gt(self) -> None:
        assert _run(
            "private fn f(@Int, @Int -> @Bool) requires(true) ensures(true) "
            "effects(pure) { @Int.1 > @Int.0 }",
            fn="f", args=[5, 3],
        ) == 1

    def test_le(self) -> None:
        assert _run(
            "private fn f(@Int, @Int -> @Bool) requires(true) ensures(true) "
            "effects(pure) { @Int.1 <= @Int.0 }",
            fn="f", args=[5, 5],
        ) == 1

    def test_ge(self) -> None:
        assert _run(
            "private fn f(@Int, @Int -> @Bool) requires(true) ensures(true) "
            "effects(pure) { @Int.1 >= @Int.0 }",
            fn="f", args=[5, 3],
        ) == 1


class TestBooleanLogic:
    def test_and(self) -> None:
        assert _run(
            "private fn f(@Bool, @Bool -> @Bool) requires(true) ensures(true) "
            "effects(pure) { @Bool.1 && @Bool.0 }",
            fn="f", args=[1, 1],
        ) == 1

    def test_and_false(self) -> None:
        assert _run(
            "private fn f(@Bool, @Bool -> @Bool) requires(true) ensures(true) "
            "effects(pure) { @Bool.1 && @Bool.0 }",
            fn="f", args=[1, 0],
        ) == 0

    def test_or(self) -> None:
        assert _run(
            "private fn f(@Bool, @Bool -> @Bool) requires(true) ensures(true) "
            "effects(pure) { @Bool.1 || @Bool.0 }",
            fn="f", args=[0, 1],
        ) == 1

    def test_not(self) -> None:
        assert _run(
            "private fn f(@Bool -> @Bool) requires(true) ensures(true) "
            "effects(pure) { !@Bool.0 }",
            fn="f", args=[1],
        ) == 0

    def test_implies_true(self) -> None:
        """false ==> anything is true."""
        assert _run(
            "private fn f(@Bool, @Bool -> @Bool) requires(true) ensures(true) "
            "effects(pure) { @Bool.1 ==> @Bool.0 }",
            fn="f", args=[0, 0],
        ) == 1

    def test_implies_false(self) -> None:
        """true ==> false is false."""
        assert _run(
            "private fn f(@Bool, @Bool -> @Bool) requires(true) ensures(true) "
            "effects(pure) { @Bool.1 ==> @Bool.0 }",
            fn="f", args=[1, 0],
        ) == 0


class TestUnaryOps:
    def test_neg(self) -> None:
        assert _run(
            "private fn neg(@Int -> @Int) requires(true) ensures(true) "
            "effects(pure) { -@Int.0 }",
            fn="neg", args=[5],
        ) == -5

    def test_neg_negative(self) -> None:
        assert _run(
            "private fn neg(@Int -> @Int) requires(true) ensures(true) "
            "effects(pure) { -@Int.0 }",
            fn="neg", args=[-3],
        ) == 3

    def test_not_true(self) -> None:
        assert _run(
            "private fn f(@Bool -> @Bool) requires(true) ensures(true) "
            "effects(pure) { !@Bool.0 }",
            fn="f", args=[1],
        ) == 0

    def test_not_false(self) -> None:
        assert _run(
            "private fn f(@Bool -> @Bool) requires(true) ensures(true) "
            "effects(pure) { !@Bool.0 }",
            fn="f", args=[0],
        ) == 1


# =====================================================================
# 5c: Control flow + let bindings
# =====================================================================


class TestIfExpr:
    def test_if_true(self) -> None:
        source = """\
private fn f(@Bool -> @Int)
  requires(true) ensures(true) effects(pure)
{ if @Bool.0 then { 1 } else { 0 } }
"""
        assert _run(source, fn="f", args=[1]) == 1

    def test_if_false(self) -> None:
        source = """\
private fn f(@Bool -> @Int)
  requires(true) ensures(true) effects(pure)
{ if @Bool.0 then { 1 } else { 0 } }
"""
        assert _run(source, fn="f", args=[0]) == 0

    def test_absolute_value(self) -> None:
        source = """\
private fn absolute_value(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ if @Int.0 >= 0 then { @Int.0 } else { -@Int.0 } }
"""
        assert _run(source, fn="absolute_value", args=[5]) == 5
        assert _run(source, fn="absolute_value", args=[-5]) == 5
        assert _run(source, fn="absolute_value", args=[0]) == 0

    def test_nested_if(self) -> None:
        source = """\
private fn clamp(@Int -> @Int)
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
private fn is_positive(@Int -> @Bool)
  requires(true) ensures(true) effects(pure)
{ if @Int.0 > 0 then { true } else { false } }
"""
        assert _run(source, fn="is_positive", args=[5]) == 1
        assert _run(source, fn="is_positive", args=[-1]) == 0


class TestLetBindings:
    def test_simple_let(self) -> None:
        source = """\
private fn f(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Int = @Int.0 + 1;
  @Int.0
}
"""
        assert _run(source, fn="f", args=[5]) == 6

    def test_multiple_lets(self) -> None:
        source = """\
private fn f(@Int -> @Int)
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
private fn f(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Int = @Int.0 * 2;
  @Int.0 + @Int.1
}
"""
        assert _run(source, fn="f", args=[5]) == 15  # 10 + 5

    def test_let_different_types(self) -> None:
        source = """\
private fn f(@Int -> @Bool)
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
private fn f(@Int -> @Int)
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
private fn double(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 * 2 }

private fn f(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ double(@Int.0) }
"""
        assert _run(source, fn="f", args=[5]) == 10

    def test_call_chain(self) -> None:
        source = """\
private fn inc(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 + 1 }

private fn double_inc(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ inc(inc(@Int.0)) }
"""
        assert _run(source, fn="double_inc", args=[5]) == 7

    def test_multiple_args(self) -> None:
        source = """\
private fn add(@Int, @Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.1 + @Int.0 }

private fn f(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ add(@Int.0, @Int.0) }
"""
        assert _run(source, fn="f", args=[5]) == 10


class TestRecursion:
    def test_factorial(self) -> None:
        source = """\
private fn factorial(@Nat -> @Nat)
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
private fn fib(@Nat -> @Nat)
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
private fn inc(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 + 1 }

private fn main(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 |> inc() }
"""
        assert _run(source, fn="main", args=[42]) == 43

    def test_pipe_chain(self) -> None:
        source = """\
private fn inc(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 + 1 }

private fn main(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 |> inc() |> inc() }
"""
        assert _run(source, fn="main", args=[10]) == 12

    def test_pipe_multi_arg(self) -> None:
        source = """\
private fn add(@Int, @Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 + @Int.1 }

private fn main(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 |> add(10) }
"""
        assert _run(source, fn="main", args=[42]) == 52


# =====================================================================
# 5e: String literals + IO host bindings
# =====================================================================

_IO_PRELUDE = """\
effect IO {
  op print(String -> Unit);
}
"""


class TestStringLitIO:
    def test_hello_world(self) -> None:
        """First light: Hello, World!"""
        source = _IO_PRELUDE + """\
private fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{ IO.print("Hello, World!") }
"""
        assert _run_io(source, fn="main") == "Hello, World!"

    def test_empty_string(self) -> None:
        source = _IO_PRELUDE + """\
private fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{ IO.print("") }
"""
        assert _run_io(source, fn="main") == ""

    def test_multiple_prints(self) -> None:
        source = _IO_PRELUDE + """\
private fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print("Hello, ");
  IO.print("World!")
}
"""
        assert _run_io(source, fn="main") == "Hello, World!"

    def test_string_dedup(self) -> None:
        """Identical strings should be deduplicated in the data section."""
        source = _IO_PRELUDE + """\
private fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print("abc");
  IO.print("abc")
}
"""
        result = _compile_ok(source)
        # The string "abc" should appear only once in the data section
        assert result.wat.count('"abc"') == 1
        exec_result = execute(result, fn_name="main")
        assert exec_result.stdout == "abcabc"

    def test_special_characters(self) -> None:
        """Strings with punctuation and spaces."""
        source = _IO_PRELUDE + """\
private fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{ IO.print("Hello, World! 123 @#$") }
"""
        assert _run_io(source, fn="main") == "Hello, World! 123 @#$"

    def test_io_with_pure_functions(self) -> None:
        """IO functions coexist with pure functions in the same module."""
        source = _IO_PRELUDE + """\
private fn add(@Int, @Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.1 + @Int.0 }

private fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{ IO.print("hello") }
"""
        result = _compile_ok(source)
        assert "add" in result.exports
        assert "main" in result.exports
        assert _run_io(source, fn="main") == "hello"

    def test_hello_world_example_file(self) -> None:
        """The actual examples/hello_world.vera compiles and runs."""
        from pathlib import Path
        example_path = Path(__file__).parent.parent / "examples" / "hello_world.vera"
        source = example_path.read_text()
        tree = parse_file(str(example_path))
        ast = transform(tree)
        result = compile(ast, source=source, file=str(example_path))
        assert result.ok
        exec_result = execute(result, fn_name="main")
        assert exec_result.stdout == "Hello, World!"


# =====================================================================
# 5f: Runtime contract insertion
# =====================================================================


class TestPreconditions:
    def test_requires_holds(self) -> None:
        """Non-trivial precondition that holds — no trap."""
        source = """\
private fn positive(@Int -> @Int)
  requires(@Int.0 > 0)
  ensures(true)
  effects(pure)
{ @Int.0 }
"""
        assert _run(source, fn="positive", args=[5]) == 5

    def test_requires_traps(self) -> None:
        """Non-trivial precondition violated — WASM trap."""
        source = """\
private fn positive(@Int -> @Int)
  requires(@Int.0 > 0)
  ensures(true)
  effects(pure)
{ @Int.0 }
"""
        _run_trap(source, fn="positive", args=[0])

    def test_requires_boundary(self) -> None:
        """Precondition with exact boundary value."""
        source = """\
private fn nonneg(@Int -> @Int)
  requires(@Int.0 >= 0)
  ensures(true)
  effects(pure)
{ @Int.0 }
"""
        assert _run(source, fn="nonneg", args=[0]) == 0
        _run_trap(source, fn="nonneg", args=[-1])

    def test_requires_neq_zero(self) -> None:
        """Precondition: denominator != 0."""
        source = """\
private fn safe_div(@Int, @Int -> @Int)
  requires(@Int.0 != 0)
  ensures(true)
  effects(pure)
{ @Int.1 / @Int.0 }
"""
        assert _run(source, fn="safe_div", args=[10, 2]) == 5
        _run_trap(source, fn="safe_div", args=[10, 0])

    def test_trivial_requires_no_overhead(self) -> None:
        """requires(true) should not produce any trap instructions."""
        source = """\
private fn f(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 }
"""
        result = _compile_ok(source)
        # No unreachable in WAT (no contract checks needed)
        assert "unreachable" not in result.wat

    def test_multiple_requires(self) -> None:
        """Multiple preconditions — all must hold."""
        source = """\
private fn bounded(@Int -> @Int)
  requires(@Int.0 >= 0)
  requires(@Int.0 <= 100)
  ensures(true)
  effects(pure)
{ @Int.0 }
"""
        assert _run(source, fn="bounded", args=[50]) == 50
        _run_trap(source, fn="bounded", args=[-1])
        _run_trap(source, fn="bounded", args=[101])


class TestPostconditions:
    def test_ensures_holds(self) -> None:
        """Postcondition that holds — no trap."""
        source = """\
private fn double(@Int -> @Int)
  requires(true)
  ensures(@Int.result >= 0)
  effects(pure)
{ @Int.0 * 2 }
"""
        assert _run(source, fn="double", args=[5]) == 10

    def test_ensures_traps(self) -> None:
        """Postcondition violated — WASM trap."""
        source = """\
private fn negate(@Int -> @Int)
  requires(true)
  ensures(@Int.result > 0)
  effects(pure)
{ -@Int.0 }
"""
        # negate(5) returns -5, which violates ensures(result > 0)
        _run_trap(source, fn="negate", args=[5])

    def test_ensures_with_params(self) -> None:
        """Postcondition referencing both result and parameters."""
        source = """\
private fn inc(@Int -> @Int)
  requires(true)
  ensures(@Int.result > @Int.0)
  effects(pure)
{ @Int.0 + 1 }
"""
        assert _run(source, fn="inc", args=[5]) == 6

    def test_ensures_result_eq(self) -> None:
        """Postcondition checking exact result value."""
        source = """\
private fn always_zero(-> @Int)
  requires(true)
  ensures(@Int.result == 0)
  effects(pure)
{ 0 }
"""
        assert _run(source, fn="always_zero") == 0

    def test_ensures_result_traps(self) -> None:
        """Postcondition checking exact value — wrong result traps."""
        source = """\
private fn buggy(-> @Int)
  requires(true)
  ensures(@Int.result == 0)
  effects(pure)
{ 42 }
"""
        _run_trap(source, fn="buggy")

    def test_trivial_ensures_no_overhead(self) -> None:
        """ensures(true) should not produce any trap instructions."""
        source = """\
private fn f(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 }
"""
        result = _compile_ok(source)
        assert "unreachable" not in result.wat

    def test_ensures_bool_result(self) -> None:
        """Postcondition on a Bool-returning function."""
        source = """\
private fn is_pos(@Int -> @Bool)
  requires(true)
  ensures(@Bool.result == true)
  effects(pure)
{ @Int.0 > 0 }
"""
        assert _run(source, fn="is_pos", args=[5]) == 1
        # is_pos(-1) returns false, violating ensures(result == true)
        _run_trap(source, fn="is_pos", args=[-1])


class TestCombinedContracts:
    def test_both_hold(self) -> None:
        """Both requires and ensures hold — normal execution."""
        source = """\
private fn safe_inc(@Int -> @Int)
  requires(@Int.0 >= 0)
  ensures(@Int.result > @Int.0)
  effects(pure)
{ @Int.0 + 1 }
"""
        assert _run(source, fn="safe_inc", args=[0]) == 1
        assert _run(source, fn="safe_inc", args=[10]) == 11

    def test_requires_fails_first(self) -> None:
        """Precondition fails before postcondition is checked."""
        source = """\
private fn safe_inc(@Int -> @Int)
  requires(@Int.0 >= 0)
  ensures(@Int.result > @Int.0)
  effects(pure)
{ @Int.0 + 1 }
"""
        _run_trap(source, fn="safe_inc", args=[-1])

    def test_contracts_with_recursion(self) -> None:
        """Runtime contracts on a recursive function."""
        source = """\
private fn factorial(@Nat -> @Nat)
  requires(@Nat.0 >= 0)
  ensures(@Nat.result >= 1)
  decreases(@Nat.0)
  effects(pure)
{
  if @Nat.0 <= 1 then { 1 }
  else { @Nat.0 * factorial(@Nat.0 - 1) }
}
"""
        assert _run(source, fn="factorial", args=[5]) == 120
        assert _run(source, fn="factorial", args=[0]) == 1


# =====================================================================
# Unsupported constructs
# =====================================================================


class TestUnsupportedSkipped:
    def test_adt_function_compiles(self) -> None:
        """Functions with ADT types now compile (not skipped)."""
        source = """\
private data Option<T> { None, Some(T) }

private fn make_none(-> @Option<Int>)
  requires(true) ensures(true) effects(pure)
{ None }

private fn simple(-> @Int)
  requires(true) ensures(true) effects(pure)
{ 1 }
"""
        result = _compile(source)
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert not errors
        # Both functions should be compiled
        assert "make_none" in result.exports
        assert "simple" in result.exports

    def test_unsupported_effect_skipped(self) -> None:
        """Functions with non-IO effects produce warnings, not errors."""
        source = """\
effect Counter {
  op tick(Unit -> Unit);
}

private fn count(@Unit -> @Unit)
  requires(true) ensures(true) effects(<Counter>)
{
  Counter.tick(())
}

private fn simple(-> @Int)
  requires(true) ensures(true) effects(pure)
{ 42 }
"""
        result = _compile(source)
        errors = [d for d in result.diagnostics if d.severity == "error"]
        warnings = [d for d in result.diagnostics if d.severity == "warning"]
        assert not errors
        assert len(warnings) > 0
        # Unsupported effect function is skipped
        assert "count" not in result.exports
        # Pure function still compiles
        assert "simple" in result.exports


# =====================================================================
# Example round-trips — compile and run actual .vera example files
# =====================================================================


class TestExampleRoundTrips:
    """Compile and execute the .vera example files that fall within
    the compilable subset (Int, Nat, Bool, Unit, String, IO)."""

    def test_absolute_value_positive(self) -> None:
        """absolute_value(5) returns 5."""
        from pathlib import Path
        path = Path(__file__).parent.parent / "examples" / "absolute_value.vera"
        source = path.read_text()
        tree = parse_file(str(path))
        program = transform(tree)
        result = compile(program, source=source, file=str(path))
        assert result.ok
        assert "absolute_value" in result.exports
        exec_result = execute(result, fn_name="absolute_value", args=[5])
        assert exec_result.value == 5

    def test_absolute_value_negative(self) -> None:
        """absolute_value(-7) returns 7."""
        from pathlib import Path
        path = Path(__file__).parent.parent / "examples" / "absolute_value.vera"
        source = path.read_text()
        tree = parse_file(str(path))
        program = transform(tree)
        result = compile(program, source=source, file=str(path))
        exec_result = execute(result, fn_name="absolute_value", args=[-7])
        assert exec_result.value == 7

    def test_absolute_value_zero(self) -> None:
        """absolute_value(0) returns 0."""
        from pathlib import Path
        path = Path(__file__).parent.parent / "examples" / "absolute_value.vera"
        source = path.read_text()
        tree = parse_file(str(path))
        program = transform(tree)
        result = compile(program, source=source, file=str(path))
        exec_result = execute(result, fn_name="absolute_value", args=[0])
        assert exec_result.value == 0

    def test_safe_divide(self) -> None:
        """safe_divide(3, 10) returns 3 (body: @Int.0/@Int.1 = 10/3)."""
        from pathlib import Path
        path = Path(__file__).parent.parent / "examples" / "safe_divide.vera"
        source = path.read_text()
        tree = parse_file(str(path))
        program = transform(tree)
        result = compile(program, source=source, file=str(path))
        assert result.ok
        assert "safe_divide" in result.exports
        # De Bruijn: @Int.1 = first param (divisor), @Int.0 = second param
        # Body: @Int.0 / @Int.1 = second / first = 10 / 3 = 3
        exec_result = execute(result, fn_name="safe_divide", args=[3, 10])
        assert exec_result.value == 3

    def test_safe_divide_trap_on_zero(self) -> None:
        """safe_divide(0, 10) traps: requires(@Int.1 != 0) violated."""
        from pathlib import Path
        path = Path(__file__).parent.parent / "examples" / "safe_divide.vera"
        source = path.read_text()
        tree = parse_file(str(path))
        program = transform(tree)
        result = compile(program, source=source, file=str(path))
        # First param (divisor) is 0 → precondition @Int.1 != 0 violated
        with pytest.raises((wasmtime.WasmtimeError, wasmtime.Trap)):
            execute(result, fn_name="safe_divide", args=[0, 10])

    def test_mutual_recursion_is_even(self) -> None:
        """Where-block mutual recursion: is_even(4) returns true."""
        from pathlib import Path
        path = Path(__file__).parent.parent / "examples" / "mutual_recursion.vera"
        source = path.read_text()
        tree = parse_file(str(path))
        program = transform(tree)
        result = compile(program, source=source, file=str(path))
        assert result.ok
        assert "is_even" in result.exports
        # is_even(4) → true (1)
        exec_result = execute(result, fn_name="is_even", args=[4])
        assert exec_result.value == 1
        # is_even(3) → false (0)
        exec_result = execute(result, fn_name="is_even", args=[3])
        assert exec_result.value == 0

    def test_mutual_recursion_zero(self) -> None:
        """is_even(0) returns true (base case)."""
        from pathlib import Path
        path = Path(__file__).parent.parent / "examples" / "mutual_recursion.vera"
        source = path.read_text()
        tree = parse_file(str(path))
        program = transform(tree)
        result = compile(program, source=source, file=str(path))
        exec_result = execute(result, fn_name="is_even", args=[0])
        assert exec_result.value == 1

    def test_factorial_example_file(self) -> None:
        """The actual examples/factorial.vera compiles and runs."""
        from pathlib import Path
        path = Path(__file__).parent.parent / "examples" / "factorial.vera"
        source = path.read_text()
        tree = parse_file(str(path))
        program = transform(tree)
        result = compile(program, source=source, file=str(path))
        assert result.ok
        exec_result = execute(result, fn_name="factorial", args=[5])
        assert exec_result.value == 120


# =====================================================================
# String escape sequences — unit tests for WAT escaping
# =====================================================================


class TestWatStringEscaping:
    """Unit tests for the _escape_wat_string helper that escapes
    special characters for WAT data section string literals."""

    @staticmethod
    def _escape(s: str) -> str:
        """Call the WAT string escaper."""
        from vera.codegen import CodeGenerator
        return CodeGenerator._escape_wat_string(s)

    def test_plain_ascii(self) -> None:
        assert self._escape("Hello, World!") == "Hello, World!"

    def test_double_quote(self) -> None:
        """Double quotes must be escaped in WAT."""
        assert self._escape('say "hi"') == "say \\22hi\\22"

    def test_backslash(self) -> None:
        """Backslashes must be escaped in WAT."""
        assert self._escape("a\\b") == "a\\\\b"

    def test_newline(self) -> None:
        """Newline characters escape to \\n in WAT."""
        assert self._escape("line1\nline2") == "line1\\nline2"

    def test_tab(self) -> None:
        """Tab characters escape to \\t in WAT."""
        assert self._escape("col1\tcol2") == "col1\\tcol2"

    def test_unicode_emoji(self) -> None:
        """Non-ASCII chars are encoded as hex bytes in WAT."""
        # '😀' is U+1F600, encoded as 4 UTF-8 bytes: f0 9f 98 80
        result = self._escape("😀")
        assert result == "\\f0\\9f\\98\\80"

    def test_mixed_special_chars(self) -> None:
        """Mix of special characters."""
        result = self._escape('a"b\\c\nd')
        assert result == "a\\22b\\\\c\\nd"

    def test_empty_string(self) -> None:
        """Empty string produces empty output."""
        assert self._escape("") == ""


# =====================================================================
# Bool comparison codegen (i32 path)
# =====================================================================


class TestBoolComparison:
    """Bool comparisons should use i32 ops, not i64."""

    def test_bool_eq_true(self) -> None:
        assert _run(
            "private fn f(@Bool, @Bool -> @Bool) requires(true) ensures(true) "
            "effects(pure) { @Bool.1 == @Bool.0 }",
            fn="f", args=[1, 1],
        ) == 1

    def test_bool_eq_false(self) -> None:
        assert _run(
            "private fn f(@Bool, @Bool -> @Bool) requires(true) ensures(true) "
            "effects(pure) { @Bool.1 == @Bool.0 }",
            fn="f", args=[1, 0],
        ) == 0

    def test_bool_neq(self) -> None:
        assert _run(
            "private fn f(@Bool, @Bool -> @Bool) requires(true) ensures(true) "
            "effects(pure) { @Bool.1 != @Bool.0 }",
            fn="f", args=[1, 0],
        ) == 1

    def test_bool_comparison_uses_i32(self) -> None:
        """Verify WAT uses i32.eq for Bool == Bool, not i64.eq."""
        result = _compile_ok(
            "private fn f(@Bool, @Bool -> @Bool) requires(true) ensures(true) "
            "effects(pure) { @Bool.1 == @Bool.0 }"
        )
        assert "i32.eq" in result.wat
        # Should NOT use i64.eq for Bool operands
        assert "i64.eq" not in result.wat


# =====================================================================
# Module assembly — import/memory conditionals
# =====================================================================


class TestModuleAssembly:
    """Verify that module-level constructs are conditional."""

    def test_pure_no_io_import(self) -> None:
        """Pure functions should not import vera.print."""
        result = _compile_ok(
            "private fn f(-> @Int) requires(true) ensures(true) effects(pure) { 42 }"
        )
        assert "vera.print" not in result.wat

    def test_pure_no_memory(self) -> None:
        """Pure functions without strings should not declare memory."""
        result = _compile_ok(
            "private fn f(-> @Int) requires(true) ensures(true) effects(pure) { 42 }"
        )
        assert "(memory" not in result.wat

    def test_io_has_import_and_memory(self) -> None:
        """IO functions import vera.print and declare memory."""
        source = _IO_PRELUDE + """\
private fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{ IO.print("hello") }
"""
        result = _compile_ok(source)
        assert 'import "vera" "print"' in result.wat
        assert "(memory" in result.wat
        assert "(data" in result.wat

    def test_multiple_exports(self) -> None:
        """Multiple compilable functions are all exported."""
        source = """\
private fn add(@Int, @Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.1 + @Int.0 }

private fn mul(@Int, @Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.1 * @Int.0 }

private fn neg(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ -@Int.0 }
"""
        result = _compile_ok(source)
        assert "add" in result.exports
        assert "mul" in result.exports
        assert "neg" in result.exports
        assert len(result.exports) == 3


# =====================================================================
# Execute error paths
# =====================================================================


class TestExecuteErrors:
    """Test error handling in the execute() function."""

    def test_function_not_found(self) -> None:
        """execute() with unknown function name raises RuntimeError."""
        result = _compile_ok(
            "private fn f(-> @Int) requires(true) ensures(true) effects(pure) { 42 }"
        )
        with pytest.raises(RuntimeError, match="not found"):
            execute(result, fn_name="nonexistent")

    def test_compilation_error_blocks_execute(self) -> None:
        """execute() refuses to run if compilation had errors."""
        from vera.errors import Diagnostic, SourceLocation
        result = CompileResult(
            wat="",
            wasm_bytes=b"",
            exports=[],
            diagnostics=[
                Diagnostic(
                    description="test error",
                    location=SourceLocation(),
                    severity="error",
                )
            ],
        )
        with pytest.raises(RuntimeError, match="compilation had errors"):
            execute(result)

    def test_first_export_used_when_no_main(self) -> None:
        """When no 'main' function, the first exported function is called."""
        source = """\
private fn compute(-> @Int)
  requires(true) ensures(true) effects(pure)
{ 99 }
"""
        result = _compile_ok(source)
        assert "main" not in result.exports
        exec_result = execute(result)  # no fn_name specified
        assert exec_result.value == 99


# =====================================================================
# 6d: State<T> host imports
# =====================================================================

def _run_state(
    source: str,
    fn: str | None = None,
    args: list[int | float] | None = None,
    initial_state: dict[str, int | float] | None = None,
) -> ExecuteResult:
    """Compile, execute, and return the full ExecuteResult."""
    result = _compile_ok(source)
    return execute(result, fn_name=fn, args=args, initial_state=initial_state)


class TestStateEffect:

    def test_state_int_get_default(self) -> None:
        """get(()) returns 0 by default for State<Int>."""
        source = """\
private fn f(-> @Int)
  requires(true) ensures(true) effects(<State<Int>>)
{ get(()) }
"""
        exec_result = _run_state(source, fn="f")
        assert exec_result.value == 0

    def test_state_int_put_then_get(self) -> None:
        """put(42) then get(()) returns 42."""
        source = """\
private fn f(-> @Int)
  requires(true) ensures(true) effects(<State<Int>>)
{
  put(42);
  get(())
}
"""
        exec_result = _run_state(source, fn="f")
        assert exec_result.value == 42

    def test_increment_pattern(self) -> None:
        """Classic increment: get, add 1, put — state goes from 0 to 1."""
        source = """\
private fn increment(@Unit -> @Unit)
  requires(true) ensures(true) effects(<State<Int>>)
{
  let @Int = get(());
  put(@Int.0 + 1);
  ()
}
"""
        exec_result = _run_state(source, fn="increment")
        assert exec_result.value is None  # Unit return
        assert exec_result.state["State_Int"] == 1

    def test_increment_example_file(self) -> None:
        """examples/increment.vera compiles and executes."""
        from pathlib import Path
        path = Path(__file__).parent.parent / "examples" / "increment.vera"
        source = path.read_text()
        tree = parse_file(str(path))
        program = transform(tree)
        result = compile(program, source=source, file=str(path))
        assert result.ok
        assert "increment" in result.exports
        exec_result = execute(result, fn_name="increment")
        assert exec_result.state["State_Int"] == 1

    def test_state_bool_get_default(self) -> None:
        """Bool state defaults to 0 (false)."""
        source = """\
private fn f(-> @Bool)
  requires(true) ensures(true) effects(<State<Bool>>)
{ get(()) }
"""
        exec_result = _run_state(source, fn="f")
        assert exec_result.value == 0

    def test_state_bool_put_get(self) -> None:
        """put(true) then get(()) returns 1."""
        source = """\
private fn f(-> @Bool)
  requires(true) ensures(true) effects(<State<Bool>>)
{
  put(true);
  get(())
}
"""
        exec_result = _run_state(source, fn="f")
        assert exec_result.value == 1

    def test_state_float64_get_default(self) -> None:
        """Float64 state defaults to 0.0."""
        source = """\
private fn f(-> @Float64)
  requires(true) ensures(true) effects(<State<Float64>>)
{ get(()) }
"""
        exec_result = _run_state(source, fn="f")
        assert exec_result.value == 0.0

    def test_state_nat_compiles(self) -> None:
        """State<Nat> compiles (Nat maps to i64)."""
        source = """\
private fn f(-> @Nat)
  requires(true) ensures(true) effects(<State<Nat>>)
{ get(()) }
"""
        exec_result = _run_state(source, fn="f")
        assert exec_result.value == 0

    def test_state_string_rejected(self) -> None:
        """State<String> is unsupported — function skipped with warning."""
        source = """\
private fn f(-> @Int)
  requires(true) ensures(true) effects(<State<String>>)
{ 42 }
"""
        result = _compile(source)
        warnings = [d for d in result.diagnostics if d.severity == "warning"]
        assert any("unsupported" in w.description.lower() for w in warnings)
        assert "f" not in result.exports

    def test_state_with_io(self) -> None:
        """Mixed effects(<State<Int>, IO>) compiles and both work."""
        source = """\
private fn f(@Unit -> @Unit)
  requires(true) ensures(true) effects(<State<Int>, IO>)
{
  put(42);
  IO.print("done");
  ()
}
"""
        exec_result = _run_state(source, fn="f")
        assert exec_result.state["State_Int"] == 42
        assert exec_result.stdout == "done"

    def test_state_wat_has_imports(self) -> None:
        """WAT output contains State import declarations."""
        source = """\
private fn f(-> @Int)
  requires(true) ensures(true) effects(<State<Int>>)
{ get(()) }
"""
        result = _compile_ok(source)
        assert 'import "vera" "state_get_Int"' in result.wat
        assert 'import "vera" "state_put_Int"' in result.wat

    def test_multiple_state_types(self) -> None:
        """Multiple State types emit all imports."""
        source = """\
private fn f(@Int -> @Unit)
  requires(true) ensures(true) effects(<State<Int>, State<Bool>>)
{
  put(@Int.0);
  ()
}
"""
        result = _compile_ok(source)
        assert 'import "vera" "state_get_Int"' in result.wat
        assert 'import "vera" "state_put_Int"' in result.wat
        assert 'import "vera" "state_get_Bool"' in result.wat
        assert 'import "vera" "state_put_Bool"' in result.wat
        assert len(result.state_types) == 2

    def test_put_void_no_drop(self) -> None:
        """put(x) in ExprStmt does not emit a drop instruction."""
        source = """\
private fn f(@Unit -> @Unit)
  requires(true) ensures(true) effects(<State<Int>>)
{
  put(42);
  ()
}
"""
        result = _compile_ok(source)
        # The function body should NOT contain 'drop' after the put call
        fn_start = result.wat.index("(func $f")
        fn_body = result.wat[fn_start:]
        # put call should be present, drop should not follow it
        assert "call $vera.state_put_Int" in fn_body
        assert "drop" not in fn_body

    def test_state_initial_value(self) -> None:
        """Initial state override: get(()) returns the initial value."""
        source = """\
private fn f(-> @Int)
  requires(true) ensures(true) effects(<State<Int>>)
{ get(()) }
"""
        exec_result = _run_state(
            source, fn="f", initial_state={"State_Int": 10}
        )
        assert exec_result.value == 10

    def test_pure_no_state_imports(self) -> None:
        """Pure functions don't produce State imports."""
        source = """\
private fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{ 42 }
"""
        result = _compile_ok(source)
        assert "state_get" not in result.wat
        assert "state_put" not in result.wat


# =====================================================================
# 6e: Bump allocator infrastructure
# =====================================================================


def _compile_with_generator(source: str):
    """Compile and return both result and CodeGenerator for metadata inspection."""
    import tempfile
    from vera.codegen import CodeGenerator

    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".vera", delete=False
    ) as f:
        f.write(source)
        f.flush()
        path = f.name

    tree = parse_file(path)
    program = transform(tree)
    gen = CodeGenerator(source=source, file=path)
    result = gen.compile_program(program)
    return result, gen


class TestLayoutHelpers:
    """Unit tests for ADT memory layout helper functions."""

    def test_align_up_already_aligned(self) -> None:
        assert _align_up(8, 8) == 8

    def test_align_up_needs_padding(self) -> None:
        assert _align_up(5, 8) == 8

    def test_align_up_zero(self) -> None:
        assert _align_up(0, 8) == 0

    def test_align_up_to_four(self) -> None:
        assert _align_up(5, 4) == 8

    def test_align_up_one(self) -> None:
        assert _align_up(1, 8) == 8

    def test_wasm_type_size_i32(self) -> None:
        assert _wasm_type_size("i32") == 4

    def test_wasm_type_size_i64(self) -> None:
        assert _wasm_type_size("i64") == 8

    def test_wasm_type_size_f64(self) -> None:
        assert _wasm_type_size("f64") == 8

    def test_wasm_type_align_i32(self) -> None:
        assert _wasm_type_align("i32") == 4

    def test_wasm_type_align_i64(self) -> None:
        assert _wasm_type_align("i64") == 8

    def test_wasm_type_align_f64(self) -> None:
        assert _wasm_type_align("f64") == 8


class TestHeapAllocation:
    """Test heap infrastructure emission in WAT output."""

    def test_heap_ptr_global_emitted(self) -> None:
        """When ADTs are declared, $heap_ptr global appears in WAT."""
        source = """\
private data Color { Red, Green, Blue }

private fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{ 42 }
"""
        result = _compile_ok(source)
        assert "global $heap_ptr" in result.wat
        assert 'export "heap_ptr"' in result.wat

    def test_alloc_function_emitted(self) -> None:
        """When ADTs are declared, $alloc function appears in WAT."""
        source = """\
private data Color { Red, Green, Blue }

private fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{ 42 }
"""
        result = _compile_ok(source)
        assert "func $alloc" in result.wat
        assert "global.get $heap_ptr" in result.wat
        assert "global.set $heap_ptr" in result.wat

    def test_no_alloc_without_adt(self) -> None:
        """Pure programs without ADTs should NOT emit allocator."""
        source = """\
private fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{ 42 }
"""
        result = _compile_ok(source)
        assert "heap_ptr" not in result.wat
        assert "$alloc" not in result.wat

    def test_heap_ptr_starts_after_strings(self) -> None:
        """Heap pointer initial value should be after string data."""
        source = """\
private data Color { Red, Green, Blue }

private fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{ IO.print("hello") }
"""
        result = _compile_ok(source)
        # "hello" is 5 bytes, so heap_ptr should start at offset 5
        assert "global $heap_ptr" in result.wat
        assert "i32.const 5" in result.wat

    def test_heap_ptr_zero_without_strings(self) -> None:
        """Without strings, heap starts at offset 0."""
        source = """\
private data Flag { On, Off }

private fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{ 42 }
"""
        result = _compile_ok(source)
        assert "i32.const 0)" in result.wat  # heap_ptr init

    def test_alloc_alignment_logic(self) -> None:
        """Alloc function contains 8-byte alignment rounding."""
        source = """\
private data Bit { Zero, One }

private fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{ 42 }
"""
        result = _compile_ok(source)
        assert "i32.const 7" in result.wat
        assert "i32.const -8" in result.wat

    def test_memory_emitted_with_adt(self) -> None:
        """ADTs cause memory to be declared even without strings."""
        source = """\
private data Flag { On, Off }

private fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{ 42 }
"""
        result = _compile_ok(source)
        assert "(memory" in result.wat


class TestAdtMetadata:
    """Test ADT constructor layout metadata registration."""

    def test_nullary_layout(self) -> None:
        """Nullary constructor: tag only, total_size = 8."""
        source = """\
private data Unit2 { MkUnit }

private fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{ 42 }
"""
        _result, gen = _compile_with_generator(source)
        layout = gen._adt_layouts["Unit2"]["MkUnit"]
        assert layout.tag == 0
        assert layout.field_offsets == ()
        assert layout.total_size == 8

    def test_single_int_field_layout(self) -> None:
        """Constructor with Int field: tag(4) + pad(4) + i64(8) = 16."""
        source = """\
private data Wrapper { Wrap(Int) }

private fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{ 42 }
"""
        _result, gen = _compile_with_generator(source)
        layout = gen._adt_layouts["Wrapper"]["Wrap"]
        assert layout.tag == 0
        assert layout.field_offsets == ((8, "i64"),)
        assert layout.total_size == 16

    def test_multiple_fields_layout(self) -> None:
        """Constructor with Int + Bool: tag(4) + pad(4) + i64(8) + i32(4) → 24."""
        source = """\
private data Pair { MkPair(Int, Bool) }

private fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{ 42 }
"""
        _result, gen = _compile_with_generator(source)
        layout = gen._adt_layouts["Pair"]["MkPair"]
        assert layout.tag == 0
        assert layout.field_offsets[0] == (8, "i64")   # Int at offset 8
        assert layout.field_offsets[1] == (16, "i32")   # Bool at offset 16
        assert layout.total_size == 24  # 20 aligned up to 24

    def test_multiple_constructors_tags(self) -> None:
        """Each constructor gets a sequential tag."""
        source = """\
private data Color { Red, Green, Blue }

private fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{ 42 }
"""
        _result, gen = _compile_with_generator(source)
        layouts = gen._adt_layouts["Color"]
        assert layouts["Red"].tag == 0
        assert layouts["Green"].tag == 1
        assert layouts["Blue"].tag == 2

    def test_float64_field_layout(self) -> None:
        """Constructor with Float64 field: tag(4) + pad(4) + f64(8) = 16."""
        source = """\
private data Box { MkBox(Float64) }

private fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{ 42 }
"""
        _result, gen = _compile_with_generator(source)
        layout = gen._adt_layouts["Box"]["MkBox"]
        assert layout.field_offsets == ((8, "f64"),)
        assert layout.total_size == 16

    def test_bool_field_layout(self) -> None:
        """Constructor with Bool field: tag(4) + i32(4) = 8."""
        source = """\
private data Toggle { MkToggle(Bool) }

private fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{ 42 }
"""
        _result, gen = _compile_with_generator(source)
        layout = gen._adt_layouts["Toggle"]["MkToggle"]
        assert layout.field_offsets == ((4, "i32"),)  # i32 aligns to 4
        assert layout.total_size == 8

    def test_type_param_is_pointer(self) -> None:
        """Type parameters map to i32 (pointer)."""
        source = """\
private data Box<T> { MkBox(T) }

private fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{ 42 }
"""
        _result, gen = _compile_with_generator(source)
        layout = gen._adt_layouts["Box"]["MkBox"]
        assert layout.field_offsets == ((4, "i32"),)  # T → pointer
        assert layout.total_size == 8

    def test_mixed_adt_constructors(self) -> None:
        """Option-like ADT: None is nullary, Some has a field."""
        source = """\
private data MyOption<T> { MyNone, MySome(T) }

private fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{ 42 }
"""
        _result, gen = _compile_with_generator(source)
        layouts = gen._adt_layouts["MyOption"]
        assert layouts["MyNone"].tag == 0
        assert layouts["MyNone"].field_offsets == ()
        assert layouts["MyNone"].total_size == 8
        assert layouts["MySome"].tag == 1
        assert layouts["MySome"].field_offsets == ((4, "i32"),)  # T → pointer
        assert layouts["MySome"].total_size == 8


# =====================================================================
# C6f: ADT constructor codegen
# =====================================================================


class TestAdtConstructors:
    """Test compilation of ADT constructor expressions to WASM."""

    def test_nullary_constructor_returns_pointer(self) -> None:
        """A nullary constructor (Red) compiles and returns an i32 >= 0."""
        source = """\
private data Color { Red, Green, Blue }

private fn make_red(-> @Color)
  requires(true) ensures(true) effects(pure)
{ Red }
"""
        result = _compile_ok(source)
        assert "make_red" in result.exports
        exec_result = execute(result, fn_name="make_red")
        assert exec_result.value is not None
        assert exec_result.value >= 0  # heap pointer

    def test_nullary_different_tags(self) -> None:
        """Different nullary constructors compile to distinct functions."""
        source = """\
private data Color { Red, Green, Blue }

private fn make_red(-> @Color)
  requires(true) ensures(true) effects(pure)
{ Red }

private fn make_green(-> @Color)
  requires(true) ensures(true) effects(pure)
{ Green }

private fn make_blue(-> @Color)
  requires(true) ensures(true) effects(pure)
{ Blue }
"""
        result = _compile_ok(source)
        assert "make_red" in result.exports
        assert "make_green" in result.exports
        assert "make_blue" in result.exports

    def test_constructor_with_int_field(self) -> None:
        """Constructor with Int field: Wrap(@Int.0) compiles."""
        source = """\
private data Wrapper { Wrap(Int) }

private fn wrap(@Int -> @Wrapper)
  requires(true) ensures(true) effects(pure)
{ Wrap(@Int.0) }
"""
        result = _compile_ok(source)
        assert "wrap" in result.exports
        exec_result = execute(result, fn_name="wrap", args=[42])
        assert exec_result.value is not None
        assert exec_result.value >= 0

    def test_constructor_with_bool_field(self) -> None:
        """Constructor with Bool field: MkToggle(@Bool.0) compiles."""
        source = """\
private data Toggle { MkToggle(Bool) }

private fn toggle(@Bool -> @Toggle)
  requires(true) ensures(true) effects(pure)
{ MkToggle(@Bool.0) }
"""
        result = _compile_ok(source)
        assert "toggle" in result.exports
        exec_result = execute(result, fn_name="toggle", args=[1])
        assert exec_result.value is not None
        assert exec_result.value >= 0

    def test_option_none(self) -> None:
        """None as Option<Int> compiles (nullary constructor)."""
        source = """\
private data Option<T> { None, Some(T) }

private fn make_none(-> @Option<Int>)
  requires(true) ensures(true) effects(pure)
{ None }
"""
        result = _compile_ok(source)
        assert "make_none" in result.exports
        exec_result = execute(result, fn_name="make_none")
        assert exec_result.value is not None

    def test_option_some(self) -> None:
        """Some(@Int.0) as Option<Int> compiles."""
        source = """\
private data Option<T> { None, Some(T) }

private fn make_some(@Int -> @Option<Int>)
  requires(true) ensures(true) effects(pure)
{ Some(@Int.0) }
"""
        result = _compile_ok(source)
        assert "make_some" in result.exports
        exec_result = execute(result, fn_name="make_some", args=[99])
        assert exec_result.value is not None
        assert exec_result.value >= 0

    def test_wat_contains_alloc_call(self) -> None:
        """WAT output for constructor contains call $alloc."""
        source = """\
private data Color { Red, Green, Blue }

private fn make_red(-> @Color)
  requires(true) ensures(true) effects(pure)
{ Red }
"""
        result = _compile_ok(source)
        assert "call $alloc" in result.wat

    def test_wat_contains_store_with_offset(self) -> None:
        """WAT output for Some(x) contains field store with offset."""
        source = """\
private data Wrapper { Wrap(Int) }

private fn wrap(@Int -> @Wrapper)
  requires(true) ensures(true) effects(pure)
{ Wrap(@Int.0) }
"""
        result = _compile_ok(source)
        assert "i64.store offset=8" in result.wat

    def test_nullary_tag_store(self) -> None:
        """WAT for Red (tag=0) stores tag 0; Green (tag=1) stores tag 1."""
        source = """\
private data Color { Red, Green, Blue }

private fn make_green(-> @Color)
  requires(true) ensures(true) effects(pure)
{ Green }
"""
        result = _compile_ok(source)
        # Green has tag=1, so WAT should contain i32.const 1 before i32.store
        assert "i32.const 1" in result.wat
        assert "i32.store\n" in result.wat or "i32.store)" in result.wat or "i32.store" in result.wat

    def test_constructor_in_let_binding(self) -> None:
        """Constructor result in a let binding compiles."""
        source = """\
private data Wrapper { Wrap(Int) }

private fn make_wrap(@Int -> @Wrapper)
  requires(true) ensures(true) effects(pure)
{
  let @Wrapper = Wrap(@Int.0);
  @Wrapper.0
}
"""
        result = _compile_ok(source)
        assert "make_wrap" in result.exports
        exec_result = execute(result, fn_name="make_wrap", args=[7])
        assert exec_result.value is not None

    def test_constructor_in_if_branches(self) -> None:
        """Constructors in both branches of if-then-else compile."""
        source = """\
private data Option<T> { None, Some(T) }

private fn maybe(@Bool -> @Option<Int>)
  requires(true) ensures(true) effects(pure)
{
  if @Bool.0 then { Some(42) }
  else { None }
}
"""
        result = _compile_ok(source)
        assert "maybe" in result.exports
        # Both branches should produce valid pointers
        exec_true = execute(result, fn_name="maybe", args=[1])
        exec_false = execute(result, fn_name="maybe", args=[0])
        assert exec_true.value is not None
        assert exec_false.value is not None

    def test_adt_param_compiles(self) -> None:
        """Function taking ADT param uses (param $p0 i32) in WAT."""
        source = """\
private data Color { Red, Green, Blue }

private fn identity(@Color -> @Color)
  requires(true) ensures(true) effects(pure)
{ @Color.0 }
"""
        result = _compile_ok(source)
        assert "identity" in result.exports
        assert "(param" in result.wat  # at least one i32 param


# =====================================================================
# C6g: Match expression codegen
# =====================================================================


class TestMatchExpressions:
    """Test compilation of match expressions to WASM."""

    def test_match_option_none_arm(self) -> None:
        """Match on None arm returns 0."""
        source = """\
private data Option<T> { None, Some(T) }

private fn test_none(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Option<Int> = None;
  match @Option<Int>.0 {
    None -> 0,
    Some(@Int) -> @Int.0
  }
}
"""
        assert _run(source, fn="test_none") == 0

    def test_match_option_some_arm(self) -> None:
        """Match on Some arm extracts value."""
        source = """\
private data Option<T> { None, Some(T) }

private fn test_some(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Option<Int> = Some(42);
  match @Option<Int>.0 {
    None -> 0,
    Some(@Int) -> @Int.0
  }
}
"""
        assert _run(source, fn="test_some") == 42

    def test_match_color_red(self) -> None:
        """Match on Red arm returns 0."""
        source = """\
private data Color { Red, Green, Blue }

private fn test_red(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Color = Red;
  match @Color.0 {
    Red -> 0,
    Green -> 1,
    Blue -> 2
  }
}
"""
        assert _run(source, fn="test_red") == 0

    def test_match_color_green(self) -> None:
        """Match on Green arm returns 1."""
        source = """\
private data Color { Red, Green, Blue }

private fn test_green(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Color = Green;
  match @Color.0 {
    Red -> 0,
    Green -> 1,
    Blue -> 2
  }
}
"""
        assert _run(source, fn="test_green") == 1

    def test_match_color_blue(self) -> None:
        """Match on Blue arm returns 2."""
        source = """\
private data Color { Red, Green, Blue }

private fn test_blue(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Color = Blue;
  match @Color.0 {
    Red -> 0,
    Green -> 1,
    Blue -> 2
  }
}
"""
        assert _run(source, fn="test_blue") == 2

    def test_match_extracts_int(self) -> None:
        """Match extracts Int field and uses it in body."""
        source = """\
private data Option<T> { None, Some(T) }

private fn test(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Option<Int> = Some(99);
  match @Option<Int>.0 {
    None -> 0,
    Some(@Int) -> @Int.0 + 1
  }
}
"""
        assert _run(source, fn="test") == 100

    def test_match_extracts_bool(self) -> None:
        """Match extracts Bool field."""
        source = """\
private data Toggle { MkToggle(Bool) }

private fn test(-> @Bool)
  requires(true) ensures(true) effects(pure)
{
  let @Toggle = MkToggle(true);
  match @Toggle.0 {
    MkToggle(@Bool) -> @Bool.0
  }
}
"""
        assert _run(source, fn="test") == 1

    def test_match_two_fields(self) -> None:
        """Match extracts first of two fields."""
        source = """\
private data Pair { MkPair(Int, Bool) }

private fn test(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Pair = MkPair(42, true);
  match @Pair.0 {
    MkPair(@Int, @Bool) -> @Int.0
  }
}
"""
        assert _run(source, fn="test") == 42

    def test_match_wildcard_catchall(self) -> None:
        """Wildcard catch-all matches None."""
        source = """\
private data Option<T> { None, Some(T) }

private fn test(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Option<Int> = None;
  match @Option<Int>.0 {
    Some(@Int) -> @Int.0,
    _ -> 0
  }
}
"""
        assert _run(source, fn="test") == 0

    def test_match_wildcard_only(self) -> None:
        """Single wildcard arm on Int."""
        source = """\
private fn test(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  match @Int.0 {
    _ -> 42
  }
}
"""
        assert _run(source, fn="test", args=[999]) == 42

    def test_match_wildcard_sub_pattern(self) -> None:
        """Wildcard inside constructor sub-pattern."""
        source = """\
private data Option<T> { None, Some(T) }

private fn test(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Option<Int> = Some(77);
  match @Option<Int>.0 {
    Some(_) -> 1,
    None -> 0
  }
}
"""
        assert _run(source, fn="test") == 1

    def test_match_bool_true(self) -> None:
        """Bool match on true arm."""
        source = """\
private fn test(@Bool -> @Int)
  requires(true) ensures(true) effects(pure)
{
  match @Bool.0 {
    true -> 1,
    false -> 0
  }
}
"""
        assert _run(source, fn="test", args=[1]) == 1

    def test_match_bool_false(self) -> None:
        """Bool match on false arm."""
        source = """\
private fn test(@Bool -> @Int)
  requires(true) ensures(true) effects(pure)
{
  match @Bool.0 {
    true -> 1,
    false -> 0
  }
}
"""
        assert _run(source, fn="test", args=[0]) == 0

    def test_match_int_literal(self) -> None:
        """Int literal match, first arm."""
        source = """\
private fn test(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  match @Int.0 {
    0 -> 100,
    1 -> 200,
    _ -> 300
  }
}
"""
        assert _run(source, fn="test", args=[0]) == 100

    def test_match_int_second_arm(self) -> None:
        """Int literal match, second arm."""
        source = """\
private fn test(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  match @Int.0 {
    0 -> 100,
    1 -> 200,
    _ -> 300
  }
}
"""
        assert _run(source, fn="test", args=[1]) == 200

    def test_match_int_wildcard_fallback(self) -> None:
        """Int literal match, wildcard fallback."""
        source = """\
private fn test(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  match @Int.0 {
    0 -> 100,
    1 -> 200,
    _ -> 300
  }
}
"""
        assert _run(source, fn="test", args=[99]) == 300

    def test_match_binding_catchall(self) -> None:
        """Binding pattern as catch-all."""
        source = """\
private data Option<T> { None, Some(T) }

private fn test(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Option<Int> = None;
  match @Option<Int>.0 {
    Some(@Int) -> @Int.0,
    @Option<Int> -> 0
  }
}
"""
        assert _run(source, fn="test") == 0

    def test_match_in_let_binding(self) -> None:
        """Match result used in a let binding."""
        source = """\
private data Option<T> { None, Some(T) }

private fn test(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Option<Int> = Some(10);
  let @Int = match @Option<Int>.0 {
    None -> 0,
    Some(@Int) -> @Int.0
  };
  @Int.0 + 1
}
"""
        assert _run(source, fn="test") == 11

    def test_match_wat_contains_tag_load(self) -> None:
        """WAT output for ADT match contains i32.load (tag load)."""
        source = """\
private data Color { Red, Green, Blue }

private fn test(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Color = Red;
  match @Color.0 {
    Red -> 0,
    Green -> 1,
    Blue -> 2
  }
}
"""
        result = _compile_ok(source)
        assert "i32.load" in result.wat

    def test_match_function_compiles(self) -> None:
        """Function with match is now exported (not skipped)."""
        source = """\
private data Option<T> { None, Some(T) }

private fn unwrap_or(@Option<Int> -> @Int)
  requires(true) ensures(true) effects(pure)
{
  match @Option<Int>.0 {
    None -> 0,
    Some(@Int) -> @Int.0
  }
}
"""
        result = _compile_ok(source)
        assert "unwrap_or" in result.exports


# =====================================================================
# C6i: Monomorphization of generic (forall<T>) functions
# =====================================================================


class TestMonomorphization:
    """Tests for monomorphization of forall<T> functions."""

    def test_identity_int(self) -> None:
        """forall<T> fn identity instantiated with Int."""
        source = """\
private forall<T> fn identity(@T -> @T)
  requires(true) ensures(true) effects(pure)
{ @T.0 }

private fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ identity(42) }
"""
        assert _run(source, fn="main") == 42

    def test_identity_bool(self) -> None:
        """forall<T> fn identity instantiated with Bool."""
        source = """\
private forall<T> fn identity(@T -> @T)
  requires(true) ensures(true) effects(pure)
{ @T.0 }

private fn main(-> @Bool)
  requires(true) ensures(true) effects(pure)
{ identity(true) }
"""
        assert _run(source, fn="main") == 1

    def test_identity_two_instantiations(self) -> None:
        """Same generic function instantiated with both Int and Bool."""
        source = """\
private forall<T> fn identity(@T -> @T)
  requires(true) ensures(true) effects(pure)
{ @T.0 }

private fn test_int(-> @Int)
  requires(true) ensures(true) effects(pure)
{ identity(42) }

private fn test_bool(-> @Bool)
  requires(true) ensures(true) effects(pure)
{ identity(false) }
"""
        result = _compile_ok(source)
        assert "identity$Int" in result.exports
        assert "identity$Bool" in result.exports
        # Run both
        exec_int = execute(result, fn_name="test_int")
        assert exec_int.value == 42
        exec_bool = execute(result, fn_name="test_bool")
        assert exec_bool.value == 0

    def test_identity_slot_ref_arg(self) -> None:
        """Generic function called with a slot reference argument."""
        source = """\
private forall<T> fn identity(@T -> @T)
  requires(true) ensures(true) effects(pure)
{ @T.0 }

private fn main(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ identity(@Int.0) }
"""
        assert _run(source, fn="main", args=[99]) == 99

    def test_const_function(self) -> None:
        """forall<A, B> fn const with two type parameters."""
        source = """\
private forall<A, B> fn const(@A, @B -> @A)
  requires(true) ensures(true) effects(pure)
{ @A.0 }

private fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ const(42, true) }
"""
        assert _run(source, fn="main") == 42

    def test_generic_with_adt_match(self) -> None:
        """forall<T> fn is_some with ADT match (Some case)."""
        source = """\
private data Option<T> { None, Some(T) }

private forall<T> fn is_some(@Option<T> -> @Bool)
  requires(true) ensures(true) effects(pure)
{
  match @Option<T>.0 {
    None -> false,
    Some(@T) -> true
  }
}

private fn main(-> @Bool)
  requires(true) ensures(true) effects(pure)
{ is_some(Some(1)) }
"""
        assert _run(source, fn="main") == 1

    def test_generic_with_adt_match_none(self) -> None:
        """forall<T> fn is_some with ADT match (None case)."""
        source = """\
private data Option<T> { None, Some(T) }

private forall<T> fn is_some(@Option<T> -> @Bool)
  requires(true) ensures(true) effects(pure)
{
  match @Option<T>.0 {
    None -> false,
    Some(@T) -> true
  }
}

private fn main(-> @Bool)
  requires(true) ensures(true) effects(pure)
{
  let @Option<Int> = None;
  is_some(@Option<Int>.0)
}
"""
        assert _run(source, fn="main") == 0

    def test_generic_fn_wat_has_mangled_name(self) -> None:
        """WAT output contains mangled function name."""
        source = """\
private forall<T> fn identity(@T -> @T)
  requires(true) ensures(true) effects(pure)
{ @T.0 }

private fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ identity(42) }
"""
        result = _compile_ok(source)
        assert "$identity$Int" in result.wat

    def test_generic_fn_mangled_in_exports(self) -> None:
        """Mangled name appears in exports, original generic does not."""
        source = """\
private forall<T> fn identity(@T -> @T)
  requires(true) ensures(true) effects(pure)
{ @T.0 }

private fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ identity(42) }
"""
        result = _compile_ok(source)
        assert "identity$Int" in result.exports
        assert "identity" not in result.exports

    def test_non_generic_fn_unaffected(self) -> None:
        """Non-generic functions compile normally alongside generic ones."""
        source = """\
private forall<T> fn identity(@T -> @T)
  requires(true) ensures(true) effects(pure)
{ @T.0 }

private fn double(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 + @Int.0 }

private fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ double(identity(21)) }
"""
        assert _run(source, fn="main") == 42

    def test_generic_identity_in_let_binding(self) -> None:
        """Generic call result used in a let binding."""
        source = """\
private forall<T> fn identity(@T -> @T)
  requires(true) ensures(true) effects(pure)
{ @T.0 }

private fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Int = identity(10);
  @Int.0 + 5
}
"""
        assert _run(source, fn="main") == 15

    def test_generic_chained_calls(self) -> None:
        """Generic function called with result of another generic call."""
        source = """\
private forall<T> fn identity(@T -> @T)
  requires(true) ensures(true) effects(pure)
{ @T.0 }

private fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ identity(identity(99)) }
"""
        assert _run(source, fn="main") == 99

    def test_generic_in_if_branch(self) -> None:
        """Generic call inside an if-then-else branch."""
        source = """\
private forall<T> fn identity(@T -> @T)
  requires(true) ensures(true) effects(pure)
{ @T.0 }

private fn main(@Bool -> @Int)
  requires(true) ensures(true) effects(pure)
{
  if @Bool.0 then { identity(1) } else { identity(2) }
}
"""
        assert _run(source, fn="main", args=[1]) == 1
        assert _run(source, fn="main", args=[0]) == 2

    def test_generic_with_arithmetic_arg(self) -> None:
        """Generic function called with arithmetic expression as argument."""
        source = """\
private forall<T> fn identity(@T -> @T)
  requires(true) ensures(true) effects(pure)
{ @T.0 }

private fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ identity(3 + 4) }
"""
        assert _run(source, fn="main") == 7

    def test_generic_no_callers_skipped(self) -> None:
        """Generic function with no callers is gracefully skipped."""
        source = """\
private forall<T> fn identity(@T -> @T)
  requires(true) ensures(true) effects(pure)
{ @T.0 }

private fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ 42 }
"""
        result = _compile_ok(source)
        assert "main" in result.exports
        # identity has no callers → no monomorphized version → not in exports
        assert "identity" not in result.exports

    def test_generics_example_file(self) -> None:
        """examples/generics.vera compiles without errors."""
        from pathlib import Path
        path = Path(__file__).parent.parent / "examples" / "generics.vera"
        source = path.read_text()
        result = _compile(source)
        assert result.ok

    def test_list_ops_example_file(self) -> None:
        """examples/list_ops.vera still compiles (concrete, not generic)."""
        from pathlib import Path
        path = Path(__file__).parent.parent / "examples" / "list_ops.vera"
        source = path.read_text()
        result = _compile(source)
        assert result.ok


# =====================================================================
# C6h: Closures
# =====================================================================


class TestClosures:
    """Tests for closure compilation — anonymous functions, captures,
    apply_fn, function tables, and call_indirect."""

    def test_closure_no_capture(self) -> None:
        """An anonymous function with no free variables compiles and runs."""
        src = """\
type IntToInt = fn(Int -> Int) effects(pure);
private fn make_fn(@Unit -> @IntToInt)
  requires(true) ensures(true) effects(pure)
{
  fn(@Int -> @Int) effects(pure) { @Int.0 * 2 }
}
private fn test(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @IntToInt = make_fn(());
  apply_fn(@IntToInt.0, 7)
}
"""
        assert _run(src, "test") == 14

    def test_closure_with_capture(self) -> None:
        """An anonymous function that captures an outer binding."""
        src = """\
type IntToInt = fn(Int -> Int) effects(pure);
private fn make_adder(@Int -> @IntToInt)
  requires(true) ensures(true) effects(pure)
{
  fn(@Int -> @Int) effects(pure) { @Int.0 + @Int.1 }
}
private fn test(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @IntToInt = make_adder(10);
  apply_fn(@IntToInt.0, 5)
}
"""
        assert _run(src, "test") == 15

    def test_apply_fn_basic(self) -> None:
        """apply_fn invokes a closure with the correct argument."""
        src = """\
type IntToInt = fn(Int -> Int) effects(pure);
private fn make_doubler(@Unit -> @IntToInt)
  requires(true) ensures(true) effects(pure)
{
  fn(@Int -> @Int) effects(pure) { @Int.0 * 2 }
}
private fn test(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @IntToInt = make_doubler(());
  apply_fn(@IntToInt.0, 21)
}
"""
        assert _run(src, "test") == 42

    def test_apply_fn_with_capture(self) -> None:
        """apply_fn on a capturing closure produces the correct result."""
        src = """\
type IntToInt = fn(Int -> Int) effects(pure);
private fn make_multiplier(@Int -> @IntToInt)
  requires(true) ensures(true) effects(pure)
{
  fn(@Int -> @Int) effects(pure) { @Int.0 * @Int.1 }
}
private fn test(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @IntToInt = make_multiplier(3);
  apply_fn(@IntToInt.0, 7)
}
"""
        assert _run(src, "test") == 21

    def test_closure_in_let(self) -> None:
        """Store a closure in a let binding, then use it."""
        src = """\
type IntToInt = fn(Int -> Int) effects(pure);
private fn make_fn(@Int -> @IntToInt)
  requires(true) ensures(true) effects(pure)
{
  fn(@Int -> @Int) effects(pure) { @Int.0 + @Int.1 }
}
private fn test(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @IntToInt = make_fn(100);
  let @Int = apply_fn(@IntToInt.0, 23);
  @Int.0
}
"""
        assert _run(src, "test") == 123

    def test_closure_as_param(self) -> None:
        """Pass a closure as a function parameter."""
        src = """\
type IntToInt = fn(Int -> Int) effects(pure);
private fn apply(@IntToInt, @Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  apply_fn(@IntToInt.0, @Int.0)
}
private fn make_fn(@Int -> @IntToInt)
  requires(true) ensures(true) effects(pure)
{
  fn(@Int -> @Int) effects(pure) { @Int.0 + @Int.1 }
}
private fn test(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @IntToInt = make_fn(50);
  apply(@IntToInt.0, 50)
}
"""
        assert _run(src, "test") == 100

    def test_closure_in_match(self) -> None:
        """Use a closure inside a match arm with an ADT constructor."""
        src = """\
private data Option<T> { None, Some(T) }
type IntMapper = fn(Int -> Int) effects(pure);
private fn map_option(@Option<Int>, @IntMapper -> @Option<Int>)
  requires(true) ensures(true) effects(pure)
{
  match @Option<Int>.0 {
    None -> None,
    Some(@Int) -> Some(apply_fn(@IntMapper.0, @Int.0))
  }
}
private fn make_adder(@Int -> @IntMapper)
  requires(true) ensures(true) effects(pure)
{
  fn(@Int -> @Int) effects(pure) { @Int.0 + @Int.1 }
}
private fn test(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @IntMapper = make_adder(100);
  let @Option<Int> = map_option(Some(5), @IntMapper.0);
  match @Option<Int>.0 {
    None -> 0,
    Some(@Int) -> @Int.0
  }
}
"""
        assert _run(src, "test") == 105

    def test_closure_in_match_none(self) -> None:
        """map_option on None returns None."""
        src = """\
private data Option<T> { None, Some(T) }
type IntMapper = fn(Int -> Int) effects(pure);
private fn map_option(@Option<Int>, @IntMapper -> @Option<Int>)
  requires(true) ensures(true) effects(pure)
{
  match @Option<Int>.0 {
    None -> None,
    Some(@Int) -> Some(apply_fn(@IntMapper.0, @Int.0))
  }
}
private fn make_adder(@Int -> @IntMapper)
  requires(true) ensures(true) effects(pure)
{
  fn(@Int -> @Int) effects(pure) { @Int.0 + @Int.1 }
}
private fn test(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @IntMapper = make_adder(100);
  let @Option<Int> = map_option(None, @IntMapper.0);
  match @Option<Int>.0 {
    None -> -1,
    Some(@Int) -> @Int.0
  }
}
"""
        assert _run(src, "test") == -1

    def test_fn_type_param_compiles(self) -> None:
        """A function with a function-type parameter is not skipped."""
        src = """\
type IntToInt = fn(Int -> Int) effects(pure);
private fn apply(@IntToInt, @Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  apply_fn(@IntToInt.0, @Int.0)
}
"""
        result = _compile_ok(src)
        assert "apply" in result.exports

    def test_table_in_wat(self) -> None:
        """WAT output includes a funcref table when closures are used."""
        src = """\
type IntToInt = fn(Int -> Int) effects(pure);
private fn make_fn(@Unit -> @IntToInt)
  requires(true) ensures(true) effects(pure)
{
  fn(@Int -> @Int) effects(pure) { @Int.0 }
}
"""
        result = _compile_ok(src)
        assert result.wat is not None
        assert "funcref" in result.wat
        assert "(table" in result.wat
        assert "(elem" in result.wat

    def test_call_indirect_in_wat(self) -> None:
        """WAT output contains call_indirect for apply_fn."""
        src = """\
type IntToInt = fn(Int -> Int) effects(pure);
private fn apply(@IntToInt, @Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  apply_fn(@IntToInt.0, @Int.0)
}
private fn make_fn(@Unit -> @IntToInt)
  requires(true) ensures(true) effects(pure)
{
  fn(@Int -> @Int) effects(pure) { @Int.0 }
}
private fn test(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @IntToInt = make_fn(());
  apply(@IntToInt.0, 99)
}
"""
        result = _compile_ok(src)
        assert result.wat is not None
        assert "call_indirect" in result.wat

    def test_type_sig_in_wat(self) -> None:
        """WAT output contains a closure type signature declaration."""
        src = """\
type IntToInt = fn(Int -> Int) effects(pure);
private fn make_fn(@Unit -> @IntToInt)
  requires(true) ensures(true) effects(pure)
{
  fn(@Int -> @Int) effects(pure) { @Int.0 }
}
"""
        result = _compile_ok(src)
        assert result.wat is not None
        assert "$closure_sig_" in result.wat
        assert "(type" in result.wat

    def test_closures_example_compiles(self) -> None:
        """examples/closures.vera compiles without errors."""
        from pathlib import Path
        path = Path(__file__).parent.parent / "examples" / "closures.vera"
        source = path.read_text()
        result = _compile(source)
        assert result.ok

    def test_closures_example_test_closure(self) -> None:
        """examples/closures.vera test_closure returns 15."""
        from pathlib import Path
        path = Path(__file__).parent.parent / "examples" / "closures.vera"
        source = path.read_text()
        result = _compile_ok(source)
        exec_result = execute(result, fn_name="test_closure")
        assert exec_result.value == 15

    def test_closures_example_test_map_option(self) -> None:
        """examples/closures.vera test_map_option returns 105."""
        from pathlib import Path
        path = Path(__file__).parent.parent / "examples" / "closures.vera"
        source = path.read_text()
        result = _compile_ok(source)
        exec_result = execute(result, fn_name="test_map_option")
        assert exec_result.value == 105

    def test_multiple_closures(self) -> None:
        """Multiple closures get distinct table entries."""
        src = """\
type IntToInt = fn(Int -> Int) effects(pure);
private fn make_adder(@Int -> @IntToInt)
  requires(true) ensures(true) effects(pure)
{
  fn(@Int -> @Int) effects(pure) { @Int.0 + @Int.1 }
}
private fn test(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @IntToInt = make_adder(10);
  let @Int = apply_fn(@IntToInt.0, 5);
  let @IntToInt = make_adder(20);
  let @Int = apply_fn(@IntToInt.0, 3);
  @Int.0 + @Int.1
}
"""
        assert _run(src, "test") == 38  # 15 + 23

    def test_closure_captures_correct_value(self) -> None:
        """Each closure captures the value at its creation point."""
        src = """\
type IntToInt = fn(Int -> Int) effects(pure);
private fn make_adder(@Int -> @IntToInt)
  requires(true) ensures(true) effects(pure)
{
  fn(@Int -> @Int) effects(pure) { @Int.0 + @Int.1 }
}
private fn test(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @IntToInt = make_adder(1);
  let @Int = apply_fn(@IntToInt.0, 0);
  let @IntToInt = make_adder(100);
  let @Int = apply_fn(@IntToInt.0, 0);
  @Int.0 + @Int.1
}
"""
        assert _run(src, "test") == 101  # 1 + 100


# =====================================================================
# C6j: Effect Handlers
# =====================================================================


class TestEffectHandlers:
    """Tests for handle[State<T>] compilation — State handlers via
    host imports, state initialization, get/put in handler body."""

    _STATE_HANDLER = """\
    get(@Unit) -> { resume(@Int.0) },
    put(@Int) -> { resume(()) }
"""

    def test_handle_state_get_init(self) -> None:
        """handle[State<Int>](@Int = 42) in { get(()) } returns 42."""
        src = """\
private fn test(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  handle[State<Int>](@Int = 42) {
    get(@Unit) -> { resume(@Int.0) },
    put(@Int) -> { resume(()) }
  } in {
    get(())
  }
}
"""
        assert _run(src, "test") == 42

    def test_handle_state_put_get(self) -> None:
        """put then get returns the put value."""
        src = """\
private fn test(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  handle[State<Int>](@Int = 0) {
    get(@Unit) -> { resume(@Int.0) },
    put(@Int) -> { resume(()) }
  } in {
    put(99);
    get(())
  }
}
"""
        assert _run(src, "test") == 99

    def test_handle_state_increment(self) -> None:
        """put(get(()) + 1) increments the state."""
        src = """\
private fn test(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  handle[State<Int>](@Int = 0) {
    get(@Unit) -> { resume(@Int.0) },
    put(@Int) -> { resume(()) }
  } in {
    put(get(()) + 1);
    get(())
  }
}
"""
        assert _run(src, "test") == 1

    def test_handle_state_run_counter(self) -> None:
        """The run_counter pattern: init 0, put 0, then 3x increment."""
        src = """\
private fn test(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  handle[State<Int>](@Int = 0) {
    get(@Unit) -> { resume(@Int.0) },
    put(@Int) -> { resume(()) }
  } in {
    put(0);
    put(get(()) + 1);
    put(get(()) + 1);
    put(get(()) + 1);
    get(())
  }
}
"""
        assert _run(src, "test") == 3

    def test_handle_state_initial_value(self) -> None:
        """Non-zero initial state is set correctly."""
        src = """\
private fn test(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  handle[State<Int>](@Int = 100) {
    get(@Unit) -> { resume(@Int.0) },
    put(@Int) -> { resume(()) }
  } in {
    put(get(()) + 5);
    get(())
  }
}
"""
        assert _run(src, "test") == 105

    def test_handle_state_in_let(self) -> None:
        """Handler body can use let bindings."""
        src = """\
private fn test(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  handle[State<Int>](@Int = 0) {
    get(@Unit) -> { resume(@Int.0) },
    put(@Int) -> { resume(()) }
  } in {
    put(10);
    let @Int = get(());
    put(@Int.0 + 5);
    get(())
  }
}
"""
        assert _run(src, "test") == 15

    def test_handle_state_pure_function(self) -> None:
        """A pure function with handle[State<T>] compiles (not skipped)."""
        src = """\
private fn test(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  handle[State<Int>](@Int = 7) {
    get(@Unit) -> { resume(@Int.0) },
    put(@Int) -> { resume(()) }
  } in {
    get(())
  }
}
"""
        result = _compile_ok(src)
        assert "test" in result.exports

    def test_handle_state_bool(self) -> None:
        """State<Bool> handler works."""
        src = """\
private fn test(@Unit -> @Bool)
  requires(true) ensures(true) effects(pure)
{
  handle[State<Bool>](@Bool = false) {
    get(@Unit) -> { resume(@Bool.0) },
    put(@Bool) -> { resume(()) }
  } in {
    put(true);
    get(())
  }
}
"""
        assert _run(src, "test") == 1  # true = 1

    def test_handle_state_wat_has_imports(self) -> None:
        """WAT output contains state host imports."""
        src = """\
private fn test(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  handle[State<Int>](@Int = 0) {
    get(@Unit) -> { resume(@Int.0) },
    put(@Int) -> { resume(()) }
  } in {
    get(())
  }
}
"""
        result = _compile_ok(src)
        assert result.wat is not None
        assert "state_get_Int" in result.wat
        assert "state_put_Int" in result.wat
        assert "(import" in result.wat

    def test_unsupported_handler_skipped(self) -> None:
        """Non-State handler causes function to be skipped."""
        src = """\
effect Exn<E> {
  op throw(E -> Unit);
}
private data Option<T> { None, Some(T) }
private fn test(@Int -> @Option<Int>)
  requires(true) ensures(true) effects(pure)
{
  handle[Exn<Int>] {
    throw(@Int) -> { None }
  } in {
    Some(@Int.0)
  }
}
"""
        result = _compile(src)
        # Function should be skipped (Exn handler not supported)
        assert "test" not in result.exports

    def test_effect_handler_example_compiles(self) -> None:
        """examples/effect_handler.vera compiles without errors."""
        from pathlib import Path
        path = Path(__file__).parent.parent / "examples" / "effect_handler.vera"
        source = path.read_text()
        result = _compile(source)
        assert result.ok

    def test_effect_handler_example_run_counter(self) -> None:
        """examples/effect_handler.vera run_counter returns 3."""
        from pathlib import Path
        path = Path(__file__).parent.parent / "examples" / "effect_handler.vera"
        source = path.read_text()
        result = _compile_ok(source)
        exec_result = execute(result, fn_name="run_counter")
        assert exec_result.value == 3

    def test_effect_handler_example_test_state_init(self) -> None:
        """examples/effect_handler.vera test_state_init returns 42."""
        from pathlib import Path
        path = Path(__file__).parent.parent / "examples" / "effect_handler.vera"
        source = path.read_text()
        result = _compile_ok(source)
        exec_result = execute(result, fn_name="test_state_init")
        assert exec_result.value == 42

    def test_effect_handler_example_test_put_get(self) -> None:
        """examples/effect_handler.vera test_put_get returns 99."""
        from pathlib import Path
        path = Path(__file__).parent.parent / "examples" / "effect_handler.vera"
        source = path.read_text()
        result = _compile_ok(source)
        exec_result = execute(result, fn_name="test_put_get")
        assert exec_result.value == 99


# =====================================================================
# C6k: Byte type
# =====================================================================


class TestByteType:
    def test_byte_identity(self) -> None:
        src = """
private fn f(@Byte -> @Byte) requires(true) ensures(true) effects(pure) {
  @Byte.0
}
"""
        assert _run(src, fn="f", args=[42]) == 42

    def test_byte_zero(self) -> None:
        src = """
private fn f(-> @Byte) requires(true) ensures(true) effects(pure) {
  0
}
"""
        assert _run(src) == 0

    def test_byte_max(self) -> None:
        src = """
private fn f(-> @Byte) requires(true) ensures(true) effects(pure) {
  255
}
"""
        assert _run(src) == 255

    def test_byte_let_binding(self) -> None:
        src = """
private fn f(@Byte -> @Byte) requires(true) ensures(true) effects(pure) {
  let @Byte = @Byte.0;
  @Byte.0
}
"""
        assert _run(src, fn="f", args=[100]) == 100

    def test_byte_eq(self) -> None:
        src = """
private fn f(@Byte, @Byte -> @Bool) requires(true) ensures(true) effects(pure) {
  @Byte.0 == @Byte.1
}
"""
        assert _run(src, fn="f", args=[5, 5]) == 1
        assert _run(src, fn="f", args=[5, 6]) == 0

    def test_byte_lt_unsigned(self) -> None:
        # @Byte.0 = second param (de Bruijn 0), @Byte.1 = first param
        src = """
private fn f(@Byte, @Byte -> @Bool) requires(true) ensures(true) effects(pure) {
  @Byte.0 < @Byte.1
}
"""
        # f(200, 10): @Byte.0=10, @Byte.1=200 → 10 < 200 = true
        assert _run(src, fn="f", args=[200, 10]) == 1
        # f(10, 200): @Byte.0=200, @Byte.1=10 → 200 < 10 = false
        assert _run(src, fn="f", args=[10, 200]) == 0

    def test_byte_gt_unsigned(self) -> None:
        src = """
private fn f(@Byte, @Byte -> @Bool) requires(true) ensures(true) effects(pure) {
  @Byte.0 > @Byte.1
}
"""
        # f(10, 200): @Byte.0=200, @Byte.1=10 → 200 > 10 = true
        assert _run(src, fn="f", args=[10, 200]) == 1
        # f(200, 10): @Byte.0=10, @Byte.1=200 → 10 > 200 = false
        assert _run(src, fn="f", args=[200, 10]) == 0

    def test_byte_le(self) -> None:
        src = """
private fn f(@Byte, @Byte -> @Bool) requires(true) ensures(true) effects(pure) {
  @Byte.0 <= @Byte.1
}
"""
        assert _run(src, fn="f", args=[5, 5]) == 1
        # f(6, 5): @Byte.0=5, @Byte.1=6 → 5 <= 6 = true
        assert _run(src, fn="f", args=[6, 5]) == 1
        # f(5, 6): @Byte.0=6, @Byte.1=5 → 6 <= 5 = false
        assert _run(src, fn="f", args=[5, 6]) == 0

    def test_byte_ge(self) -> None:
        src = """
private fn f(@Byte, @Byte -> @Bool) requires(true) ensures(true) effects(pure) {
  @Byte.0 >= @Byte.1
}
"""
        assert _run(src, fn="f", args=[5, 5]) == 1
        # f(5, 6): @Byte.0=6, @Byte.1=5 → 6 >= 5 = true
        assert _run(src, fn="f", args=[5, 6]) == 1
        # f(6, 5): @Byte.0=5, @Byte.1=6 → 5 >= 6 = false
        assert _run(src, fn="f", args=[6, 5]) == 0

    def test_byte_unsigned_comparison_wat(self) -> None:
        """Byte comparisons should use unsigned i32 ops."""
        src = """
private fn f(@Byte, @Byte -> @Bool) requires(true) ensures(true) effects(pure) {
  @Byte.0 < @Byte.1
}
"""
        result = _compile_ok(src)
        assert "i32.lt_u" in result.wat


# =====================================================================
# C6k: Array literals
# =====================================================================


class TestArrayLit:
    def test_int_array_index_0(self) -> None:
        src = """
private fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Array<Int> = [10, 20, 30];
  @Array<Int>.0[0]
}
"""
        assert _run(src) == 10

    def test_int_array_index_1(self) -> None:
        src = """
private fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Array<Int> = [10, 20, 30];
  @Array<Int>.0[1]
}
"""
        assert _run(src) == 20

    def test_int_array_index_2(self) -> None:
        src = """
private fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Array<Int> = [10, 20, 30];
  @Array<Int>.0[2]
}
"""
        assert _run(src) == 30

    def test_single_element_array(self) -> None:
        src = """
private fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Array<Int> = [42];
  @Array<Int>.0[0]
}
"""
        assert _run(src) == 42

    def test_bool_array(self) -> None:
        src = """
private fn f(-> @Bool) requires(true) ensures(true) effects(pure) {
  let @Array<Bool> = [true, false, true];
  @Array<Bool>.0[1]
}
"""
        assert _run(src) == 0

    def test_array_wat_has_alloc(self) -> None:
        """Array literal WAT should contain call $alloc."""
        src = """
private fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Array<Int> = [1, 2, 3];
  @Array<Int>.0[0]
}
"""
        result = _compile_ok(src)
        assert "call $alloc" in result.wat

    def test_array_wat_has_bounds_check(self) -> None:
        """Array indexing WAT should contain unreachable for OOB."""
        src = """
private fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Array<Int> = [1, 2, 3];
  @Array<Int>.0[0]
}
"""
        result = _compile_ok(src)
        assert "unreachable" in result.wat


# =====================================================================
# C6k: Array bounds checking
# =====================================================================


class TestArrayBoundsCheck:
    def test_oob_positive_index(self) -> None:
        src = """
private fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Array<Int> = [10, 20, 30];
  @Array<Int>.0[3]
}
"""
        _run_trap(src)

    def test_oob_large_index(self) -> None:
        src = """
private fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Array<Int> = [10, 20, 30];
  @Array<Int>.0[100]
}
"""
        _run_trap(src)

    def test_last_valid_index(self) -> None:
        src = """
private fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Array<Int> = [10, 20, 30];
  @Array<Int>.0[2]
}
"""
        assert _run(src) == 30

    def test_first_valid_index(self) -> None:
        src = """
private fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Array<Int> = [10, 20, 30];
  @Array<Int>.0[0]
}
"""
        assert _run(src) == 10


# =====================================================================
# C6k: Array length
# =====================================================================


class TestArrayLength:
    def test_length_three(self) -> None:
        src = """
private fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Array<Int> = [10, 20, 30];
  length(@Array<Int>.0)
}
"""
        assert _run(src) == 3

    def test_length_one(self) -> None:
        src = """
private fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Array<Int> = [42];
  length(@Array<Int>.0)
}
"""
        assert _run(src) == 1

    def test_length_in_comparison(self) -> None:
        src = """
private fn f(-> @Bool) requires(true) ensures(true) effects(pure) {
  let @Array<Int> = [10, 20, 30];
  length(@Array<Int>.0) == 3
}
"""
        assert _run(src) == 1

    def test_length_in_let(self) -> None:
        src = """
private fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Array<Int> = [1, 2, 3, 4, 5];
  let @Int = length(@Array<Int>.0);
  @Int.0
}
"""
        assert _run(src) == 5

    def test_array_fn_param_compiles(self) -> None:
        """Functions with Array params should compile with pair params."""
        src = """
private fn f(@Array<Int> -> @Int) requires(true) ensures(true) effects(pure) {
  @Array<Int>.0[0]
}
private fn g(-> @Int) requires(true) ensures(true) effects(pure) {
  42
}
"""
        result = _compile_ok(src)
        # Both f and g should compile
        assert "$f" in result.wat
        assert "$g" in result.wat
        # f should have pair params
        assert "(param $p0_ptr i32)" in result.wat
        assert "(param $p0_len i32)" in result.wat


# =====================================================================
# C6l: Assert and assume
# =====================================================================


class TestAssertAssume:
    def test_assert_true(self) -> None:
        """assert(true) should not trap."""
        assert _run("""
private fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  assert(true);
  42
}
""") == 42

    def test_assert_false(self) -> None:
        """assert(false) should trap."""
        _run_trap("""
private fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  assert(false);
  42
}
""")

    def test_assert_with_expression(self) -> None:
        """assert with a computed expression."""
        assert _run("""
private fn f(@Int -> @Int) requires(true) ensures(true) effects(pure) {
  assert(@Int.0 > 0);
  @Int.0 + 1
}
""", args=[5]) == 6

    def test_assert_expression_false_traps(self) -> None:
        """assert with expression that evaluates to false."""
        _run_trap("""
private fn f(@Int -> @Int) requires(true) ensures(true) effects(pure) {
  assert(@Int.0 > 0);
  @Int.0
}
""", args=[0])

    def test_assert_in_sequence(self) -> None:
        """assert followed by computation."""
        assert _run("""
private fn f(@Int, @Int -> @Int) requires(true) ensures(true) effects(pure) {
  assert(@Int.1 > 0);
  let @Int = @Int.1 + @Int.0;
  assert(@Int.0 > 0);
  @Int.0
}
""", args=[3, 5]) == 8

    def test_assume_is_noop(self) -> None:
        """assume should be a no-op at runtime."""
        assert _run("""
private fn f(@Int -> @Int) requires(true) ensures(true) effects(pure) {
  assume(@Int.0 > 0);
  @Int.0 * 2
}
""", args=[5]) == 10

    def test_assert_wat_contains_unreachable(self) -> None:
        """WAT should contain unreachable for assert."""
        result = _compile_ok("""
private fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  assert(true);
  1
}
""")
        assert "unreachable" in result.wat


# =====================================================================
# C6l: Forall quantifier
# =====================================================================


class TestForall:
    def test_forall_all_positive(self) -> None:
        """forall over array where all elements satisfy predicate."""
        assert _run("""
private fn f(-> @Bool) requires(true) ensures(true) effects(pure) {
  let @Array<Int> = [1, 2, 3];
  forall(@Int, length(@Array<Int>.0), fn(@Int -> @Bool) effects(pure) {
    @Array<Int>.0[@Int.0] > 0
  })
}
""") == 1

    def test_forall_not_all_positive(self) -> None:
        """forall over array where one element fails predicate."""
        assert _run("""
private fn f(-> @Bool) requires(true) ensures(true) effects(pure) {
  let @Array<Int> = [1, -2, 3];
  forall(@Int, length(@Array<Int>.0), fn(@Int -> @Bool) effects(pure) {
    @Array<Int>.0[@Int.0] > 0
  })
}
""") == 0

    def test_forall_empty_domain(self) -> None:
        """forall with empty domain should be vacuously true."""
        assert _run("""
private fn f(-> @Bool) requires(true) ensures(true) effects(pure) {
  forall(@Int, 0, fn(@Int -> @Bool) effects(pure) {
    false
  })
}
""") == 1

    def test_forall_single_element_true(self) -> None:
        """forall with single element, predicate true."""
        assert _run("""
private fn f(-> @Bool) requires(true) ensures(true) effects(pure) {
  let @Array<Int> = [42];
  forall(@Int, length(@Array<Int>.0), fn(@Int -> @Bool) effects(pure) {
    @Array<Int>.0[@Int.0] > 0
  })
}
""") == 1

    def test_forall_single_element_false(self) -> None:
        """forall with single element, predicate false."""
        assert _run("""
private fn f(-> @Bool) requires(true) ensures(true) effects(pure) {
  let @Array<Int> = [-1];
  forall(@Int, length(@Array<Int>.0), fn(@Int -> @Bool) effects(pure) {
    @Array<Int>.0[@Int.0] > 0
  })
}
""") == 0

    def test_forall_all_equal(self) -> None:
        """forall checking all elements equal a value."""
        assert _run("""
private fn f(-> @Bool) requires(true) ensures(true) effects(pure) {
  let @Array<Int> = [7, 7, 7];
  forall(@Int, length(@Array<Int>.0), fn(@Int -> @Bool) effects(pure) {
    @Array<Int>.0[@Int.0] == 7
  })
}
""") == 1


# =====================================================================
# C6l: Exists quantifier
# =====================================================================


class TestExists:
    def test_exists_has_zero(self) -> None:
        """exists with one matching element."""
        assert _run("""
private fn f(-> @Bool) requires(true) ensures(true) effects(pure) {
  let @Array<Int> = [1, 0, 3];
  exists(@Int, length(@Array<Int>.0), fn(@Int -> @Bool) effects(pure) {
    @Array<Int>.0[@Int.0] == 0
  })
}
""") == 1

    def test_exists_no_match(self) -> None:
        """exists with no matching element."""
        assert _run("""
private fn f(-> @Bool) requires(true) ensures(true) effects(pure) {
  let @Array<Int> = [1, 2, 3];
  exists(@Int, length(@Array<Int>.0), fn(@Int -> @Bool) effects(pure) {
    @Array<Int>.0[@Int.0] == 0
  })
}
""") == 0

    def test_exists_empty_domain(self) -> None:
        """exists with empty domain should be false."""
        assert _run("""
private fn f(-> @Bool) requires(true) ensures(true) effects(pure) {
  exists(@Int, 0, fn(@Int -> @Bool) effects(pure) {
    true
  })
}
""") == 0

    def test_exists_single_element_true(self) -> None:
        """exists with single matching element."""
        assert _run("""
private fn f(-> @Bool) requires(true) ensures(true) effects(pure) {
  let @Array<Int> = [0];
  exists(@Int, length(@Array<Int>.0), fn(@Int -> @Bool) effects(pure) {
    @Array<Int>.0[@Int.0] == 0
  })
}
""") == 1

    def test_exists_single_element_false(self) -> None:
        """exists with single non-matching element."""
        assert _run("""
private fn f(-> @Bool) requires(true) ensures(true) effects(pure) {
  let @Array<Int> = [5];
  exists(@Int, length(@Array<Int>.0), fn(@Int -> @Bool) effects(pure) {
    @Array<Int>.0[@Int.0] == 0
  })
}
""") == 0


# =====================================================================
# C6l: Quantifier WAT inspection
# =====================================================================


class TestQuantifierWat:
    def test_forall_wat_has_loop(self) -> None:
        """WAT for forall should contain loop and block."""
        result = _compile_ok("""
private fn f(-> @Bool) requires(true) ensures(true) effects(pure) {
  let @Array<Int> = [1, 2, 3];
  forall(@Int, length(@Array<Int>.0), fn(@Int -> @Bool) effects(pure) {
    @Array<Int>.0[@Int.0] > 0
  })
}
""")
        assert "loop" in result.wat
        assert "block" in result.wat
        assert "br_if" in result.wat

    def test_exists_wat_has_loop(self) -> None:
        """WAT for exists should contain loop and block."""
        result = _compile_ok("""
private fn f(-> @Bool) requires(true) ensures(true) effects(pure) {
  let @Array<Int> = [1, 2, 3];
  exists(@Int, length(@Array<Int>.0), fn(@Int -> @Bool) effects(pure) {
    @Array<Int>.0[@Int.0] == 0
  })
}
""")
        assert "loop" in result.wat
        assert "block" in result.wat


# =====================================================================
# Refinement type alias compilation
# =====================================================================


class TestRefinementTypeAlias:
    """Refined type aliases (e.g. PosInt, Percentage) resolve to their
    base WASM type for params, returns, and let bindings."""

    _PREAMBLE = """
type PosInt = { @Int | @Int.0 > 0 };
type Nat = { @Int | @Int.0 >= 0 };
type Percentage = { @Int | @Int.0 >= 0 && @Int.0 <= 100 };
"""

    def test_safe_divide_basic(self) -> None:
        val = _run(self._PREAMBLE + """
private fn safe_divide(@Int, @PosInt -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 / @PosInt.0 }
""", fn="safe_divide", args=[10, 2])
        assert val == 5

    def test_safe_divide_integer_division(self) -> None:
        val = _run(self._PREAMBLE + """
private fn safe_divide(@Int, @PosInt -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 / @PosInt.0 }
""", fn="safe_divide", args=[7, 3])
        assert val == 2

    def test_to_percentage_clamp_low(self) -> None:
        val = _run(self._PREAMBLE + """
private fn to_percentage(@Int -> @Percentage)
  requires(true) ensures(true) effects(pure)
{
  if @Int.0 < 0 then { 0 }
  else { if @Int.0 > 100 then { 100 } else { @Int.0 } }
}
""", fn="to_percentage", args=[-5])
        assert val == 0

    def test_to_percentage_passthrough(self) -> None:
        val = _run(self._PREAMBLE + """
private fn to_percentage(@Int -> @Percentage)
  requires(true) ensures(true) effects(pure)
{
  if @Int.0 < 0 then { 0 }
  else { if @Int.0 > 100 then { 100 } else { @Int.0 } }
}
""", fn="to_percentage", args=[50])
        assert val == 50

    def test_to_percentage_clamp_high(self) -> None:
        val = _run(self._PREAMBLE + """
private fn to_percentage(@Int -> @Percentage)
  requires(true) ensures(true) effects(pure)
{
  if @Int.0 < 0 then { 0 }
  else { if @Int.0 > 100 then { 100 } else { @Int.0 } }
}
""", fn="to_percentage", args=[150])
        assert val == 100

    def test_refined_type_let_binding(self) -> None:
        """Let binding to a refined type alias resolves correctly."""
        val = _run(self._PREAMBLE + """
private fn f(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @PosInt = @Int.0;
  @PosInt.0 + 1
}
""", fn="f", args=[10])
        assert val == 11

    def test_refined_return_in_expr(self) -> None:
        """Function returning a refined type works in expressions."""
        val = _run(self._PREAMBLE + """
private fn clamp(@Int -> @Percentage)
  requires(true) ensures(true) effects(pure)
{
  if @Int.0 < 0 then { 0 }
  else { if @Int.0 > 100 then { 100 } else { @Int.0 } }
}

private fn main(-> @Int) requires(true) ensures(true) effects(pure) {
  clamp(200) + clamp(50)
}
""")
        assert val == 150

    def test_refined_type_exports_in_wat(self) -> None:
        """WAT should contain function exports for refined-type fns."""
        result = _compile_ok(self._PREAMBLE + """
private fn safe_divide(@Int, @PosInt -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 / @PosInt.0 }

private fn to_percentage(@Int -> @Percentage)
  requires(true) ensures(true) effects(pure)
{
  if @Int.0 < 0 then { 0 }
  else { if @Int.0 > 100 then { 100 } else { @Int.0 } }
}
""")
        assert '(export "safe_divide"' in result.wat
        assert '(export "to_percentage"' in result.wat


# =====================================================================
# C6.5e: String and Array types in function signatures
# =====================================================================


class TestStringArraySignatures:
    """Tests for String and Array types in function parameters and returns."""

    def test_string_param(self) -> None:
        """Function taking a String param compiles with pair params."""
        src = """
private fn say(@String -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{ IO.print(@String.0) }
"""
        result = _compile_ok(src)
        assert "say" in result.exports
        assert "(param $p0_ptr i32)" in result.wat
        assert "(param $p0_len i32)" in result.wat

    def test_string_return(self) -> None:
        """Function returning a String compiles with (result i32 i32)."""
        src = '''
private fn greeting(-> @String)
  requires(true) ensures(true) effects(pure)
{ "hello" }
'''
        result = _compile_ok(src)
        assert "greeting" in result.exports
        assert "(result i32 i32)" in result.wat

    def test_string_param_and_return(self) -> None:
        """String param + String return: identity-like function."""
        src = """
private fn echo(@String -> @String)
  requires(true) ensures(true) effects(pure)
{ @String.0 }
"""
        result = _compile_ok(src)
        assert "echo" in result.exports
        assert "(param $p0_ptr i32)" in result.wat
        assert "(result i32 i32)" in result.wat

    def test_string_call_chain(self) -> None:
        """String-returning fn called by another fn via IO.print."""
        src = '''
private fn greeting(-> @String)
  requires(true) ensures(true) effects(pure)
{ "hello world" }

private fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{ IO.print(greeting()) }
'''
        result = _compile_ok(src)
        exec_result = execute(result)
        assert exec_result.stdout == "hello world"

    def test_array_param(self) -> None:
        """Function taking an Array<Int> param compiles with pair params."""
        src = """
private fn get_len(@Array<Int> -> @Int)
  requires(true) ensures(true) effects(pure)
{ length(@Array<Int>.0) }
"""
        result = _compile_ok(src)
        assert "get_len" in result.exports
        assert "(param $p0_ptr i32)" in result.wat
        assert "(param $p0_len i32)" in result.wat

    def test_array_return(self) -> None:
        """Function returning an Array literal compiles."""
        src = """
private fn nums(-> @Array<Int>)
  requires(true) ensures(true) effects(pure)
{ [1, 2, 3] }
"""
        result = _compile_ok(src)
        assert "nums" in result.exports
        assert "(result i32 i32)" in result.wat

    def test_mixed_params(self) -> None:
        """Function with both pair and primitive params."""
        src = """
private fn add_to(@Int, @String -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 + 1 }
"""
        result = _compile_ok(src)
        assert "add_to" in result.exports
        # Int param is plain i64, String param is pair
        assert "(param $p0 i64)" in result.wat
        assert "(param $p1_ptr i32)" in result.wat
        assert "(param $p1_len i32)" in result.wat
        # Can execute with Int=10, String ptr=0, len=0
        exec_result = execute(result, fn_name="add_to", args=[10, 0, 0])
        assert exec_result.value == 11

    def test_string_return_execution(self) -> None:
        """Executing a String-returning function returns a pointer."""
        src = '''
private fn hello(-> @String)
  requires(true) ensures(true) effects(pure)
{ "hello" }
'''
        result = _compile_ok(src)
        exec_result = execute(result, fn_name="hello")
        # Returns the data pointer (an integer)
        assert isinstance(exec_result.value, int)


# =====================================================================
# 6.5f: old()/new() state expressions in postconditions
# =====================================================================


class TestOldNewContracts:
    """Tests for old()/new() state expression compilation in postconditions."""

    def test_old_new_postcondition_compiles(self) -> None:
        """Function with old()/new() in ensures clause compiles to WASM."""
        src = """
private fn increment(@Unit -> @Unit)
  requires(true)
  ensures(new(State<Int>) == old(State<Int>) + 1)
  effects(<State<Int>>)
{
  let @Int = get(());
  put(@Int.0 + 1);
  ()
}
"""
        result = _compile_ok(src)
        assert "increment" in result.exports

    def test_old_new_postcondition_passes(self) -> None:
        """Postcondition holds — no trap when new == old + 1."""
        src = """
private fn increment(@Unit -> @Unit)
  requires(true)
  ensures(new(State<Int>) == old(State<Int>) + 1)
  effects(<State<Int>>)
{
  let @Int = get(());
  put(@Int.0 + 1);
  ()
}
"""
        result = _compile_ok(src)
        exec_result = execute(
            result, fn_name="increment",
            initial_state={"State_Int": 10},
        )
        # Should complete without trap
        assert exec_result.value is None  # Unit return

    def test_old_new_postcondition_traps(self) -> None:
        """Postcondition violated — traps when increment is wrong."""
        src = """
private fn bad_increment(@Unit -> @Unit)
  requires(true)
  ensures(new(State<Int>) == old(State<Int>) + 1)
  effects(<State<Int>>)
{
  let @Int = get(());
  put(@Int.0 + 2);
  ()
}
"""
        result = _compile_ok(src)
        with pytest.raises((wasmtime.WasmtimeError, wasmtime.Trap)):
            execute(
                result, fn_name="bad_increment",
                initial_state={"State_Int": 5},
            )

    def test_trivial_ensures_no_snapshot(self) -> None:
        """ensures(true) with State effect does NOT emit a snapshot."""
        src = """
private fn inc(@Unit -> @Unit)
  requires(true) ensures(true)
  effects(<State<Int>>)
{
  let @Int = get(());
  put(@Int.0 + 1);
  ()
}
"""
        result = _compile_ok(src)
        wat = result.wat
        assert "inc" in result.exports
        # Body should call state_get for the let binding,
        # but no snapshot local.set before the body
        lines = wat.split("\n")
        # Find the function body — there should be exactly one
        # state_get call (the let binding), not two (snapshot + let)
        state_get_count = sum(
            1 for l in lines if "call $vera.state_get_Int" in l
        )
        # Only the body's get() call — no snapshot
        assert state_get_count == 1

    def test_old_new_wat_structure(self) -> None:
        """WAT contains state_get snapshot before body and new() in postcondition."""
        src = """
private fn increment(@Unit -> @Unit)
  requires(true)
  ensures(new(State<Int>) == old(State<Int>) + 1)
  effects(<State<Int>>)
{
  let @Int = get(());
  put(@Int.0 + 1);
  ()
}
"""
        result = _compile_ok(src)
        wat = result.wat
        lines = wat.split("\n")
        state_get_count = sum(
            1 for l in lines if "call $vera.state_get_Int" in l
        )
        # 3 calls: snapshot (old), body get(), postcondition new()
        assert state_get_count == 3

    def test_new_reads_current_state(self) -> None:
        """new(State<T>) reads the current value, not the snapshot."""
        # Increment by 5 but claim increment by 5 in postcondition
        src = """
private fn add_five(@Unit -> @Unit)
  requires(true)
  ensures(new(State<Int>) == old(State<Int>) + 5)
  effects(<State<Int>>)
{
  let @Int = get(());
  put(@Int.0 + 5);
  ()
}
"""
        result = _compile_ok(src)
        exec_result = execute(
            result, fn_name="add_five",
            initial_state={"State_Int": 100},
        )
        assert exec_result.value is None  # Unit, no trap
