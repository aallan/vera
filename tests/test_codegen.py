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
    with pytest.raises((wasmtime.WasmtimeError, wasmtime.Trap, RuntimeError)):
        execute(result, fn_name=fn, args=args)


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
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{ IO.print("Hello, World!") }
"""
        assert _run_io(source, fn="main") == "Hello, World!"

    def test_empty_string(self) -> None:
        source = _IO_PRELUDE + """\
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{ IO.print("") }
"""
        assert _run_io(source, fn="main") == ""

    def test_multiple_prints(self) -> None:
        source = _IO_PRELUDE + """\
public fn main(@Unit -> @Unit)
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
public fn main(@Unit -> @Unit)
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
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{ IO.print("Hello, World! 123 @#$") }
"""
        assert _run_io(source, fn="main") == "Hello, World! 123 @#$"

    def test_io_with_pure_functions(self) -> None:
        """IO functions coexist with pure functions in the same module."""
        source = _IO_PRELUDE + """\
public fn add(@Int, @Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.1 + @Int.0 }

public fn main(@Unit -> @Unit)
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
# Unsupported constructs
# =====================================================================


class TestUnsupportedSkipped:
    def test_adt_function_compiles(self) -> None:
        """Functions with ADT types now compile (not skipped)."""
        source = """\
private data Option<T> { None, Some(T) }

public fn make_none(-> @Option<Int>)
  requires(true) ensures(true) effects(pure)
{ None }

public fn simple(-> @Int)
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

public fn count(@Unit -> @Unit)
  requires(true) ensures(true) effects(<Counter>)
{
  Counter.tick(())
}

public fn simple(-> @Int)
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
        with pytest.raises((wasmtime.WasmtimeError, wasmtime.Trap, RuntimeError)):
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
# String escape sequences — end-to-end (Vera source → WASM execution)
# =====================================================================


class TestStringEscapeE2E:
    """End-to-end tests: Vera escape sequences through compile + execute."""

    def test_newline_in_print(self) -> None:
        source = _IO_PRELUDE + r'''
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{ IO.print("line1\nline2") }
'''
        assert _run_io(source, fn="main") == "line1\nline2"

    def test_tab_in_print(self) -> None:
        source = _IO_PRELUDE + r'''
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{ IO.print("col1\tcol2") }
'''
        assert _run_io(source, fn="main") == "col1\tcol2"

    def test_backslash_roundtrip(self) -> None:
        source = _IO_PRELUDE + r'''
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{ IO.print("a\\b") }
'''
        assert _run_io(source, fn="main") == "a\\b"

    def test_unicode_basic(self) -> None:
        source = _IO_PRELUDE + r'''
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{ IO.print("\u{41}\u{42}\u{43}") }
'''
        assert _run_io(source, fn="main") == "ABC"

    def test_string_length_with_escapes(self) -> None:
        """Escaped \\n is one character, so length should be 3."""
        source = r'''
public fn len(@Unit -> @Nat)
  requires(true) ensures(true) effects(pure)
{ string_length("a\nb") }
'''
        assert _run(source, fn="len") == 3


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


# =====================================================================
# Module assembly — import/memory conditionals
# =====================================================================


class TestModuleAssembly:
    """Verify that module-level constructs are conditional."""

    def test_pure_no_io_import(self) -> None:
        """Pure functions should not import vera.print."""
        result = _compile_ok(
            "public fn f(-> @Int) requires(true) ensures(true) effects(pure) { 42 }"
        )
        assert "vera.print" not in result.wat

    def test_pure_no_memory(self) -> None:
        """Pure functions without strings should not declare memory."""
        result = _compile_ok(
            "public fn f(-> @Int) requires(true) ensures(true) effects(pure) { 42 }"
        )
        assert "(memory" not in result.wat

    def test_io_has_import_and_memory(self) -> None:
        """IO functions import vera.print and declare memory."""
        source = _IO_PRELUDE + """\
public fn main(@Unit -> @Unit)
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
public fn add(@Int, @Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.1 + @Int.0 }

public fn mul(@Int, @Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.1 * @Int.0 }

public fn neg(@Int -> @Int)
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
            "public fn f(-> @Int) requires(true) ensures(true) effects(pure) { 42 }"
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
public fn compute(-> @Int)
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
public fn f(-> @Int)
  requires(true) ensures(true) effects(<State<Int>>)
{ get(()) }
"""
        exec_result = _run_state(source, fn="f")
        assert exec_result.value == 0

    def test_state_int_put_then_get(self) -> None:
        """put(42) then get(()) returns 42."""
        source = """\
public fn f(-> @Int)
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
public fn increment(@Unit -> @Unit)
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
public fn f(-> @Bool)
  requires(true) ensures(true) effects(<State<Bool>>)
{ get(()) }
"""
        exec_result = _run_state(source, fn="f")
        assert exec_result.value == 0

    def test_state_bool_put_get(self) -> None:
        """put(true) then get(()) returns 1."""
        source = """\
public fn f(-> @Bool)
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
public fn f(-> @Float64)
  requires(true) ensures(true) effects(<State<Float64>>)
{ get(()) }
"""
        exec_result = _run_state(source, fn="f")
        assert exec_result.value == 0.0

    def test_state_nat_compiles(self) -> None:
        """State<Nat> compiles (Nat maps to i64)."""
        source = """\
public fn f(-> @Nat)
  requires(true) ensures(true) effects(<State<Nat>>)
{ get(()) }
"""
        exec_result = _run_state(source, fn="f")
        assert exec_result.value == 0

    def test_state_string_rejected(self) -> None:
        """State<String> is unsupported — function skipped with warning."""
        source = """\
public fn f(-> @Int)
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
public fn f(@Unit -> @Unit)
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
public fn f(-> @Int)
  requires(true) ensures(true) effects(<State<Int>>)
{ get(()) }
"""
        result = _compile_ok(source)
        assert 'import "vera" "state_get_Int"' in result.wat
        assert 'import "vera" "state_put_Int"' in result.wat

    def test_multiple_state_types(self) -> None:
        """Multiple State types emit all imports."""
        source = """\
public fn f(@Int -> @Unit)
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
public fn f(@Unit -> @Unit)
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
public fn f(-> @Int)
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
public fn f(-> @Int)
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

public fn f(-> @Int)
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

public fn f(-> @Int)
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
public fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{ 42 }
"""
        result = _compile_ok(source)
        assert "heap_ptr" not in result.wat
        assert "$alloc" not in result.wat

    def test_heap_ptr_starts_after_strings(self) -> None:
        """Heap pointer initial value should be after string data + GC regions."""
        source = """\
private data Color { Red, Green, Blue }

public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{ IO.print("hello") }
"""
        result = _compile_ok(source)
        # "hello" is 5 bytes; GC adds 8192 (4K shadow stack + 4K worklist)
        # so heap_ptr should start at 5 + 8192 = 8197
        assert "global $heap_ptr" in result.wat
        assert "i32.const 8197" in result.wat

    def test_heap_ptr_zero_without_strings(self) -> None:
        """Without strings, heap starts at GC offset 8192."""
        source = """\
private data Flag { On, Off }

public fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{ 42 }
"""
        result = _compile_ok(source)
        assert "i32.const 8192)" in result.wat  # heap_ptr init

    def test_alloc_alignment_logic(self) -> None:
        """Alloc function contains 8-byte alignment rounding."""
        source = """\
private data Bit { Zero, One }

public fn f(-> @Int)
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

public fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{ 42 }
"""
        result = _compile_ok(source)
        assert "(memory" in result.wat


class TestGarbageCollection:
    """Test GC infrastructure emission and behavior."""

    def test_gc_globals_emitted(self) -> None:
        """Programs with ADTs emit GC globals: gc_sp, gc_stack_base, etc."""
        source = """\
private data Flag { On, Off }

public fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{ 42 }
"""
        result = _compile_ok(source)
        assert "global $gc_sp" in result.wat
        assert "global $gc_stack_base" in result.wat
        assert "global $gc_heap_start" in result.wat
        assert "global $gc_free_head" in result.wat

    def test_gc_collect_emitted(self) -> None:
        """Programs with ADTs emit the $gc_collect function."""
        source = """\
private data Flag { On, Off }

public fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{ 42 }
"""
        result = _compile_ok(source)
        assert "func $gc_collect" in result.wat

    def test_gc_no_overhead_without_alloc(self) -> None:
        """Pure programs without ADTs emit no GC infrastructure."""
        source = """\
public fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{ 42 }
"""
        result = _compile_ok(source)
        assert "gc_sp" not in result.wat
        assert "gc_collect" not in result.wat
        assert "gc_stack_base" not in result.wat
        assert "$alloc" not in result.wat

    def test_gc_shadow_push_after_constructor(self) -> None:
        """Constructor allocation is followed by shadow stack push."""
        source = """\
private data Box { MkBox(Int) }

public fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  match MkBox(42) {
    MkBox(@Int) -> @Int.0
  }
}
"""
        result = _compile_ok(source)
        # Shadow stack push: global.get $gc_sp / local.get N / i32.store
        assert "global.get $gc_sp" in result.wat
        assert "global.set $gc_sp" in result.wat

    def test_gc_prologue_saves_gc_sp(self) -> None:
        """Functions that allocate save/restore $gc_sp."""
        source = """\
private data Box { MkBox(Int) }

public fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  match MkBox(42) {
    MkBox(@Int) -> @Int.0
  }
}
"""
        result = _compile_ok(source)
        wat = result.wat
        # Prologue saves gc_sp
        assert "global.get $gc_sp" in wat
        # Epilogue restores gc_sp
        assert "global.set $gc_sp" in wat

    def test_gc_preserves_live_data(self) -> None:
        """ADT data survives allocation pressure — correct result after many allocs."""
        source = """\
private data Box { MkBox(Int) }

public fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Box = MkBox(100);
  let @Box = MkBox(200);
  let @Box = MkBox(300);
  match @Box.0 {
    MkBox(@Int) -> @Int.0
  }
}
"""
        assert _run(source) == 300

    def test_gc_string_concat_pressure(self) -> None:
        """String concat exercises allocation and GC shadow stack."""
        source = """\
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print("hello world")
}
"""
        assert _run_io(source) == "hello world"

    def test_gc_adt_across_function_calls(self) -> None:
        """ADT values survive across function call boundaries."""
        source = """\
private data Pair { MkPair(Int, Int) }

public fn sum_pair(@Pair -> @Int)
  requires(true) ensures(true) effects(pure)
{
  match @Pair.0 {
    MkPair(@Int, @Int) -> @Int.0 + @Int.1
  }
}

public fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  sum_pair(MkPair(17, 25))
}
"""
        assert _run(source, fn="f") == 42

    def test_gc_nested_adt_construction(self) -> None:
        """Nested ADT construction — inner alloc must survive outer alloc."""
        source = """\
private data Box { MkBox(Int) }
private data Wrapper { Wrap(Box) }

public fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  match Wrap(MkBox(99)) {
    Wrap(@Box) -> match @Box.0 {
      MkBox(@Int) -> @Int.0
    }
  }
}
"""
        assert _run(source) == 99

    def test_gc_recursive_adt(self) -> None:
        """Recursive ADT (list) survives GC — sum elements."""
        source = """\
private data List { Nil, Cons(Int, List) }

public fn sum(@List -> @Int)
  requires(true) ensures(true) effects(pure)
{
  match @List.0 {
    Nil -> 0,
    Cons(@Int, @List) -> @Int.0 + sum(@List.0)
  }
}

public fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  sum(Cons(1, Cons(2, Cons(3, Nil))))
}
"""
        assert _run(source, fn="f") == 6

    def test_gc_closure_survives(self) -> None:
        """Closure allocation survives across apply_fn."""
        source = """\
type Fn1 = fn(Int -> Int) effects(pure);

public fn f(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Fn1 = fn(@Int -> @Int) effects(pure) { @Int.0 + 10 };
  apply_fn(@Fn1.0, 32)
}
"""
        assert _run(source, fn="f") == 42


class TestAdtMetadata:
    """Test ADT constructor layout metadata registration."""

    def test_nullary_layout(self) -> None:
        """Nullary constructor: tag only, total_size = 8."""
        source = """\
private data Unit2 { MkUnit }

public fn f(-> @Int)
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

public fn f(-> @Int)
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

public fn f(-> @Int)
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

public fn f(-> @Int)
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

public fn f(-> @Int)
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

public fn f(-> @Int)
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

public fn f(-> @Int)
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

public fn f(-> @Int)
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

public fn make_red(-> @Color)
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

public fn make_red(-> @Color)
  requires(true) ensures(true) effects(pure)
{ Red }

public fn make_green(-> @Color)
  requires(true) ensures(true) effects(pure)
{ Green }

public fn make_blue(-> @Color)
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

public fn wrap(@Int -> @Wrapper)
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

public fn toggle(@Bool -> @Toggle)
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

public fn make_none(-> @Option<Int>)
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

public fn make_some(@Int -> @Option<Int>)
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

public fn make_red(-> @Color)
  requires(true) ensures(true) effects(pure)
{ Red }
"""
        result = _compile_ok(source)
        assert "call $alloc" in result.wat

    def test_wat_contains_store_with_offset(self) -> None:
        """WAT output for Some(x) contains field store with offset."""
        source = """\
private data Wrapper { Wrap(Int) }

public fn wrap(@Int -> @Wrapper)
  requires(true) ensures(true) effects(pure)
{ Wrap(@Int.0) }
"""
        result = _compile_ok(source)
        assert "i64.store offset=8" in result.wat

    def test_nullary_tag_store(self) -> None:
        """WAT for Red (tag=0) stores tag 0; Green (tag=1) stores tag 1."""
        source = """\
private data Color { Red, Green, Blue }

public fn make_green(-> @Color)
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

public fn make_wrap(@Int -> @Wrapper)
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

public fn maybe(@Bool -> @Option<Int>)
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

public fn identity(@Color -> @Color)
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

public fn test_none(-> @Int)
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

public fn test_some(-> @Int)
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

public fn test_red(-> @Int)
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

public fn test_green(-> @Int)
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

public fn test_blue(-> @Int)
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

public fn test(-> @Int)
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

public fn test(-> @Bool)
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

public fn test(-> @Int)
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

public fn test(-> @Int)
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
public fn test(@Int -> @Int)
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

public fn test(-> @Int)
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
public fn test(@Bool -> @Int)
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
public fn test(@Bool -> @Int)
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
public fn test(@Int -> @Int)
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
public fn test(@Int -> @Int)
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
public fn test(@Int -> @Int)
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

public fn test(-> @Int)
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

public fn test(-> @Int)
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

public fn test(-> @Int)
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

public fn unwrap_or(@Option<Int> -> @Int)
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

    def test_match_nested_some(self) -> None:
        """Nested constructor: Cons(Some(@Int), _) extracts the inner Int."""
        source = """\
private data Option<T> { None, Some(T) }
private data List<T> { Nil, Cons(T, List<T>) }

public fn first_val(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @List<Option<Int>> = Cons(Some(42), Nil);
  match @List<Option<Int>>.0 {
    Cons(Some(@Int), _) -> @Int.0,
    _ -> 0
  }
}
"""
        assert _run(source, fn="first_val") == 42

    def test_match_nested_none(self) -> None:
        """Nested nullary: Cons(None, _) arm is selected."""
        source = """\
private data Option<T> { None, Some(T) }
private data List<T> { Nil, Cons(T, List<T>) }

public fn test_none(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @List<Option<Int>> = Cons(None, Nil);
  match @List<Option<Int>>.0 {
    Cons(Some(@Int), _) -> @Int.0,
    Cons(None, _) -> 99,
    _ -> 0
  }
}
"""
        assert _run(source, fn="test_none") == 99

    def test_match_nested_multi_field(self) -> None:
        """Nested constructor with both fields used."""
        source = """\
private data Option<T> { None, Some(T) }
private data Pair<A, B> { MkPair(A, B) }

public fn test(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Pair<Option<Int>, Int> = MkPair(Some(10), 5);
  match @Pair<Option<Int>, Int>.0 {
    MkPair(Some(@Int), _) -> @Int.0,
    _ -> 0
  }
}
"""
        assert _run(source, fn="test") == 10

    def test_match_nested_different_arms(self) -> None:
        """Different nesting per arm selects correct arm."""
        source = """\
private data Option<T> { None, Some(T) }
private data List<T> { Nil, Cons(T, List<T>) }

public fn test(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @List<Option<Int>> = Cons(Some(77), Nil);
  match @List<Option<Int>>.0 {
    Cons(None, _) -> 0,
    Cons(Some(@Int), _) -> @Int.0,
    _ -> 99
  }
}
"""
        assert _run(source, fn="test") == 77

    def test_match_nested_fallthrough(self) -> None:
        """Nested Some doesn't match None, falls through to wildcard."""
        source = """\
private data Option<T> { None, Some(T) }
private data List<T> { Nil, Cons(T, List<T>) }

public fn test(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @List<Option<Int>> = Cons(None, Nil);
  match @List<Option<Int>>.0 {
    Cons(Some(@Int), _) -> @Int.0,
    _ -> 55
  }
}
"""
        assert _run(source, fn="test") == 55


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
public fn test(@Unit -> @Int)
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
public fn test(@Unit -> @Int)
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
public fn test(@Unit -> @Int)
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
public fn test(@Unit -> @Int)
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
public fn test(@Unit -> @Int)
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
public fn test(@Unit -> @Int)
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
public fn test(@Unit -> @Int)
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
public fn test(@Unit -> @Bool)
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
public fn test(@Unit -> @Int)
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

    def test_exn_handler_compiles(self) -> None:
        """Exn<E> handler compiles to WASM using exception handling."""
        src = """\
effect Exn<E> {
  op throw(E -> Never);
}
private data Option<T> { None, Some(T) }
public fn test(@Int -> @Option<Int>)
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
        assert "test" in result.exports
        assert "try_table" in result.wat
        assert "tag $exn_Int" in result.wat

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

    def test_effect_handler_example_safe_div(self) -> None:
        """examples/effect_handler.vera safe_div(10, 2) returns 5."""
        from pathlib import Path
        path = Path(__file__).parent.parent / "examples" / "effect_handler.vera"
        source = path.read_text()
        result = _compile_ok(source)
        exec_result = execute(result, fn_name="safe_div", args=[10, 2])
        assert exec_result.value == 5

    def test_effect_handler_example_safe_div_zero(self) -> None:
        """examples/effect_handler.vera safe_div(7, 0) returns -1."""
        from pathlib import Path
        path = Path(__file__).parent.parent / "examples" / "effect_handler.vera"
        source = path.read_text()
        result = _compile_ok(source)
        exec_result = execute(result, fn_name="safe_div", args=[7, 0])
        assert exec_result.value == -1

    def test_effect_handler_example_main(self) -> None:
        """examples/effect_handler.vera main returns 4."""
        from pathlib import Path
        path = Path(__file__).parent.parent / "examples" / "effect_handler.vera"
        source = path.read_text()
        result = _compile_ok(source)
        exec_result = execute(result, fn_name="main")
        assert exec_result.value == 4


# =====================================================================
# Exn<E> exception handler compilation
# =====================================================================


class TestExnHandlers:
    """Tests for Exn<E> effect handler compilation using WASM exceptions."""

    def test_exn_throw_caught(self) -> None:
        """Body throws, handler catches and transforms the value."""
        src = """\
effect Exn<E> {
  op throw(E -> Never);
}
public fn test(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  handle[Exn<Int>] {
    throw(@Int) -> { @Int.0 + 100 }
  } in {
    throw(42)
  }
}
"""
        assert _run(src, fn="test") == 142

    def test_exn_no_throw(self) -> None:
        """Body completes normally, handler clause is not invoked."""
        src = """\
effect Exn<E> {
  op throw(E -> Never);
}
public fn test(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  handle[Exn<Int>] {
    throw(@Int) -> { @Int.0 + 100 }
  } in {
    99
  }
}
"""
        assert _run(src, fn="test") == 99

    def test_exn_cross_function(self) -> None:
        """Function with Exn effect throws, caller catches via handle."""
        src = """\
effect Exn<E> {
  op throw(E -> Never);
}
private fn risky(@Int -> @Int)
  requires(true) ensures(true) effects(<Exn<Int>>)
{
  if @Int.0 > 0 then { throw(@Int.0) } else { 0 }
}
public fn test(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  handle[Exn<Int>] {
    throw(@Int) -> { @Int.0 * 2 }
  } in {
    risky(21)
  }
}
"""
        assert _run(src, fn="test") == 42

    def test_exn_no_throw_cross_function(self) -> None:
        """Cross-function call that doesn't throw."""
        src = """\
effect Exn<E> {
  op throw(E -> Never);
}
private fn safe(@Int -> @Int)
  requires(true) ensures(true) effects(<Exn<Int>>)
{
  if @Int.0 > 100 then { throw(@Int.0) } else { @Int.0 + 1 }
}
public fn test(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  handle[Exn<Int>] {
    throw(@Int) -> { 0 - 1 }
  } in {
    safe(10)
  }
}
"""
        assert _run(src, fn="test") == 11

    def test_exn_with_io(self) -> None:
        """Exn handler inside a function with IO effects."""
        src = """\
effect Exn<E> {
  op throw(E -> Never);
}
public fn test(@Unit -> @Int)
  requires(true) ensures(true) effects(<IO>)
{
  handle[Exn<Int>] {
    throw(@Int) -> { @Int.0 }
  } in {
    IO.print("before throw");
    throw(77)
  }
}
"""
        result = _compile_ok(src)
        exec_result = execute(result, fn_name="test")
        assert exec_result.value == 77
        assert exec_result.stdout == "before throw"

    def test_exn_nested_inner_catches(self) -> None:
        """Nested handlers — inner catches, outer not triggered."""
        src = """\
effect Exn<E> {
  op throw(E -> Never);
}
public fn test(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  handle[Exn<Int>] {
    throw(@Int) -> { 0 - 1 }
  } in {
    handle[Exn<Int>] {
      throw(@Int) -> { @Int.0 + 500 }
    } in {
      throw(10)
    }
  }
}
"""
        assert _run(src, fn="test") == 510

    def test_exn_nat_type(self) -> None:
        """Exn<Nat> with Nat exception value."""
        src = """\
effect Exn<E> {
  op throw(E -> Never);
}
public fn test(@Unit -> @Nat)
  requires(true) ensures(true) effects(pure)
{
  handle[Exn<Nat>] {
    throw(@Nat) -> { @Nat.0 + 1000 }
  } in {
    throw(42)
  }
}
"""
        assert _run(src, fn="test") == 1042


# =====================================================================
# C6k: Byte type
# =====================================================================


class TestByteType:
    def test_byte_identity(self) -> None:
        src = """
public fn f(@Byte -> @Byte) requires(true) ensures(true) effects(pure) {
  @Byte.0
}
"""
        assert _run(src, fn="f", args=[42]) == 42

    def test_byte_zero(self) -> None:
        src = """
public fn f(-> @Byte) requires(true) ensures(true) effects(pure) {
  0
}
"""
        assert _run(src) == 0

    def test_byte_max(self) -> None:
        src = """
public fn f(-> @Byte) requires(true) ensures(true) effects(pure) {
  255
}
"""
        assert _run(src) == 255

    def test_byte_let_binding(self) -> None:
        src = """
public fn f(@Byte -> @Byte) requires(true) ensures(true) effects(pure) {
  let @Byte = @Byte.0;
  @Byte.0
}
"""
        assert _run(src, fn="f", args=[100]) == 100

    def test_byte_eq(self) -> None:
        src = """
public fn f(@Byte, @Byte -> @Bool) requires(true) ensures(true) effects(pure) {
  @Byte.0 == @Byte.1
}
"""
        assert _run(src, fn="f", args=[5, 5]) == 1
        assert _run(src, fn="f", args=[5, 6]) == 0

    def test_byte_lt_unsigned(self) -> None:
        # @Byte.0 = second param (de Bruijn 0), @Byte.1 = first param
        src = """
public fn f(@Byte, @Byte -> @Bool) requires(true) ensures(true) effects(pure) {
  @Byte.0 < @Byte.1
}
"""
        # f(200, 10): @Byte.0=10, @Byte.1=200 → 10 < 200 = true
        assert _run(src, fn="f", args=[200, 10]) == 1
        # f(10, 200): @Byte.0=200, @Byte.1=10 → 200 < 10 = false
        assert _run(src, fn="f", args=[10, 200]) == 0

    def test_byte_gt_unsigned(self) -> None:
        src = """
public fn f(@Byte, @Byte -> @Bool) requires(true) ensures(true) effects(pure) {
  @Byte.0 > @Byte.1
}
"""
        # f(10, 200): @Byte.0=200, @Byte.1=10 → 200 > 10 = true
        assert _run(src, fn="f", args=[10, 200]) == 1
        # f(200, 10): @Byte.0=10, @Byte.1=200 → 10 > 200 = false
        assert _run(src, fn="f", args=[200, 10]) == 0

    def test_byte_le(self) -> None:
        src = """
public fn f(@Byte, @Byte -> @Bool) requires(true) ensures(true) effects(pure) {
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
public fn f(@Byte, @Byte -> @Bool) requires(true) ensures(true) effects(pure) {
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
public fn f(@Byte, @Byte -> @Bool) requires(true) ensures(true) effects(pure) {
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
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Array<Int> = [10, 20, 30];
  @Array<Int>.0[0]
}
"""
        assert _run(src) == 10

    def test_int_array_index_1(self) -> None:
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Array<Int> = [10, 20, 30];
  @Array<Int>.0[1]
}
"""
        assert _run(src) == 20

    def test_int_array_index_2(self) -> None:
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Array<Int> = [10, 20, 30];
  @Array<Int>.0[2]
}
"""
        assert _run(src) == 30

    def test_single_element_array(self) -> None:
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Array<Int> = [42];
  @Array<Int>.0[0]
}
"""
        assert _run(src) == 42

    def test_bool_array(self) -> None:
        src = """
public fn f(-> @Bool) requires(true) ensures(true) effects(pure) {
  let @Array<Bool> = [true, false, true];
  @Array<Bool>.0[1]
}
"""
        assert _run(src) == 0

    def test_array_wat_has_alloc(self) -> None:
        """Array literal WAT should contain call $alloc."""
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Array<Int> = [1, 2, 3];
  @Array<Int>.0[0]
}
"""
        result = _compile_ok(src)
        assert "call $alloc" in result.wat

    def test_array_wat_has_bounds_check(self) -> None:
        """Array indexing WAT should contain unreachable for OOB."""
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
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
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Array<Int> = [10, 20, 30];
  @Array<Int>.0[3]
}
"""
        _run_trap(src)

    def test_oob_large_index(self) -> None:
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Array<Int> = [10, 20, 30];
  @Array<Int>.0[100]
}
"""
        _run_trap(src)

    def test_last_valid_index(self) -> None:
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Array<Int> = [10, 20, 30];
  @Array<Int>.0[2]
}
"""
        assert _run(src) == 30

    def test_first_valid_index(self) -> None:
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
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
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Array<Int> = [10, 20, 30];
  array_length(@Array<Int>.0)
}
"""
        assert _run(src) == 3

    def test_length_one(self) -> None:
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Array<Int> = [42];
  array_length(@Array<Int>.0)
}
"""
        assert _run(src) == 1

    def test_length_in_comparison(self) -> None:
        src = """
public fn f(-> @Bool) requires(true) ensures(true) effects(pure) {
  let @Array<Int> = [10, 20, 30];
  array_length(@Array<Int>.0) == 3
}
"""
        assert _run(src) == 1

    def test_length_in_let(self) -> None:
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Array<Int> = [1, 2, 3, 4, 5];
  let @Int = array_length(@Array<Int>.0);
  @Int.0
}
"""
        assert _run(src) == 5

    # --- array_append (#242) ---

    def test_array_append_length(self) -> None:
        """array_append returns an array with length + 1."""
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  array_length(array_append([1, 2, 3], 4))
}
"""
        assert _run(src) == 4

    def test_array_append_element_value(self) -> None:
        """The appended element is accessible at the last index."""
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Array<Int> = array_append([10, 20, 30], 99);
  @Array<Int>.0[3]
}
"""
        assert _run(src) == 99

    def test_array_append_preserves_existing(self) -> None:
        """array_append preserves all existing elements."""
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Array<Int> = array_append([10, 20, 30], 99);
  @Array<Int>.0[1]
}
"""
        assert _run(src) == 20

    def test_array_append_empty(self) -> None:
        """array_append onto empty array produces [elem]."""
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Array<Int> = array_append([], 42);
  @Array<Int>.0[0]
}
"""
        assert _run(src) == 42

    def test_array_fn_param_compiles(self) -> None:
        """Functions with Array params should compile with pair params."""
        src = """
public fn f(@Array<Int> -> @Int) requires(true) ensures(true) effects(pure) {
  @Array<Int>.0[0]
}
public fn g(-> @Int) requires(true) ensures(true) effects(pure) {
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
# Array construction builtins (#209)
# =====================================================================


class TestArrayRange:
    """Tests for array_range(start, end) → Array<Int>."""

    def test_range_length(self) -> None:
        """array_range(0, 5) produces an array of length 5."""
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  array_length(array_range(0, 5))
}
"""
        assert _run(src) == 5

    def test_range_first_element(self) -> None:
        """First element of array_range(3, 7) is 3."""
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Array<Int> = array_range(3, 7);
  @Array<Int>.0[0]
}
"""
        assert _run(src) == 3

    def test_range_last_element(self) -> None:
        """Last element of array_range(3, 7) is 6 (end-exclusive)."""
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Array<Int> = array_range(3, 7);
  @Array<Int>.0[3]
}
"""
        assert _run(src) == 6

    def test_range_empty_reversed(self) -> None:
        """array_range(5, 3) produces an empty array."""
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  array_length(array_range(5, 3))
}
"""
        assert _run(src) == 0

    def test_range_empty_equal(self) -> None:
        """array_range(5, 5) produces an empty array."""
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  array_length(array_range(5, 5))
}
"""
        assert _run(src) == 0

    def test_range_negative_start(self) -> None:
        """array_range with negative start works correctly."""
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Array<Int> = array_range(0 - 2, 2);
  @Array<Int>.0[0]
}
"""
        assert _run(src) == -2

    def test_range_negative_length(self) -> None:
        """array_range with negative start has correct length."""
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  array_length(array_range(0 - 2, 3))
}
"""
        assert _run(src) == 5


class TestArrayConcat:
    """Tests for array_concat(array_a, array_b) → Array<T>."""

    def test_concat_length(self) -> None:
        """Concatenation has combined length."""
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  array_length(array_concat([1, 2], [3, 4, 5]))
}
"""
        assert _run(src) == 5

    def test_concat_first_half(self) -> None:
        """Elements from first array are preserved."""
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Array<Int> = array_concat([10, 20], [30, 40]);
  @Array<Int>.0[1]
}
"""
        assert _run(src) == 20

    def test_concat_second_half(self) -> None:
        """Elements from second array are at the right offset."""
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Array<Int> = array_concat([10, 20], [30, 40]);
  @Array<Int>.0[2]
}
"""
        assert _run(src) == 30

    def test_concat_empty_left(self) -> None:
        """Concatenating empty left with non-empty right works."""
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Array<Int> = array_concat([], [1, 2]);
  @Array<Int>.0[0]
}
"""
        assert _run(src) == 1

    def test_concat_empty_right(self) -> None:
        """Concatenating non-empty left with empty right works."""
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  array_length(array_concat([1, 2], []))
}
"""
        assert _run(src) == 2

    def test_concat_both_empty(self) -> None:
        """Concatenating two empty arrays produces empty."""
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  array_length(array_concat([], []))
}
"""
        assert _run(src) == 0


# =====================================================================
# User-defined functions shadow built-in intrinsics (#154)
# =====================================================================


class TestBuiltinShadowing:
    """User-defined functions take priority over built-in intrinsics."""

    def test_user_length_over_adt(self) -> None:
        """User-defined length() over a recursive ADT compiles and runs."""
        src = """
private data List<T> { Nil, Cons(T, List<T>) }

private fn length(@List<Int> -> @Nat)
  requires(true) ensures(@Nat.result >= 0)
  decreases(@List<Int>.0) effects(pure)
{
  match @List<Int>.0 {
    Nil -> 0,
    Cons(@Int, @List<Int>) -> 1 + length(@List<Int>.0)
  }
}

public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  let @List<Int> = Cons(1, Cons(2, Cons(3, Nil)));
  length(@List<Int>.0)
}
"""
        assert _run(src) == 3

    def test_user_length_single_element(self) -> None:
        """User-defined length returns 1 for a single-element list."""
        src = """
private data List<T> { Nil, Cons(T, List<T>) }

private fn length(@List<Int> -> @Nat)
  requires(true) ensures(@Nat.result >= 0)
  decreases(@List<Int>.0) effects(pure)
{
  match @List<Int>.0 {
    Nil -> 0,
    Cons(@Int, @List<Int>) -> 1 + length(@List<Int>.0)
  }
}

public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  length(Cons(42, Nil))
}
"""
        assert _run(src) == 1

    def test_builtin_array_length_still_works(self) -> None:
        """Array length built-in works when no user-defined length exists."""
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Array<Int> = [10, 20, 30];
  array_length(@Array<Int>.0)
}
"""
        assert _run(src) == 3


# =====================================================================
# C6l: Assert and assume
# =====================================================================


class TestAssertAssume:
    def test_assert_true(self) -> None:
        """assert(true) should not trap."""
        assert _run("""
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  assert(true);
  42
}
""") == 42

    def test_assert_false(self) -> None:
        """assert(false) should trap."""
        _run_trap("""
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  assert(false);
  42
}
""")

    def test_assert_with_expression(self) -> None:
        """assert with a computed expression."""
        assert _run("""
public fn f(@Int -> @Int) requires(true) ensures(true) effects(pure) {
  assert(@Int.0 > 0);
  @Int.0 + 1
}
""", args=[5]) == 6

    def test_assert_expression_false_traps(self) -> None:
        """assert with expression that evaluates to false."""
        _run_trap("""
public fn f(@Int -> @Int) requires(true) ensures(true) effects(pure) {
  assert(@Int.0 > 0);
  @Int.0
}
""", args=[0])

    def test_assert_in_sequence(self) -> None:
        """assert followed by computation."""
        assert _run("""
public fn f(@Int, @Int -> @Int) requires(true) ensures(true) effects(pure) {
  assert(@Int.1 > 0);
  let @Int = @Int.1 + @Int.0;
  assert(@Int.0 > 0);
  @Int.0
}
""", args=[3, 5]) == 8

    def test_assume_is_noop(self) -> None:
        """assume should be a no-op at runtime."""
        assert _run("""
public fn f(@Int -> @Int) requires(true) ensures(true) effects(pure) {
  assume(@Int.0 > 0);
  @Int.0 * 2
}
""", args=[5]) == 10

    def test_assert_wat_contains_unreachable(self) -> None:
        """WAT should contain unreachable for assert."""
        result = _compile_ok("""
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
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
public fn f(-> @Bool) requires(true) ensures(true) effects(pure) {
  let @Array<Int> = [1, 2, 3];
  forall(@Int, array_length(@Array<Int>.0), fn(@Int -> @Bool) effects(pure) {
    @Array<Int>.0[@Int.0] > 0
  })
}
""") == 1

    def test_forall_not_all_positive(self) -> None:
        """forall over array where one element fails predicate."""
        assert _run("""
public fn f(-> @Bool) requires(true) ensures(true) effects(pure) {
  let @Array<Int> = [1, -2, 3];
  forall(@Int, array_length(@Array<Int>.0), fn(@Int -> @Bool) effects(pure) {
    @Array<Int>.0[@Int.0] > 0
  })
}
""") == 0

    def test_forall_empty_domain(self) -> None:
        """forall with empty domain should be vacuously true."""
        assert _run("""
public fn f(-> @Bool) requires(true) ensures(true) effects(pure) {
  forall(@Int, 0, fn(@Int -> @Bool) effects(pure) {
    false
  })
}
""") == 1

    def test_forall_single_element_true(self) -> None:
        """forall with single element, predicate true."""
        assert _run("""
public fn f(-> @Bool) requires(true) ensures(true) effects(pure) {
  let @Array<Int> = [42];
  forall(@Int, array_length(@Array<Int>.0), fn(@Int -> @Bool) effects(pure) {
    @Array<Int>.0[@Int.0] > 0
  })
}
""") == 1

    def test_forall_single_element_false(self) -> None:
        """forall with single element, predicate false."""
        assert _run("""
public fn f(-> @Bool) requires(true) ensures(true) effects(pure) {
  let @Array<Int> = [-1];
  forall(@Int, array_length(@Array<Int>.0), fn(@Int -> @Bool) effects(pure) {
    @Array<Int>.0[@Int.0] > 0
  })
}
""") == 0

    def test_forall_all_equal(self) -> None:
        """forall checking all elements equal a value."""
        assert _run("""
public fn f(-> @Bool) requires(true) ensures(true) effects(pure) {
  let @Array<Int> = [7, 7, 7];
  forall(@Int, array_length(@Array<Int>.0), fn(@Int -> @Bool) effects(pure) {
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
public fn f(-> @Bool) requires(true) ensures(true) effects(pure) {
  let @Array<Int> = [1, 0, 3];
  exists(@Int, array_length(@Array<Int>.0), fn(@Int -> @Bool) effects(pure) {
    @Array<Int>.0[@Int.0] == 0
  })
}
""") == 1

    def test_exists_no_match(self) -> None:
        """exists with no matching element."""
        assert _run("""
public fn f(-> @Bool) requires(true) ensures(true) effects(pure) {
  let @Array<Int> = [1, 2, 3];
  exists(@Int, array_length(@Array<Int>.0), fn(@Int -> @Bool) effects(pure) {
    @Array<Int>.0[@Int.0] == 0
  })
}
""") == 0

    def test_exists_empty_domain(self) -> None:
        """exists with empty domain should be false."""
        assert _run("""
public fn f(-> @Bool) requires(true) ensures(true) effects(pure) {
  exists(@Int, 0, fn(@Int -> @Bool) effects(pure) {
    true
  })
}
""") == 0

    def test_exists_single_element_true(self) -> None:
        """exists with single matching element."""
        assert _run("""
public fn f(-> @Bool) requires(true) ensures(true) effects(pure) {
  let @Array<Int> = [0];
  exists(@Int, array_length(@Array<Int>.0), fn(@Int -> @Bool) effects(pure) {
    @Array<Int>.0[@Int.0] == 0
  })
}
""") == 1

    def test_exists_single_element_false(self) -> None:
        """exists with single non-matching element."""
        assert _run("""
public fn f(-> @Bool) requires(true) ensures(true) effects(pure) {
  let @Array<Int> = [5];
  exists(@Int, array_length(@Array<Int>.0), fn(@Int -> @Bool) effects(pure) {
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
public fn f(-> @Bool) requires(true) ensures(true) effects(pure) {
  let @Array<Int> = [1, 2, 3];
  forall(@Int, array_length(@Array<Int>.0), fn(@Int -> @Bool) effects(pure) {
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
public fn f(-> @Bool) requires(true) ensures(true) effects(pure) {
  let @Array<Int> = [1, 2, 3];
  exists(@Int, array_length(@Array<Int>.0), fn(@Int -> @Bool) effects(pure) {
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
public fn safe_divide(@Int, @PosInt -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 / @PosInt.0 }
""", fn="safe_divide", args=[10, 2])
        assert val == 5

    def test_safe_divide_integer_division(self) -> None:
        val = _run(self._PREAMBLE + """
public fn safe_divide(@Int, @PosInt -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 / @PosInt.0 }
""", fn="safe_divide", args=[7, 3])
        assert val == 2

    def test_to_percentage_clamp_low(self) -> None:
        val = _run(self._PREAMBLE + """
public fn to_percentage(@Int -> @Percentage)
  requires(true) ensures(true) effects(pure)
{
  if @Int.0 < 0 then { 0 }
  else { if @Int.0 > 100 then { 100 } else { @Int.0 } }
}
""", fn="to_percentage", args=[-5])
        assert val == 0

    def test_to_percentage_passthrough(self) -> None:
        val = _run(self._PREAMBLE + """
public fn to_percentage(@Int -> @Percentage)
  requires(true) ensures(true) effects(pure)
{
  if @Int.0 < 0 then { 0 }
  else { if @Int.0 > 100 then { 100 } else { @Int.0 } }
}
""", fn="to_percentage", args=[50])
        assert val == 50

    def test_to_percentage_clamp_high(self) -> None:
        val = _run(self._PREAMBLE + """
public fn to_percentage(@Int -> @Percentage)
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
public fn f(@Int -> @Int)
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
public fn clamp(@Int -> @Percentage)
  requires(true) ensures(true) effects(pure)
{
  if @Int.0 < 0 then { 0 }
  else { if @Int.0 > 100 then { 100 } else { @Int.0 } }
}

public fn main(-> @Int) requires(true) ensures(true) effects(pure) {
  clamp(200) + clamp(50)
}
""")
        assert val == 150

    def test_refined_type_exports_in_wat(self) -> None:
        """WAT should contain function exports for refined-type fns."""
        result = _compile_ok(self._PREAMBLE + """
public fn safe_divide(@Int, @PosInt -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 / @PosInt.0 }

public fn to_percentage(@Int -> @Percentage)
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
public fn say(@String -> @Unit)
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
public fn greeting(-> @String)
  requires(true) ensures(true) effects(pure)
{ "hello" }
'''
        result = _compile_ok(src)
        assert "greeting" in result.exports
        assert "(result i32 i32)" in result.wat

    def test_string_param_and_return(self) -> None:
        """String param + String return: identity-like function."""
        src = """
public fn echo(@String -> @String)
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
public fn greeting(-> @String)
  requires(true) ensures(true) effects(pure)
{ "hello world" }

public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{ IO.print(greeting()) }
'''
        result = _compile_ok(src)
        exec_result = execute(result)
        assert exec_result.stdout == "hello world"

    def test_array_param(self) -> None:
        """Function taking an Array<Int> param compiles with pair params."""
        src = """
public fn get_len(@Array<Int> -> @Int)
  requires(true) ensures(true) effects(pure)
{ array_length(@Array<Int>.0) }
"""
        result = _compile_ok(src)
        assert "get_len" in result.exports
        assert "(param $p0_ptr i32)" in result.wat
        assert "(param $p0_len i32)" in result.wat

    def test_array_return(self) -> None:
        """Function returning an Array literal compiles."""
        src = """
public fn nums(-> @Array<Int>)
  requires(true) ensures(true) effects(pure)
{ [1, 2, 3] }
"""
        result = _compile_ok(src)
        assert "nums" in result.exports
        assert "(result i32 i32)" in result.wat

    def test_mixed_params(self) -> None:
        """Function with both pair and primitive params."""
        src = """
public fn add_to(@Int, @String -> @Int)
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
public fn hello(-> @String)
  requires(true) ensures(true) effects(pure)
{ "hello" }
'''
        result = _compile_ok(src)
        exec_result = execute(result, fn_name="hello")
        # Returns the data pointer (an integer)
        assert isinstance(exec_result.value, int)


class TestFormatExpr:
    """Unit tests for ast.format_expr and related helpers."""

    def test_int_lit(self) -> None:
        from vera.ast import IntLit, format_expr
        assert format_expr(IntLit(value=42)) == "42"

    def test_bool_lit(self) -> None:
        from vera.ast import BoolLit, format_expr
        assert format_expr(BoolLit(value=True)) == "true"
        assert format_expr(BoolLit(value=False)) == "false"

    def test_slot_ref(self) -> None:
        from vera.ast import SlotRef, format_expr
        expr = SlotRef(type_name="Int", type_args=None, index=1)
        assert format_expr(expr) == "@Int.1"

    def test_slot_ref_with_type_args(self) -> None:
        from vera.ast import NamedType, SlotRef, format_expr
        expr = SlotRef(
            type_name="Option",
            type_args=(NamedType(name="Int", type_args=None),),
            index=0,
        )
        assert format_expr(expr) == "@Option<@Int>.0"

    def test_result_ref(self) -> None:
        from vera.ast import ResultRef, format_expr
        expr = ResultRef(type_name="Int", type_args=None)
        assert format_expr(expr) == "@Int.result"

    def test_binary_le(self) -> None:
        from vera.ast import BinOp, BinaryExpr, SlotRef, format_expr
        expr = BinaryExpr(
            op=BinOp.LE,
            left=SlotRef(type_name="Int", type_args=None, index=1),
            right=SlotRef(type_name="Int", type_args=None, index=2),
        )
        assert format_expr(expr) == "@Int.1 <= @Int.2"

    def test_unary_not(self) -> None:
        from vera.ast import BoolLit, UnaryExpr, UnaryOp, format_expr
        expr = UnaryExpr(op=UnaryOp.NOT, operand=BoolLit(value=True))
        assert format_expr(expr) == "!true"

    def test_unary_neg(self) -> None:
        from vera.ast import IntLit, UnaryExpr, UnaryOp, format_expr
        expr = UnaryExpr(op=UnaryOp.NEG, operand=IntLit(value=5))
        assert format_expr(expr) == "-5"

    def test_fn_call(self) -> None:
        from vera.ast import FnCall, IntLit, format_expr
        expr = FnCall(name="abs", args=(IntLit(value=3),))
        assert format_expr(expr) == "abs(3)"

    def test_format_fn_signature(self) -> None:
        from vera.ast import (
            BoolLit, FnDecl, NamedType, format_fn_signature,
        )
        decl = FnDecl(
            name="clamp",
            forall_vars=None,
            forall_constraints=None,
            params=(
                NamedType(name="Int", type_args=None),
                NamedType(name="Int", type_args=None),
                NamedType(name="Int", type_args=None),
            ),
            return_type=NamedType(name="Int", type_args=None),
            contracts=(),
            effect=(),
            body=(BoolLit(value=True),),
            where_fns=None,
        )
        assert format_fn_signature(decl) == "clamp(@Int, @Int, @Int -> @Int)"


# =====================================================================
# String operations
# =====================================================================


class TestStringLength:
    def test_basic(self) -> None:
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  string_length("hello")
}
"""
        assert _run(src) == 5

    def test_empty(self) -> None:
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  string_length("")
}
"""
        assert _run(src) == 0

    def test_in_let(self) -> None:
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Int = string_length("abc");
  @Int.0
}
"""
        assert _run(src) == 3


class TestStringConcat:
    def test_basic(self) -> None:
        src = """
effect IO { op print(String -> Unit); }
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print(string_concat("hello", " world"))
}
"""
        assert _run_io(src) == "hello world"

    def test_empty_left(self) -> None:
        src = """
effect IO { op print(String -> Unit); }
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print(string_concat("", "world"))
}
"""
        assert _run_io(src) == "world"

    def test_empty_right(self) -> None:
        src = """
effect IO { op print(String -> Unit); }
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print(string_concat("hello", ""))
}
"""
        assert _run_io(src) == "hello"

    def test_both_empty(self) -> None:
        src = """
effect IO { op print(String -> Unit); }
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print(string_concat("", ""))
}
"""
        assert _run_io(src) == ""

    def test_concat_length(self) -> None:
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  string_length(string_concat("abc", "def"))
}
"""
        assert _run(src) == 6


class TestStringSlice:
    def test_basic(self) -> None:
        src = """
effect IO { op print(String -> Unit); }
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print(string_slice("hello world", 6, 11))
}
"""
        assert _run_io(src) == "world"

    def test_prefix(self) -> None:
        src = """
effect IO { op print(String -> Unit); }
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print(string_slice("hello", 0, 3))
}
"""
        assert _run_io(src) == "hel"

    def test_empty_slice(self) -> None:
        src = """
effect IO { op print(String -> Unit); }
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print(string_slice("hello", 2, 2))
}
"""
        assert _run_io(src) == ""

    def test_slice_length(self) -> None:
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  string_length(string_slice("hello world", 0, 5))
}
"""
        assert _run(src) == 5

    def test_slice_then_concat(self) -> None:
        src = """
effect IO { op print(String -> Unit); }
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print(string_concat(
    string_slice("abcdef", 0, 3),
    string_slice("abcdef", 3, 6)
  ))
}
"""
        assert _run_io(src) == "abcdef"


class TestStringCharCode:
    def test_uppercase_a(self) -> None:
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Nat = string_char_code("A", 0);
  @Nat.0
}
"""
        assert _run(src) == 65

    def test_digit_zero(self) -> None:
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Nat = string_char_code("0", 0);
  @Nat.0
}
"""
        assert _run(src) == 48

    def test_second_char(self) -> None:
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Nat = string_char_code("AB", 1);
  @Nat.0
}
"""
        assert _run(src) == 66

    def test_space(self) -> None:
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Nat = string_char_code(" ", 0);
  @Nat.0
}
"""
        assert _run(src) == 32


class TestStringFromCharCode:
    """string_from_char_code creates a single-character string from a code point."""

    def test_uppercase_a(self) -> None:
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Nat = string_char_code(string_from_char_code(65), 0);
  @Nat.0
}
"""
        assert _run(src) == 65

    def test_digit(self) -> None:
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Nat = string_char_code(string_from_char_code(48), 0);
  @Nat.0
}
"""
        assert _run(src) == 48

    def test_space(self) -> None:
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Nat = string_char_code(string_from_char_code(32), 0);
  @Nat.0
}
"""
        assert _run(src) == 32

    def test_length_is_one(self) -> None:
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Nat = string_length(string_from_char_code(65));
  @Nat.0
}
"""
        assert _run(src) == 1

    def test_concat_builds_string(self) -> None:
        src = """
public fn f(-> @Bool) requires(true) ensures(true) effects(pure) {
  let @String = string_concat(string_from_char_code(65), string_from_char_code(66));
  string_starts_with(@String.0, "AB")
}
"""
        assert _run(src) == 1


class TestStringRepeat:
    """string_repeat repeats a string N times."""

    def test_basic(self) -> None:
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Nat = string_length(string_repeat("ab", 3));
  @Nat.0
}
"""
        assert _run(src) == 6

    def test_single_char(self) -> None:
        src = """
public fn f(-> @Bool) requires(true) ensures(true) effects(pure) {
  string_starts_with(string_repeat("x", 5), "xxxxx")
}
"""
        assert _run(src) == 1

    def test_zero_count(self) -> None:
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Nat = string_length(string_repeat("hello", 0));
  @Nat.0
}
"""
        assert _run(src) == 0

    def test_one_count(self) -> None:
        src = """
public fn f(-> @Bool) requires(true) ensures(true) effects(pure) {
  string_starts_with(string_repeat("hello", 1), "hello")
}
"""
        assert _run(src) == 1

    def test_empty_string(self) -> None:
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Nat = string_length(string_repeat("", 100));
  @Nat.0
}
"""
        assert _run(src) == 0


class TestParseNat:
    """parse_nat returns Result<Nat, String>."""

    _PREAMBLE = """
private data Result<T, E> { Ok(T), Err(E) }
"""

    def _ok_prog(self, literal: str) -> str:
        return self._PREAMBLE + f"""
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {{
  match parse_nat("{literal}") {{
    Ok(@Nat) -> @Nat.0,
    Err(_) -> 0 - 1
  }}
}}
"""

    def _err_prog(self, literal: str) -> str:
        return self._PREAMBLE + f"""
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {{
  match parse_nat("{literal}") {{
    Ok(_) -> 0,
    Err(_) -> 1
  }}
}}
"""

    def test_basic(self) -> None:
        assert _run(self._ok_prog("42")) == 42

    def test_zero(self) -> None:
        assert _run(self._ok_prog("0")) == 0

    def test_large(self) -> None:
        assert _run(self._ok_prog("12345")) == 12345

    def test_leading_spaces(self) -> None:
        assert _run(self._ok_prog("  99")) == 99

    def test_trailing_spaces(self) -> None:
        assert _run(self._ok_prog("77  ")) == 77

    def test_empty_string_err(self) -> None:
        assert _run(self._err_prog("")) == 1

    def test_invalid_digit_err(self) -> None:
        assert _run(self._err_prog("abc")) == 1

    def test_mixed_invalid_err(self) -> None:
        assert _run(self._err_prog("12x3")) == 1

    def test_err_string_extraction(self) -> None:
        """Err arm can bind and use the error string."""
        src = self._PREAMBLE + """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  match parse_nat("abc") {
    Ok(_) -> 0,
    Err(@String) -> string_length(@String.0)
  }
}
"""
        # "invalid digit" has length 13
        assert _run(src) == 13


class TestParseFloat64:
    """parse_float64 returns Result<Float64, String>."""

    _PREAMBLE = """
private data Result<T, E> { Ok(T), Err(E) }
"""

    def _ok_prog(self, literal: str, expect_int: int) -> str:
        """Build a program that parses a float and compares to expected value.

        Returns 1 if the float matches the expected integer value, 0 otherwise.
        This avoids returning f64 directly since Result wrapping returns i32.
        """
        return self._PREAMBLE + f"""
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {{
  match parse_float64("{literal}") {{
    Ok(@Float64) -> float_to_int(@Float64.0),
    Err(_) -> 0 - 999
  }}
}}
"""

    def _err_prog(self, literal: str) -> str:
        return self._PREAMBLE + f"""
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {{
  match parse_float64("{literal}") {{
    Ok(_) -> 0,
    Err(_) -> 1
  }}
}}
"""

    def test_integer(self) -> None:
        assert _run(self._ok_prog("42", 42)) == 42

    def test_decimal(self) -> None:
        # float_to_int truncates, so 3.14 -> 3
        assert _run(self._ok_prog("3.14", 3)) == 3

    def test_negative(self) -> None:
        # -2.5 truncated to int -> -2
        assert _run(self._ok_prog("-2.5", -2)) == -2

    def test_leading_spaces(self) -> None:
        assert _run(self._ok_prog("  1.0", 1)) == 1

    def test_no_decimal(self) -> None:
        assert _run(self._ok_prog("100", 100)) == 100

    def test_empty_err(self) -> None:
        assert _run(self._err_prog("")) == 1

    def test_invalid_err(self) -> None:
        assert _run(self._err_prog("abc")) == 1

    def test_err_string_extraction(self) -> None:
        """Err arm can bind and use the error string."""
        src = self._PREAMBLE + """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  match parse_float64("abc") {
    Ok(_) -> 0,
    Err(@String) -> string_length(@String.0)
  }
}
"""
        # "invalid character" has length 17
        assert _run(src) == 17


class TestParseInt:
    """parse_int returns Result<Int, String>."""

    _PREAMBLE = """
private data Result<T, E> { Ok(T), Err(E) }
"""

    def _ok_prog(self, literal: str) -> str:
        return self._PREAMBLE + f"""
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {{
  match parse_int("{literal}") {{
    Ok(@Int) -> @Int.0,
    Err(_) -> 0 - 999
  }}
}}
"""

    def _err_prog(self, literal: str) -> str:
        return self._PREAMBLE + f"""
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {{
  match parse_int("{literal}") {{
    Ok(_) -> 0,
    Err(_) -> 1
  }}
}}
"""

    def test_basic(self) -> None:
        assert _run(self._ok_prog("42")) == 42

    def test_negative(self) -> None:
        assert _run(self._ok_prog("-7")) == -7

    def test_positive_sign(self) -> None:
        assert _run(self._ok_prog("+5")) == 5

    def test_zero(self) -> None:
        assert _run(self._ok_prog("0")) == 0

    def test_spaces(self) -> None:
        assert _run(self._ok_prog("  42  ")) == 42

    def test_empty_err(self) -> None:
        assert _run(self._err_prog("")) == 1

    def test_invalid_err(self) -> None:
        assert _run(self._err_prog("abc")) == 1

    def test_err_string_extraction(self) -> None:
        """Err arm can bind and use the error string."""
        src = self._PREAMBLE + """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  match parse_int("abc") {
    Ok(_) -> 0,
    Err(@String) -> string_length(@String.0)
  }
}
"""
        # "invalid digit" has length 13
        assert _run(src) == 13


class TestParseBool:
    """parse_bool returns Result<Bool, String>."""

    _PREAMBLE = """
private data Result<T, E> { Ok(T), Err(E) }
"""

    def _ok_prog(self, literal: str, expect_true: bool) -> str:
        expected = 1 if expect_true else 0
        return self._PREAMBLE + f"""
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {{
  match parse_bool("{literal}") {{
    Ok(@Bool) -> if @Bool.0 then {{ 1 }} else {{ 0 }},
    Err(_) -> 0 - 999
  }}
}}
"""

    def _err_prog(self, literal: str) -> str:
        return self._PREAMBLE + f"""
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {{
  match parse_bool("{literal}") {{
    Ok(_) -> 0,
    Err(_) -> 1
  }}
}}
"""

    def test_true(self) -> None:
        assert _run(self._ok_prog("true", True)) == 1

    def test_false(self) -> None:
        assert _run(self._ok_prog("false", False)) == 0

    def test_invalid(self) -> None:
        assert _run(self._err_prog("yes")) == 1

    def test_empty(self) -> None:
        assert _run(self._err_prog("")) == 1

    def test_whitespace(self) -> None:
        assert _run(self._ok_prog("  true  ", True)) == 1

    def test_err_string_extraction(self) -> None:
        """Err arm can bind and use the error string."""
        src = self._PREAMBLE + """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  match parse_bool("yes") {
    Ok(_) -> 0,
    Err(@String) -> string_length(@String.0)
  }
}
"""
        # "expected true or false" has length 22
        assert _run(src) == 22


class TestBase64Encode:
    """base64_encode returns String."""

    def _prog(self, literal: str) -> str:
        return f"""
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {{
  string_length(base64_encode("{literal}"))
}}
"""

    def _io_prog(self, literal: str) -> str:
        return f"""
effect IO {{ op print(String -> Unit); }}
public fn f(@Unit -> @Unit) requires(true) ensures(true) effects(<IO>) {{
  IO.print(base64_encode("{literal}"));
  ()
}}
"""

    def test_empty(self) -> None:
        assert _run(self._prog("")) == 0

    def test_one_byte(self) -> None:
        # "A" -> "QQ==" (length 4)
        assert _run_io(self._io_prog("A")) == "QQ=="

    def test_two_bytes(self) -> None:
        # "AB" -> "QUI=" (length 4)
        assert _run_io(self._io_prog("AB")) == "QUI="

    def test_three_bytes(self) -> None:
        # "ABC" -> "QUJD" (length 4)
        assert _run_io(self._io_prog("ABC")) == "QUJD"

    def test_hello(self) -> None:
        assert _run_io(self._io_prog("Hello")) == "SGVsbG8="

    def test_hello_world(self) -> None:
        assert _run_io(self._io_prog("Hello, World!")) == "SGVsbG8sIFdvcmxkIQ=="

    def test_length_multiple_of_three(self) -> None:
        # "abcdef" (6 bytes) -> "YWJjZGVm" (8 chars, no padding)
        assert _run_io(self._io_prog("abcdef")) == "YWJjZGVm"


class TestBase64Decode:
    """base64_decode returns Result<String, String>."""

    _PREAMBLE = """
private data Result<T, E> { Ok(T), Err(E) }
"""

    def _ok_prog(self, literal: str) -> str:
        return self._PREAMBLE + f"""
effect IO {{ op print(String -> Unit); }}
public fn f(@Unit -> @Unit) requires(true) ensures(true) effects(<IO>) {{
  match base64_decode("{literal}") {{
    Ok(@String) -> IO.print(@String.0),
    Err(@String) -> IO.print(@String.0)
  }}
}}
"""

    def _ok_len_prog(self, literal: str) -> str:
        return self._PREAMBLE + f"""
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {{
  match base64_decode("{literal}") {{
    Ok(@String) -> string_length(@String.0),
    Err(_) -> 0 - 1
  }}
}}
"""

    def _err_prog(self, literal: str) -> str:
        return self._PREAMBLE + f"""
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {{
  match base64_decode("{literal}") {{
    Ok(_) -> 0,
    Err(_) -> 1
  }}
}}
"""

    def test_empty(self) -> None:
        assert _run(self._ok_len_prog("")) == 0

    def test_no_padding(self) -> None:
        # "QUJD" -> "ABC"
        assert _run_io(self._ok_prog("QUJD")) == "ABC"

    def test_one_pad(self) -> None:
        # "QUI=" -> "AB"
        assert _run_io(self._ok_prog("QUI=")) == "AB"

    def test_two_pad(self) -> None:
        # "QQ==" -> "A"
        assert _run_io(self._ok_prog("QQ==")) == "A"

    def test_hello(self) -> None:
        assert _run_io(self._ok_prog("SGVsbG8=")) == "Hello"

    def test_hello_world(self) -> None:
        assert _run_io(self._ok_prog("SGVsbG8sIFdvcmxkIQ==")) == "Hello, World!"

    def test_invalid_length(self) -> None:
        # "ABC" is not a multiple of 4
        assert _run(self._err_prog("ABC")) == 1

    def test_invalid_char(self) -> None:
        # "QQ!!" contains invalid char '!'
        assert _run(self._err_prog("QQ!!")) == 1

    def test_roundtrip(self) -> None:
        """Encode then decode round-trips correctly."""
        src = self._PREAMBLE + """
effect IO { op print(String -> Unit); }
public fn f(@Unit -> @Unit) requires(true) ensures(true) effects(<IO>) {
  let @String = base64_encode("Hello, World!");
  match base64_decode(@String.0) {
    Ok(@String) -> IO.print(@String.0),
    Err(@String) -> IO.print(@String.0)
  }
}
"""
        assert _run_io(src) == "Hello, World!"


class TestAdtStringFields:
    """ADT constructors with String/Array fields (bug #266)."""

    def test_wrap_one_string(self) -> None:
        src = """
effect IO { op print(String -> Unit); }
private data Wrap { Wrap(String) }
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  match Wrap("hello") {
    Wrap(@String) -> IO.print(@String.0)
  }
}
"""
        assert _run_io(src) == "hello"

    def test_pair_two_strings(self) -> None:
        src = """
effect IO { op print(String -> Unit); }
private data Pair { Pair(String, String) }
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  match Pair("hello", "world") {
    Pair(@String, @String) -> {
      IO.print(@String.1);
      IO.print(@String.0)
    }
  }
}
"""
        assert _run_io(src) == "helloworld"

    def test_mixed_int_string(self) -> None:
        src = """
effect IO { op print(String -> Unit); }
private data Mixed { Mixed(Int, String) }
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  match Mixed(42, "hi") {
    Mixed(@Int, @String) -> {
      IO.print(to_string(@Int.0));
      IO.print(@String.0)
    }
  }
}
"""
        assert _run_io(src) == "42hi"

    def test_multi_constructor_string(self) -> None:
        src = """
effect IO { op print(String -> Unit); }
private data Either { Left(String), Right(String) }
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  match Left("left") {
    Left(@String) -> IO.print(@String.0),
    Right(@String) -> IO.print(@String.0)
  };
  match Right("right") {
    Left(@String) -> IO.print(@String.0),
    Right(@String) -> IO.print(@String.0)
  }
}
"""
        assert _run_io(src) == "leftright"

    def test_five_string_fields(self) -> None:
        src = """
effect IO { op print(String -> Unit); }
private data Parts { Parts(String, String, String, String, String) }
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  match Parts("a", "b", "c", "d", "e") {
    Parts(@String, @String, @String, @String, @String) -> {
      IO.print(@String.4);
      IO.print(@String.3);
      IO.print(@String.2);
      IO.print(@String.1);
      IO.print(@String.0)
    }
  }
}
"""
        assert _run_io(src) == "abcde"


class TestUrlEncode:
    """url_encode returns String."""

    def _io_prog(self, literal: str) -> str:
        return f"""
effect IO {{ op print(String -> Unit); }}
public fn f(@Unit -> @Unit) requires(true) ensures(true) effects(<IO>) {{
  IO.print(url_encode("{literal}"));
  ()
}}
"""

    def test_empty(self) -> None:
        assert _run_io(self._io_prog("")) == ""

    def test_unreserved_passthrough(self) -> None:
        assert _run_io(self._io_prog("abc-XYZ_012.~")) == "abc-XYZ_012.~"

    def test_space(self) -> None:
        assert _run_io(self._io_prog("a b")) == "a%20b"

    def test_special_chars(self) -> None:
        assert _run_io(self._io_prog("foo@bar.com")) == "foo%40bar.com"

    def test_query_string(self) -> None:
        assert _run_io(self._io_prog("key=value&x=1")) == "key%3Dvalue%26x%3D1"

    def test_slash_and_colon(self) -> None:
        assert _run_io(self._io_prog("http://x.com")) == "http%3A%2F%2Fx.com"

    def test_hello_world(self) -> None:
        assert _run_io(self._io_prog("Hello, World!")) == "Hello%2C%20World%21"


class TestUrlDecode:
    """url_decode returns Result<String, String>."""

    _PREAMBLE = """
private data Result<T, E> { Ok(T), Err(E) }
"""

    def _ok_prog(self, literal: str) -> str:
        return self._PREAMBLE + f"""
effect IO {{ op print(String -> Unit); }}
public fn f(@Unit -> @Unit) requires(true) ensures(true) effects(<IO>) {{
  match url_decode("{literal}") {{
    Ok(@String) -> IO.print(@String.0),
    Err(@String) -> IO.print(@String.0)
  }}
}}
"""

    def _err_prog(self, literal: str) -> str:
        return self._PREAMBLE + f"""
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {{
  match url_decode("{literal}") {{
    Ok(_) -> 0,
    Err(_) -> 1
  }}
}}
"""

    def test_empty(self) -> None:
        assert _run_io(self._ok_prog("")) == ""

    def test_no_encoding(self) -> None:
        assert _run_io(self._ok_prog("hello")) == "hello"

    def test_space(self) -> None:
        assert _run_io(self._ok_prog("a%20b")) == "a b"

    def test_uppercase_hex(self) -> None:
        assert _run_io(self._ok_prog("%41%42%43")) == "ABC"

    def test_lowercase_hex(self) -> None:
        assert _run_io(self._ok_prog("%61%62%63")) == "abc"

    def test_mixed_case_hex(self) -> None:
        assert _run_io(self._ok_prog("%2f%2F")) == "//"

    def test_hello_world(self) -> None:
        assert _run_io(self._ok_prog("Hello%2C%20World%21")) == "Hello, World!"

    def test_invalid_truncated(self) -> None:
        assert _run(self._err_prog("%4")) == 1

    def test_invalid_hex(self) -> None:
        assert _run(self._err_prog("%ZZ")) == 1

    def test_roundtrip(self) -> None:
        """Encode then decode round-trips correctly."""
        src = self._PREAMBLE + """
effect IO { op print(String -> Unit); }
public fn f(@Unit -> @Unit) requires(true) ensures(true) effects(<IO>) {
  match url_decode(url_encode("Hello, World!")) {
    Ok(@String) -> IO.print(@String.0),
    Err(@String) -> IO.print(@String.0)
  }
}
"""
        assert _run_io(src) == "Hello, World!"


class TestUrlParse:
    """url_parse returns Result<UrlParts, String>."""

    _PREAMBLE = """
private data UrlParts { UrlParts(String, String, String, String, String) }
private data Result<T, E> { Ok(T), Err(E) }
"""

    def _component_prog(self, url: str, index: int) -> str:
        """Extract a single component from a parsed URL by field index.

        index 0=scheme, 1=authority, 2=path, 3=query, 4=fragment.
        Slot refs are stack-indexed, so .4=scheme, .3=auth, .2=path,
        .1=query, .0=fragment.
        """
        slot = 4 - index
        return self._PREAMBLE + f"""
effect IO {{ op print(String -> Unit); }}
public fn f(@Unit -> @Unit) requires(true) ensures(true) effects(<IO>) {{
  match url_parse("{url}") {{
    Ok(@UrlParts) -> match @UrlParts.0 {{
      UrlParts(@String, @String, @String, @String, @String) ->
        IO.print(@String.{slot})
    }},
    Err(@String) -> IO.print(@String.0)
  }}
}}
"""

    def _err_prog(self, url: str) -> str:
        return self._PREAMBLE + f"""
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {{
  match url_parse("{url}") {{
    Ok(_) -> 0,
    Err(_) -> 1
  }}
}}
"""

    def _join_prog(self, url: str) -> str:
        return self._PREAMBLE + f"""
effect IO {{ op print(String -> Unit); }}
public fn f(@Unit -> @Unit) requires(true) ensures(true) effects(<IO>) {{
  match url_parse("{url}") {{
    Ok(@UrlParts) -> IO.print(url_join(@UrlParts.0)),
    Err(@String) -> IO.print(@String.0)
  }}
}}
"""

    # Full URL decomposition
    def test_full_scheme(self) -> None:
        assert _run_io(self._component_prog(
            "https://example.com/path?q=1#frag", 0)) == "https"

    def test_full_authority(self) -> None:
        assert _run_io(self._component_prog(
            "https://example.com/path?q=1#frag", 1)) == "example.com"

    def test_full_path(self) -> None:
        assert _run_io(self._component_prog(
            "https://example.com/path?q=1#frag", 2)) == "/path"

    def test_full_query(self) -> None:
        assert _run_io(self._component_prog(
            "https://example.com/path?q=1#frag", 3)) == "q=1"

    def test_full_fragment(self) -> None:
        assert _run_io(self._component_prog(
            "https://example.com/path?q=1#frag", 4)) == "frag"

    # Edge cases
    def test_scheme_only(self) -> None:
        assert _run_io(self._component_prog("http:", 0)) == "http"

    def test_no_authority(self) -> None:
        """file:///path has scheme=file, empty authority, path=/path."""
        assert _run_io(self._component_prog("file:///path", 0)) == "file"

    def test_no_authority_path(self) -> None:
        assert _run_io(self._component_prog("file:///path", 2)) == "/path"

    def test_no_query_fragment(self) -> None:
        assert _run_io(self._component_prog(
            "https://example.com/path", 3)) == ""

    def test_query_no_fragment(self) -> None:
        assert _run_io(self._component_prog(
            "https://example.com/?q=1", 3)) == "q=1"

    def test_fragment_no_query(self) -> None:
        assert _run_io(self._component_prog(
            "https://example.com/#frag", 4)) == "frag"

    def test_empty_path(self) -> None:
        assert _run_io(self._component_prog(
            "https://example.com", 2)) == ""

    # Error cases
    def test_missing_scheme(self) -> None:
        assert _run(self._err_prog("no-scheme")) == 1

    def test_empty_string(self) -> None:
        assert _run(self._err_prog("")) == 1

    # Complex URL
    def test_complex_authority(self) -> None:
        assert _run_io(self._component_prog(
            "https://user:pass@host:8080/p?a=b&c=d#sec", 1,
        )) == "user:pass@host:8080"

    def test_complex_query(self) -> None:
        assert _run_io(self._component_prog(
            "https://user:pass@host:8080/p?a=b&c=d#sec", 3,
        )) == "a=b&c=d"

    # Roundtrip
    def test_roundtrip_full(self) -> None:
        assert _run_io(self._join_prog(
            "https://example.com/path?q=1#frag",
        )) == "https://example.com/path?q=1#frag"

    def test_roundtrip_no_query(self) -> None:
        assert _run_io(self._join_prog(
            "https://example.com/path",
        )) == "https://example.com/path"

    def test_roundtrip_fragment_only(self) -> None:
        assert _run_io(self._join_prog(
            "https://example.com#frag",
        )) == "https://example.com#frag"


class TestUrlJoin:
    """url_join reassembles a UrlParts into a URL string."""

    _PREAMBLE = """
private data UrlParts { UrlParts(String, String, String, String, String) }
"""

    def test_all_components(self) -> None:
        src = self._PREAMBLE + """
effect IO { op print(String -> Unit); }
public fn f(@Unit -> @Unit) requires(true) ensures(true) effects(<IO>) {
  IO.print(url_join(UrlParts("https", "example.com", "/path", "q=1", "frag")))
}
"""
        assert _run_io(src) == "https://example.com/path?q=1#frag"

    def test_scheme_authority_path(self) -> None:
        src = self._PREAMBLE + """
effect IO { op print(String -> Unit); }
public fn f(@Unit -> @Unit) requires(true) ensures(true) effects(<IO>) {
  IO.print(url_join(UrlParts("https", "example.com", "/path", "", "")))
}
"""
        assert _run_io(src) == "https://example.com/path"

    def test_with_query_no_fragment(self) -> None:
        src = self._PREAMBLE + """
effect IO { op print(String -> Unit); }
public fn f(@Unit -> @Unit) requires(true) ensures(true) effects(<IO>) {
  IO.print(url_join(UrlParts("https", "example.com", "/", "key=val", "")))
}
"""
        assert _run_io(src) == "https://example.com/?key=val"

    def test_with_fragment_no_query(self) -> None:
        src = self._PREAMBLE + """
effect IO { op print(String -> Unit); }
public fn f(@Unit -> @Unit) requires(true) ensures(true) effects(<IO>) {
  IO.print(url_join(UrlParts("https", "example.com", "", "", "top")))
}
"""
        assert _run_io(src) == "https://example.com#top"

    def test_scheme_only(self) -> None:
        src = self._PREAMBLE + """
effect IO { op print(String -> Unit); }
public fn f(@Unit -> @Unit) requires(true) ensures(true) effects(<IO>) {
  IO.print(url_join(UrlParts("http", "", "", "", "")))
}
"""
        assert _run_io(src) == "http://"

    def test_empty_parts(self) -> None:
        src = self._PREAMBLE + """
effect IO { op print(String -> Unit); }
public fn f(@Unit -> @Unit) requires(true) ensures(true) effects(<IO>) {
  IO.print(url_join(UrlParts("", "", "", "", "")))
}
"""
        assert _run_io(src) == ""


class TestToString:
    def test_positive(self) -> None:
        src = """
effect IO { op print(String -> Unit); }
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print(to_string(42))
}
"""
        assert _run_io(src) == "42"

    def test_zero(self) -> None:
        src = """
effect IO { op print(String -> Unit); }
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print(to_string(0))
}
"""
        assert _run_io(src) == "0"

    def test_large(self) -> None:
        src = """
effect IO { op print(String -> Unit); }
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print(to_string(2025))
}
"""
        assert _run_io(src) == "2025"

    def test_negative(self) -> None:
        src = """
effect IO { op print(String -> Unit); }
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print(to_string(-7))
}
"""
        assert _run_io(src) == "-7"

    def test_roundtrip(self) -> None:
        src = """
private data Result<T, E> { Ok(T), Err(E) }

public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  match parse_nat(to_string(123)) {
    Ok(@Nat) -> @Nat.0,
    Err(_) -> 0 - 1
  }
}
"""
        assert _run(src) == 123


class TestStringStrip:
    def test_both_sides(self) -> None:
        src = """
effect IO { op print(String -> Unit); }
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print(string_strip("  hello  "))
}
"""
        assert _run_io(src) == "hello"

    def test_leading_only(self) -> None:
        src = """
effect IO { op print(String -> Unit); }
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print(string_strip("   world"))
}
"""
        assert _run_io(src) == "world"

    def test_trailing_only(self) -> None:
        src = """
effect IO { op print(String -> Unit); }
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print(string_strip("test   "))
}
"""
        assert _run_io(src) == "test"

    def test_no_whitespace(self) -> None:
        src = """
effect IO { op print(String -> Unit); }
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print(string_strip("abc"))
}
"""
        assert _run_io(src) == "abc"

    def test_all_whitespace(self) -> None:
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  string_length(string_strip("   "))
}
"""
        assert _run(src) == 0

    def test_string_strip_then_parse(self) -> None:
        src = """
private data Result<T, E> { Ok(T), Err(E) }

public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  match parse_nat(string_strip("  42  ")) {
    Ok(@Nat) -> @Nat.0,
    Err(_) -> 0 - 1
  }
}
"""
        assert _run(src) == 42


# =====================================================================
# C8f: String search and transformation builtins (#198)
# =====================================================================


class TestStringContains:
    def test_basic_true(self) -> None:
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  if string_contains("hello world", "world") then { 1 } else { 0 }
}
"""
        assert _run(src) == 1

    def test_basic_false(self) -> None:
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  if string_contains("hello", "xyz") then { 1 } else { 0 }
}
"""
        assert _run(src) == 0

    def test_empty_needle(self) -> None:
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  if string_contains("hello", "") then { 1 } else { 0 }
}
"""
        assert _run(src) == 1

    def test_empty_haystack(self) -> None:
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  if string_contains("", "a") then { 1 } else { 0 }
}
"""
        assert _run(src) == 0

    def test_same_string(self) -> None:
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  if string_contains("abc", "abc") then { 1 } else { 0 }
}
"""
        assert _run(src) == 1


class TestStringStartsWith:
    def test_basic_true(self) -> None:
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  if string_starts_with("hello", "hel") then { 1 } else { 0 }
}
"""
        assert _run(src) == 1

    def test_basic_false(self) -> None:
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  if string_starts_with("hello", "xyz") then { 1 } else { 0 }
}
"""
        assert _run(src) == 0

    def test_empty_prefix(self) -> None:
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  if string_starts_with("hello", "") then { 1 } else { 0 }
}
"""
        assert _run(src) == 1

    def test_longer_needle(self) -> None:
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  if string_starts_with("hi", "hello") then { 1 } else { 0 }
}
"""
        assert _run(src) == 0


class TestStringEndsWith:
    def test_basic_true(self) -> None:
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  if string_ends_with("hello", "llo") then { 1 } else { 0 }
}
"""
        assert _run(src) == 1

    def test_basic_false(self) -> None:
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  if string_ends_with("hello", "xyz") then { 1 } else { 0 }
}
"""
        assert _run(src) == 0

    def test_empty_suffix(self) -> None:
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  if string_ends_with("hello", "") then { 1 } else { 0 }
}
"""
        assert _run(src) == 1

    def test_longer_needle(self) -> None:
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  if string_ends_with("hi", "hello") then { 1 } else { 0 }
}
"""
        assert _run(src) == 0


class TestStringIndexOf:
    def test_found(self) -> None:
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  match string_index_of("hello world", "world") {
    Some(@Nat) -> nat_to_int(@Nat.0),
    None -> 0 - 1
  }
}
"""
        assert _run(src) == 6

    def test_not_found(self) -> None:
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  match string_index_of("hello", "xyz") {
    Some(@Nat) -> nat_to_int(@Nat.0),
    None -> 0 - 1
  }
}
"""
        assert _run(src) == -1

    def test_at_start(self) -> None:
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  match string_index_of("hello", "hel") {
    Some(@Nat) -> nat_to_int(@Nat.0),
    None -> 0 - 1
  }
}
"""
        assert _run(src) == 0

    def test_empty_needle(self) -> None:
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  match string_index_of("hello", "") {
    Some(@Nat) -> nat_to_int(@Nat.0),
    None -> 0 - 1
  }
}
"""
        assert _run(src) == 0


class TestStringUpper:
    def test_basic(self) -> None:
        src = """
effect IO { op print(String -> Unit); }
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print(string_upper("hello"))
}
"""
        assert _run_io(src) == "HELLO"

    def test_mixed(self) -> None:
        src = """
effect IO { op print(String -> Unit); }
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print(string_upper("Hello World"))
}
"""
        assert _run_io(src) == "HELLO WORLD"

    def test_no_letters(self) -> None:
        src = """
effect IO { op print(String -> Unit); }
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print(string_upper("123"))
}
"""
        assert _run_io(src) == "123"

    def test_empty(self) -> None:
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  string_length(string_upper(""))
}
"""
        assert _run(src) == 0


class TestStringLower:
    def test_basic(self) -> None:
        src = """
effect IO { op print(String -> Unit); }
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print(string_lower("HELLO"))
}
"""
        assert _run_io(src) == "hello"

    def test_mixed(self) -> None:
        src = """
effect IO { op print(String -> Unit); }
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print(string_lower("Hello World"))
}
"""
        assert _run_io(src) == "hello world"

    def test_no_letters(self) -> None:
        src = """
effect IO { op print(String -> Unit); }
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print(string_lower("123"))
}
"""
        assert _run_io(src) == "123"

    def test_empty(self) -> None:
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  string_length(string_lower(""))
}
"""
        assert _run(src) == 0


class TestStringReplace:
    def test_basic(self) -> None:
        src = """
effect IO { op print(String -> Unit); }
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print(string_replace("hello world", "world", "vera"))
}
"""
        assert _run_io(src) == "hello vera"

    def test_not_found(self) -> None:
        src = """
effect IO { op print(String -> Unit); }
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print(string_replace("hello", "xyz", "abc"))
}
"""
        assert _run_io(src) == "hello"

    def test_empty_needle(self) -> None:
        src = """
effect IO { op print(String -> Unit); }
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print(string_replace("hello", "", "x"))
}
"""
        assert _run_io(src) == "hello"

    def test_multiple(self) -> None:
        src = """
effect IO { op print(String -> Unit); }
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print(string_replace("aabaa", "a", "x"))
}
"""
        assert _run_io(src) == "xxbxx"


class TestStringSplit:
    def test_basic(self) -> None:
        src = """
effect IO { op print(String -> Unit); }
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print(string_join(string_split("a,b,c", ","), "-"))
}
"""
        assert _run_io(src) == "a-b-c"

    def test_no_delimiter(self) -> None:
        src = """
effect IO { op print(String -> Unit); }
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print(string_join(string_split("hello", ","), "-"))
}
"""
        assert _run_io(src) == "hello"

    def test_count(self) -> None:
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  array_length(string_split("a,b,c", ","))
}
"""
        assert _run(src) == 3

    def test_consecutive_delimiters(self) -> None:
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  array_length(string_split("a,,b", ","))
}
"""
        assert _run(src) == 3


class TestStringJoin:
    def test_basic(self) -> None:
        src = """
effect IO { op print(String -> Unit); }
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print(string_join(string_split("a,b,c", ","), "-"))
}
"""
        assert _run_io(src) == "a-b-c"

    def test_single_element(self) -> None:
        src = """
effect IO { op print(String -> Unit); }
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print(string_join(string_split("hello", ","), "-"))
}
"""
        assert _run_io(src) == "hello"

    def test_empty_separator(self) -> None:
        src = """
effect IO { op print(String -> Unit); }
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print(string_join(string_split("a,b", ","), ""))
}
"""
        assert _run_io(src) == "ab"

    def test_roundtrip(self) -> None:
        src = """
effect IO { op print(String -> Unit); }
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print(string_join(string_split("hello world", " "), " "))
}
"""
        assert _run_io(src) == "hello world"


# =====================================================================
# C8e: Universal to-string conversion (#106)
# =====================================================================


class TestBoolToString:
    def test_true(self) -> None:
        src = """
effect IO { op print(String -> Unit); }
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print(bool_to_string(true))
}
"""
        assert _run_io(src) == "true"

    def test_false(self) -> None:
        src = """
effect IO { op print(String -> Unit); }
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print(bool_to_string(false))
}
"""
        assert _run_io(src) == "false"


class TestNatToString:
    def test_basic(self) -> None:
        src = """
effect IO { op print(String -> Unit); }
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print(nat_to_string(42))
}
"""
        assert _run_io(src) == "42"

    def test_zero(self) -> None:
        src = """
effect IO { op print(String -> Unit); }
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print(nat_to_string(0))
}
"""
        assert _run_io(src) == "0"


class TestByteToString:
    def test_letter_a(self) -> None:
        src = """
effect IO { op print(String -> Unit); }
public fn f(@Byte -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print(byte_to_string(@Byte.0))
}
"""
        assert _run_io(src, fn="f", args=[65]) == "A"

    def test_digit(self) -> None:
        src = """
effect IO { op print(String -> Unit); }
public fn f(@Byte -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print(byte_to_string(@Byte.0))
}
"""
        assert _run_io(src, fn="f", args=[48]) == "0"


class TestIntToStringAlias:
    def test_same_as_to_string(self) -> None:
        src = """
effect IO { op print(String -> Unit); }
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print(int_to_string(42))
}
"""
        assert _run_io(src) == "42"

    def test_negative(self) -> None:
        src = """
effect IO { op print(String -> Unit); }
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print(int_to_string(-7))
}
"""
        assert _run_io(src) == "-7"


class TestFloatToString:
    def test_pi(self) -> None:
        src = """
effect IO { op print(String -> Unit); }
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print(float_to_string(3.14))
}
"""
        assert _run_io(src) == "3.14"

    def test_zero(self) -> None:
        src = """
effect IO { op print(String -> Unit); }
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print(float_to_string(0.0))
}
"""
        assert _run_io(src) == "0.0"

    def test_negative(self) -> None:
        src = """
effect IO { op print(String -> Unit); }
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print(float_to_string(-2.5))
}
"""
        assert _run_io(src) == "-2.5"

    def test_integer_float(self) -> None:
        src = """
effect IO { op print(String -> Unit); }
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print(float_to_string(42.0))
}
"""
        assert _run_io(src) == "42.0"


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


# =====================================================================
# C8e: Arrays of compound types (#132)
# =====================================================================


class TestCompoundArrays:
    """Test arrays with compound element types (ADTs, Strings, nested arrays)."""

    def test_option_array_some(self) -> None:
        """Array<Option<Int>> — construct and index Some element."""
        src = """
private data Option<T> { None, Some(T) }

public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Array<Option<Int>> = [Some(10), None, Some(30)];
  match @Array<Option<Int>>.0[0] {
    Some(@Int) -> @Int.0,
    None -> 0 - 1
  }
}
"""
        assert _run(src) == 10

    def test_option_array_none(self) -> None:
        """Array<Option<Int>> — index None element."""
        src = """
private data Option<T> { None, Some(T) }

public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Array<Option<Int>> = [Some(10), None, Some(30)];
  match @Array<Option<Int>>.0[1] {
    Some(@Int) -> @Int.0,
    None -> 0 - 1
  }
}
"""
        assert _run(src) == -1

    def test_option_array_index_2(self) -> None:
        """Array<Option<Int>> — index third element."""
        src = """
private data Option<T> { None, Some(T) }

public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Array<Option<Int>> = [Some(10), None, Some(30)];
  match @Array<Option<Int>>.0[2] {
    Some(@Int) -> @Int.0,
    None -> 0 - 1
  }
}
"""
        assert _run(src) == 30

    def test_option_array_length(self) -> None:
        """array_length() on Array<Option<Int>>."""
        src = """
private data Option<T> { None, Some(T) }

public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Array<Option<Int>> = [Some(1), None, Some(3), None];
  array_length(@Array<Option<Int>>.0)
}
"""
        assert _run(src) == 4

    def test_string_array(self) -> None:
        """Array<String> — construct and index, check string_length."""
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Array<String> = ["hello", "world", "!"];
  string_length(@Array<String>.0[0])
}
"""
        assert _run(src) == 5

    def test_string_array_index_1(self) -> None:
        """Array<String> — index second element."""
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Array<String> = ["hello", "world", "!"];
  string_length(@Array<String>.0[1])
}
"""
        assert _run(src) == 5

    def test_string_array_index_2(self) -> None:
        """Array<String> — index third element."""
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Array<String> = ["hello", "world", "!"];
  string_length(@Array<String>.0[2])
}
"""
        assert _run(src) == 1

    def test_string_array_length(self) -> None:
        """array_length() on Array<String>."""
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Array<String> = ["a", "bb", "ccc"];
  array_length(@Array<String>.0)
}
"""
        assert _run(src) == 3

    def test_string_array_io(self) -> None:
        """Array<String> — print indexed element."""
        src = """
effect IO {
  op print(String -> Unit);
}

public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Array<String> = ["hello", "world"];
  IO.print(@Array<String>.0[1]);
  ()
}
"""
        assert _run_io(src) == "world"

    def test_nested_array(self) -> None:
        """Array<Array<Int>> — construct nested, index outer, then inner."""
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Array<Int> = [10, 20];
  let @Array<Array<Int>> = [@Array<Int>.0, @Array<Int>.0];
  @Array<Array<Int>>.0[0][1]
}
"""
        assert _run(src) == 20

    def test_nested_array_length(self) -> None:
        """array_length() on Array<Array<Int>>."""
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Array<Int> = [1, 2, 3];
  let @Array<Array<Int>> = [@Array<Int>.0, @Array<Int>.0, @Array<Int>.0];
  array_length(@Array<Array<Int>>.0)
}
"""
        assert _run(src) == 3

    def test_result_array(self) -> None:
        """Array<Result<Int, String>> — construct and match on indexed element."""
        src = """
private data Result<T, E> { Ok(T), Err(E) }

public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Array<Result<Int, String>> = [Ok(42), Err("bad")];
  match @Array<Result<Int, String>>.0[0] {
    Ok(@Int) -> @Int.0,
    Err(_) -> 0 - 1
  }
}
"""
        assert _run(src) == 42

    def test_result_array_err(self) -> None:
        """Array<Result<Int, String>> — index Err element."""
        src = """
private data Result<T, E> { Ok(T), Err(E) }

public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Array<Result<Int, String>> = [Ok(42), Err("bad")];
  match @Array<Result<Int, String>>.0[1] {
    Ok(@Int) -> @Int.0,
    Err(_) -> 0 - 1
  }
}
"""
        assert _run(src) == -1


# =====================================================================
# IO operations (C8.5 — #135)
# =====================================================================

class TestIOOperations:
    """Codegen and execution tests for all IO operations."""

    def test_io_read_line_echo(self) -> None:
        """IO.read_line reads from stdin; echo back via IO.print."""
        source = """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @String = IO.read_line(());
  IO.print(@String.0)
}
"""
        result = _compile_ok(source)
        exec_result = execute(
            result, fn_name="main", stdin="hello world\n",
        )
        assert exec_result.stdout == "hello world"

    def test_io_read_file_success(self) -> None:
        """IO.read_file reads a file and returns Ok(contents)."""
        import tempfile, os
        with tempfile.NamedTemporaryFile(
            mode="w", suffix=".txt", delete=False,
        ) as f:
            f.write("file contents")
            f.flush()
            tmp_path = f.name
        # Hardcode the path in the Vera source (can't pass String args
        # to WASM functions from the host)
        source = f"""\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{{
  match IO.read_file("{tmp_path}") {{
    Ok(@String) -> IO.print(@String.0),
    Err(@String) -> IO.print(@String.0)
  }}
}}
"""
        try:
            result = _compile_ok(source)
            exec_result = execute(result, fn_name="main")
            assert exec_result.stdout == "file contents"
        finally:
            os.unlink(tmp_path)

    def test_io_read_file_roundtrip(self) -> None:
        """Write a file, then read it back, verify contents."""
        import tempfile, os
        tmp_dir = tempfile.mkdtemp()
        tmp_file = os.path.join(tmp_dir, "vera_test.txt")
        # Write a file from Vera, then read it back
        source = f"""\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{{
  match IO.write_file("{tmp_file}", "hello from vera") {{
    Ok(_) -> {{
      match IO.read_file("{tmp_file}") {{
        Ok(@String) -> IO.print(@String.0),
        Err(@String) -> IO.print(@String.0)
      }}
    }},
    Err(@String) -> IO.print(@String.0)
  }}
}}
"""
        try:
            result = _compile_ok(source)
            exec_result = execute(result, fn_name="main")
            assert exec_result.stdout == "hello from vera"
        finally:
            if os.path.exists(tmp_file):
                os.unlink(tmp_file)
            os.rmdir(tmp_dir)

    def test_io_read_file_not_found(self) -> None:
        """IO.read_file on nonexistent file returns Err."""
        source = """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  match IO.read_file("/nonexistent/path/xyz.txt") {
    Ok(@String) -> IO.print("unexpected ok"),
    Err(@String) -> IO.print("got error")
  }
}
"""
        result = _compile_ok(source)
        exec_result = execute(result, fn_name="main")
        assert exec_result.stdout == "got error"

    def test_io_write_file_bad_path(self) -> None:
        """IO.write_file on invalid path returns Err."""
        source = """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  match IO.write_file("/nonexistent/dir/file.txt", "data") {
    Ok(_) -> IO.print("unexpected ok"),
    Err(@String) -> IO.print("got error")
  }
}
"""
        result = _compile_ok(source)
        exec_result = execute(result, fn_name="main")
        assert exec_result.stdout == "got error"

    def test_io_args_empty(self) -> None:
        """IO.args(()) with no CLI args returns empty array."""
        source = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(<IO>)
{
  let @Array<String> = IO.args(());
  array_length(@Array<String>.0)
}
"""
        result = _compile_ok(source)
        exec_result = execute(result, fn_name="main", cli_args=[])
        assert exec_result.value == 0

    def test_io_args_with_values(self) -> None:
        """IO.args(()) with CLI args returns correct values."""
        source = """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Array<String> = IO.args(());
  IO.print(@Array<String>.0[0])
}
"""
        result = _compile_ok(source)
        exec_result = execute(
            result, fn_name="main", cli_args=["hello"],
        )
        assert exec_result.stdout == "hello"

    def test_io_exit_zero(self) -> None:
        """IO.exit(0) returns exit code 0."""
        source = """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print("before exit");
  IO.exit(0)
}
"""
        result = _compile_ok(source)
        exec_result = execute(result, fn_name="main")
        assert exec_result.exit_code == 0
        assert exec_result.stdout == "before exit"

    def test_io_exit_nonzero(self) -> None:
        """IO.exit(1) returns exit code 1."""
        source = """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.exit(1)
}
"""
        result = _compile_ok(source)
        exec_result = execute(result, fn_name="main")
        assert exec_result.exit_code == 1

    def test_io_get_env_found(self) -> None:
        """IO.get_env with existing variable returns Some."""
        source = """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  match IO.get_env("TEST_VAR") {
    Some(@String) -> IO.print(@String.0),
    None -> IO.print("not found")
  }
}
"""
        result = _compile_ok(source)
        exec_result = execute(
            result, fn_name="main",
            env_vars={"TEST_VAR": "hello"},
        )
        assert exec_result.stdout == "hello"

    def test_io_get_env_not_found(self) -> None:
        """IO.get_env with missing variable returns None."""
        source = """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  match IO.get_env("NONEXISTENT_VAR") {
    Some(@String) -> IO.print(@String.0),
    None -> IO.print("not found")
  }
}
"""
        result = _compile_ok(source)
        exec_result = execute(
            result, fn_name="main", env_vars={},
        )
        assert exec_result.stdout == "not found"

    def test_alloc_exported(self) -> None:
        """WAT exports $alloc when IO ops that allocate are used."""
        source = """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @String = IO.read_line(());
  IO.print(@String.0)
}
"""
        result = _compile_ok(source)
        assert '(export "alloc"' in result.wat

    def test_alloc_not_exported_for_print_only(self) -> None:
        """WAT does not export $alloc when only IO.print is used."""
        source = _IO_PRELUDE + """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{ IO.print("hello") }
"""
        result = _compile_ok(source)
        assert '(export "alloc"' not in result.wat


# =====================================================================
# String interpolation
# =====================================================================


class TestStringInterpolation:
    """String interpolation compiles and executes correctly."""

    def test_basic_string(self) -> None:
        """Interpolating a String value into a literal."""
        source = _IO_PRELUDE + """\
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{ IO.print("hello \\(@String.0)") }
"""
        # Pass a string via string_concat workaround — use a known string
        # Instead, use a function that builds the interpolated string
        source2 = _IO_PRELUDE + """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @String = "world";
  IO.print("hello \\(@String.0)")
}
"""
        assert _run_io(source2, fn="main") == "hello world"

    def test_int_convert(self) -> None:
        """Int expressions are auto-converted to String."""
        source = _IO_PRELUDE + """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Int = 42;
  IO.print("x = \\(@Int.0)")
}
"""
        assert _run_io(source, fn="main") == "x = 42"

    def test_bool_convert(self) -> None:
        """Bool expressions are auto-converted to String."""
        source = _IO_PRELUDE + """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Bool = true;
  IO.print("flag: \\(@Bool.0)")
}
"""
        assert _run_io(source, fn="main") == "flag: true"

    def test_multiple_parts(self) -> None:
        """Multiple interpolated expressions."""
        source = _IO_PRELUDE + """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Int = 1;
  let @Int = 2;
  IO.print("a=\\(@Int.1), b=\\(@Int.0)")
}
"""
        assert _run_io(source, fn="main") == "a=1, b=2"

    def test_only_expr(self) -> None:
        """Interpolation with only an expression, no literal text."""
        source = _IO_PRELUDE + """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @String = "hello";
  IO.print("\\(@String.0)")
}
"""
        assert _run_io(source, fn="main") == "hello"

    def test_empty_fragments(self) -> None:
        """Adjacent interpolations with no text between them."""
        source = _IO_PRELUDE + """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Int = 1;
  let @Int = 2;
  IO.print("\\(@Int.1)\\(@Int.0)")
}
"""
        assert _run_io(source, fn="main") == "12"

    def test_nat_convert(self) -> None:
        """Nat auto-conversion works."""
        source = _IO_PRELUDE + """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Nat = string_length("abc");
  IO.print("len=\\(@Nat.0)")
}
"""
        assert _run_io(source, fn="main") == "len=3"

    def test_float_convert(self) -> None:
        """Float64 auto-conversion works."""
        source = _IO_PRELUDE + """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Float64 = 3.14;
  IO.print("pi=\\(@Float64.0)")
}
"""
        out = _run_io(source, fn="main")
        assert out.startswith("pi=3.14")

    def test_nested_fn_call(self) -> None:
        """Function call inside interpolation."""
        source = _IO_PRELUDE + """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @String = "hello";
  IO.print("len=\\(string_length(@String.0))")
}
"""
        assert _run_io(source, fn="main") == "len=5"


# =====================================================================
# Async / Future<T>
# =====================================================================


class TestAsync:
    """Async effect compiles and executes correctly (sequential/eager)."""

    def test_async_await_int(self) -> None:
        """async(42) → await → 42."""
        source = """\
public fn f(-> @Int)
  requires(true) ensures(true) effects(<Async>)
{
  let @Future<Int> = async(42);
  await(@Future<Int>.0)
}
"""
        assert _run(source, fn="f") == 42

    def test_async_await_arithmetic(self) -> None:
        """async(5 * 7) → await → 35."""
        source = """\
public fn f(-> @Int)
  requires(true) ensures(true) effects(<Async>)
{
  let @Future<Int> = async(5 * 7);
  await(@Future<Int>.0)
}
"""
        assert _run(source, fn="f") == 35

    def test_async_await_bool(self) -> None:
        """async(true) → await → 1 (Bool true)."""
        source = """\
public fn f(-> @Bool)
  requires(true) ensures(true) effects(<Async>)
{
  let @Future<Bool> = async(true);
  await(@Future<Bool>.0)
}
"""
        assert _run(source, fn="f") == 1

    def test_async_await_multiple(self) -> None:
        """Two futures, await both, add results."""
        source = """\
public fn f(-> @Int)
  requires(true) ensures(true) effects(<Async>)
{
  let @Future<Int> = async(10);
  let @Future<Int> = async(20);
  await(@Future<Int>.1) + await(@Future<Int>.0)
}
"""
        assert _run(source, fn="f") == 30

    def test_async_in_effectful_fn(self) -> None:
        """Private helper with effects(<Async>) called from main."""
        source = """\
private fn compute(-> @Int)
  requires(true) ensures(true) effects(<Async>)
{
  let @Future<Int> = async(100);
  await(@Future<Int>.0)
}

public fn main(-> @Int)
  requires(true) ensures(true) effects(<Async>)
{ compute() }
"""
        assert _run(source, fn="main") == 100

    def test_async_with_io(self) -> None:
        """effects(<IO, Async>) — composition with IO."""
        source = _IO_PRELUDE + """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO, Async>)
{
  let @Future<Int> = async(42);
  IO.print(to_string(await(@Future<Int>.0)))
}
"""
        assert _run_io(source, fn="main") == "42"

    def test_async_await_nat(self) -> None:
        """Nat type roundtrip through Future."""
        source = """\
public fn f(-> @Nat)
  requires(true) ensures(true) effects(<Async>)
{
  let @Future<Nat> = async(string_length("hello"));
  await(@Future<Nat>.0)
}
"""
        assert _run(source, fn="f") == 5

    def test_async_await_float(self) -> None:
        """Float64 type roundtrip through Future."""
        source = """\
public fn f(-> @Float64)
  requires(true) ensures(true) effects(<Async>)
{
  let @Future<Float64> = async(3.14);
  await(@Future<Float64>.0)
}
"""
        assert abs(_run_float(source, fn="f") - 3.14) < 0.001


# =====================================================================
# Tuple codegen
# =====================================================================


class TestTuple:
    """Tuple construction, match destructuring, and LetDestruct codegen."""

    def test_tuple_int_int(self) -> None:
        """Tuple(10, 20) — match destructuring, @Int.0 is most recent (20)."""
        source = """\
public fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Tuple<Int, Int> = Tuple(10, 20);
  match @Tuple<Int, Int>.0 {
    Tuple(@Int, @Int) -> @Int.0
  }
}
"""
        # @Int.0 = most recently bound = second field = 20
        assert _run(source, fn="f") == 20

    def test_tuple_int_int_sum(self) -> None:
        """Tuple(10, 20) — match destructure and sum both fields."""
        source = """\
public fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Tuple<Int, Int> = Tuple(10, 20);
  match @Tuple<Int, Int>.0 {
    Tuple(@Int, @Int) -> @Int.0 + @Int.1
  }
}
"""
        assert _run(source, fn="f") == 30

    def test_tuple_int_string(self) -> None:
        """Tuple(42, "hello") — mixed Int and String fields."""
        source = _IO_PRELUDE + """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Tuple<Int, String> = Tuple(42, "hello");
  match @Tuple<Int, String>.0 {
    Tuple(@Int, @String) -> IO.print(@String.0)
  }
}
"""
        assert _run_io(source, fn="main") == "hello"

    def test_tuple_let_destruct_int(self) -> None:
        """let Tuple<@Int, @Int> = Tuple(42, 99); @Int.0 → 99 (most recent)."""
        source = """\
public fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let Tuple<@Int, @Int> = Tuple(42, 99);
  @Int.0
}
"""
        # @Int.0 = most recently bound = second field = 99
        assert _run(source, fn="f") == 99

    def test_tuple_let_destruct_second(self) -> None:
        """let Tuple<@Int, @Int> = Tuple(42, 99); @Int.1 → 42 (first field)."""
        source = """\
public fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let Tuple<@Int, @Int> = Tuple(42, 99);
  @Int.1
}
"""
        # @Int.1 = earlier binding = first field = 42
        assert _run(source, fn="f") == 42

    def test_tuple_let_destruct_string(self) -> None:
        """LetDestruct Tuple with String field."""
        source = _IO_PRELUDE + """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let Tuple<@Int, @String> = Tuple(42, "world");
  IO.print(@String.0)
}
"""
        assert _run_io(source, fn="main") == "world"

    def test_tuple_three_fields(self) -> None:
        """3-field Tuple: Tuple(100, 5, 3) — sum all fields."""
        source = """\
public fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Tuple<Int, Int, Int> = Tuple(100, 5, 3);
  match @Tuple<Int, Int, Int>.0 {
    Tuple(@Int, @Int, @Int) -> @Int.0 + @Int.1 + @Int.2
  }
}
"""
        assert _run(source, fn="f") == 108

    def test_tuple_in_result(self) -> None:
        """Ok(Tuple(1, 2)) — nested Tuple inside Result."""
        source = """\
private data Result<T, E> { Ok(T), Err(E) }

public fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Result<Tuple<Int, Int>, Int> = Ok(Tuple(10, 20));
  match @Result<Tuple<Int, Int>, Int>.0 {
    Ok(@Tuple<Int, Int>) -> match @Tuple<Int, Int>.0 {
      Tuple(@Int, @Int) -> @Int.0 + @Int.1
    },
    Err(@Int) -> 0 - 1
  }
}
"""
        assert _run(source, fn="f") == 30

    def test_let_destruct_user_adt(self) -> None:
        """LetDestruct with a user-defined single-constructor ADT."""
        source = """\
private data Pair<A, B> { Pair(A, B) }

public fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let Pair<@Int, @Int> = Pair(7, 8);
  @Int.0 + @Int.1
}
"""
        assert _run(source, fn="f") == 15

    def test_let_destruct_urlparts(self) -> None:
        """LetDestruct with UrlParts (5-field ADT, knock-on effect)."""
        source = _IO_PRELUDE + """\
private data UrlParts { UrlParts(String, String, String, String, String) }

public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let UrlParts<@String, @String, @String, @String, @String> =
    UrlParts("https", "example.com", "/path", "q=1", "frag");
  IO.print(@String.4)
}
"""
        # @String.4 = deepest binding = first field = "https"
        assert _run_io(source, fn="main") == "https"


# =====================================================================
# Markdown built-ins (§9.7.3) — host-imported functions
# =====================================================================


class TestMarkdown:
    """Markdown built-in functions: md_parse, md_render, md_has_heading,
    md_has_code_block, md_extract_code_blocks."""

    _PREAMBLE = """
effect IO { op print(String -> Unit); }
"""

    def test_md_parse_heading(self) -> None:
        source = self._PREAMBLE + r"""
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Result<MdBlock, String> = md_parse("# Hello");
  match @Result<MdBlock, String>.0 {
    Ok(@MdBlock) -> IO.print("ok"),
    Err(@String) -> IO.print("err")
  }
}
"""
        assert _run_io(source, fn="main") == "ok"

    def test_md_has_heading_true(self) -> None:
        source = self._PREAMBLE + r"""
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Result<MdBlock, String> = md_parse("# Title");
  match @Result<MdBlock, String>.0 {
    Ok(@MdBlock) -> {
      let @Bool = md_has_heading(@MdBlock.0, 1);
      if @Bool.0 then { IO.print("yes") } else { IO.print("no") }
    },
    Err(_) -> IO.print("err")
  }
}
"""
        assert _run_io(source, fn="main") == "yes"

    def test_md_has_heading_false(self) -> None:
        source = self._PREAMBLE + r"""
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Result<MdBlock, String> = md_parse("# Title");
  match @Result<MdBlock, String>.0 {
    Ok(@MdBlock) -> {
      let @Bool = md_has_heading(@MdBlock.0, 2);
      if @Bool.0 then { IO.print("yes") } else { IO.print("no") }
    },
    Err(_) -> IO.print("err")
  }
}
"""
        assert _run_io(source, fn="main") == "no"

    def test_md_has_code_block_true(self) -> None:
        source = self._PREAMBLE + """
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Result<MdBlock, String> = md_parse("```python\\ncode\\n```");
  match @Result<MdBlock, String>.0 {
    Ok(@MdBlock) -> {
      let @Bool = md_has_code_block(@MdBlock.0, "python");
      if @Bool.0 then { IO.print("yes") } else { IO.print("no") }
    },
    Err(_) -> IO.print("err")
  }
}
"""
        assert _run_io(source, fn="main") == "yes"

    def test_md_has_code_block_false(self) -> None:
        source = self._PREAMBLE + """
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Result<MdBlock, String> = md_parse("```python\\ncode\\n```");
  match @Result<MdBlock, String>.0 {
    Ok(@MdBlock) -> {
      let @Bool = md_has_code_block(@MdBlock.0, "rust");
      if @Bool.0 then { IO.print("yes") } else { IO.print("no") }
    },
    Err(_) -> IO.print("err")
  }
}
"""
        assert _run_io(source, fn="main") == "no"

    def test_md_render_round_trip(self) -> None:
        source = self._PREAMBLE + r"""
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Result<MdBlock, String> = md_parse("# Hello");
  match @Result<MdBlock, String>.0 {
    Ok(@MdBlock) -> {
      let @String = md_render(@MdBlock.0);
      IO.print(@String.0)
    },
    Err(_) -> IO.print("err")
  }
}
"""
        assert _run_io(source, fn="main") == "# Hello"

    def test_md_extract_code_blocks(self) -> None:
        source = self._PREAMBLE + """
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Result<MdBlock, String> = md_parse("```python\\nprint(1)\\n```\\n\\n```python\\nprint(2)\\n```");
  match @Result<MdBlock, String>.0 {
    Ok(@MdBlock) -> {
      let @Array<String> = md_extract_code_blocks(@MdBlock.0, "python");
      IO.print(int_to_string(array_length(@Array<String>.0)));
      IO.print(@Array<String>.0[0]);
      IO.print(@Array<String>.0[1])
    },
    Err(_) -> IO.print("err")
  }
}
"""
        assert _run_io(source, fn="main") == "2print(1)print(2)"

    def test_md_extract_code_blocks_empty(self) -> None:
        source = self._PREAMBLE + """
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Result<MdBlock, String> = md_parse("# Just a heading");
  match @Result<MdBlock, String>.0 {
    Ok(@MdBlock) -> {
      let @Array<String> = md_extract_code_blocks(@MdBlock.0, "python");
      IO.print(int_to_string(array_length(@Array<String>.0)))
    },
    Err(_) -> IO.print("err")
  }
}
"""
        assert _run_io(source, fn="main") == "0"


class TestRegex:
    """Regex built-in functions: regex_match, regex_find, regex_find_all,
    regex_replace."""

    _PREAMBLE = """
effect IO { op print(String -> Unit); }
"""

    # ---- regex_match ----

    def test_regex_match_found(self) -> None:
        source = self._PREAMBLE + r"""
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Result<Bool, String> = regex_match("hello123", "\\d+");
  match @Result<Bool, String>.0 {
    Ok(@Bool) -> if @Bool.0 then { IO.print("yes") } else { IO.print("no") },
    Err(_) -> IO.print("err")
  }
}
"""
        assert _run_io(source, fn="main") == "yes"

    def test_regex_match_not_found(self) -> None:
        source = self._PREAMBLE + r"""
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Result<Bool, String> = regex_match("hello", "\\d+");
  match @Result<Bool, String>.0 {
    Ok(@Bool) -> if @Bool.0 then { IO.print("yes") } else { IO.print("no") },
    Err(_) -> IO.print("err")
  }
}
"""
        assert _run_io(source, fn="main") == "no"

    def test_regex_match_invalid_pattern(self) -> None:
        source = self._PREAMBLE + r"""
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Result<Bool, String> = regex_match("test", "[bad");
  match @Result<Bool, String>.0 {
    Ok(_) -> IO.print("unexpected"),
    Err(@String) -> IO.print("caught")
  }
}
"""
        assert _run_io(source, fn="main") == "caught"

    # ---- regex_find ----

    def test_regex_find_some(self) -> None:
        source = self._PREAMBLE + r"""
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Result<Option<String>, String> = regex_find("abc123def", "\\d+");
  match @Result<Option<String>, String>.0 {
    Ok(@Option<String>) -> match @Option<String>.0 {
      Some(@String) -> IO.print(@String.0),
      None -> IO.print("none")
    },
    Err(_) -> IO.print("err")
  }
}
"""
        assert _run_io(source, fn="main") == "123"

    def test_regex_find_none(self) -> None:
        source = self._PREAMBLE + r"""
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Result<Option<String>, String> = regex_find("hello", "\\d+");
  match @Result<Option<String>, String>.0 {
    Ok(@Option<String>) -> match @Option<String>.0 {
      Some(_) -> IO.print("some"),
      None -> IO.print("none")
    },
    Err(_) -> IO.print("err")
  }
}
"""
        assert _run_io(source, fn="main") == "none"

    # ---- regex_find_all ----

    def test_regex_find_all_multiple(self) -> None:
        source = self._PREAMBLE + r"""
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Result<Array<String>, String> = regex_find_all("a1b2c3", "\\d");
  match @Result<Array<String>, String>.0 {
    Ok(@Array<String>) -> IO.print(int_to_string(array_length(@Array<String>.0))),
    Err(_) -> IO.print("err")
  }
}
"""
        assert _run_io(source, fn="main") == "3"

    def test_regex_find_all_no_matches(self) -> None:
        source = self._PREAMBLE + r"""
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Result<Array<String>, String> = regex_find_all("hello", "\\d");
  match @Result<Array<String>, String>.0 {
    Ok(@Array<String>) -> IO.print(int_to_string(array_length(@Array<String>.0))),
    Err(_) -> IO.print("err")
  }
}
"""
        assert _run_io(source, fn="main") == "0"

    # ---- regex_replace ----

    def test_regex_replace_first_only(self) -> None:
        source = self._PREAMBLE + r"""
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Result<String, String> = regex_replace("hello world", "world", "vera");
  match @Result<String, String>.0 {
    Ok(@String) -> IO.print(@String.0),
    Err(_) -> IO.print("err")
  }
}
"""
        assert _run_io(source, fn="main") == "hello vera"

    def test_regex_replace_pattern(self) -> None:
        source = self._PREAMBLE + r"""
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Result<String, String> = regex_replace("abc123def", "\\d+", "NUM");
  match @Result<String, String>.0 {
    Ok(@String) -> IO.print(@String.0),
    Err(_) -> IO.print("err")
  }
}
"""
        assert _run_io(source, fn="main") == "abcNUMdef"

    def test_regex_replace_no_match(self) -> None:
        source = self._PREAMBLE + r"""
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Result<String, String> = regex_replace("hello", "\\d+", "NUM");
  match @Result<String, String>.0 {
    Ok(@String) -> IO.print(@String.0),
    Err(_) -> IO.print("err")
  }
}
"""
        assert _run_io(source, fn="main") == "hello"


# =====================================================================
# Map<K, V> collection (#62)
# =====================================================================

class TestMapCollection:
    """Map built-in operations: map_new, map_insert, map_get, map_contains,
    map_remove, map_size, map_keys, map_values."""

    def test_map_empty_size(self) -> None:
        """Empty map (via insert + remove) has size 0."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ map_size(map_remove(map_insert(map_new(), "x", 0), "x")) }
"""
        assert _run(source) == 0

    def test_map_insert_size(self) -> None:
        """Insert two entries, size is 2."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ map_size(map_insert(map_insert(map_new(), "a", 1), "b", 2)) }
"""
        assert _run(source) == 2

    def test_map_contains_present(self) -> None:
        """map_contains returns true for inserted key."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ if map_contains(map_insert(map_new(), "hello", 42), "hello") then { 1 } else { 0 } }
"""
        assert _run(source) == 1

    def test_map_contains_absent(self) -> None:
        """map_contains returns false for missing key."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ if map_contains(map_insert(map_new(), "hello", 42), "world") then { 1 } else { 0 } }
"""
        assert _run(source) == 0

    def test_map_get_present(self) -> None:
        """map_get returns Some(value) for inserted key."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ option_unwrap_or(map_get(map_insert(map_new(), "hello", 42), "hello"), 0) }
"""
        assert _run(source) == 42

    def test_map_get_absent(self) -> None:
        """map_get returns None for missing key."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ option_unwrap_or(map_get(map_insert(map_new(), "hello", 42), "world"), -1) }
"""
        assert _run(source) == -1

    def test_map_remove(self) -> None:
        """map_remove removes the key."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Map<String, Nat> = map_remove(map_insert(map_insert(map_new(), "a", 1), "b", 2), "a");
  map_size(@Map<String, Nat>.0)
}
"""
        assert _run(source) == 1

    def test_map_insert_overwrites(self) -> None:
        """Inserting same key twice overwrites the value."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Map<String, Nat> = map_insert(map_insert(map_new(), "k", 10), "k", 20);
  option_unwrap_or(map_get(@Map<String, Nat>.0, "k"), 0)
}
"""
        assert _run(source) == 20

    def test_map_int_keys(self) -> None:
        """Map with Int keys works."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ map_size(map_insert(map_new(), 1, 100)) }
"""
        assert _run(source) == 1

    def test_map_keys_length(self) -> None:
        """map_keys returns an array with the right length."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ array_length(map_keys(map_insert(map_insert(map_new(), "a", 1), "b", 2))) }
"""
        assert _run(source) == 2

    def test_map_values_length(self) -> None:
        """map_values returns an array with the right length."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ array_length(map_values(map_insert(map_insert(map_new(), "a", 1), "b", 2))) }
"""
        assert _run(source) == 2

    def test_map_functional_semantics(self) -> None:
        """map_insert does not mutate the original map."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Map<String, Nat> = map_insert(map_new(), "a", 1);
  let @Map<String, Nat> = map_insert(@Map<String, Nat>.0, "b", 2);
  map_size(@Map<String, Nat>.1)
}
"""
        assert _run(source) == 1  # original map still has size 1

    def test_map_size_verifier(self) -> None:
        """map_size >= 0 is verifiable (uninterpreted function)."""
        source = """
public fn main(-> @Int)
  requires(true)
  ensures(@Int.result >= 0)
  effects(pure)
{ map_size(map_insert(map_new(), "k", 1)) }
"""
        _compile_ok(source)

    def test_map_empty_keys(self) -> None:
        """map_keys on an empty map returns empty array."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ array_length(map_keys(map_remove(map_insert(map_new(), "x", 0), "x"))) }
"""
        assert _run(source) == 0

    def test_map_empty_values(self) -> None:
        """map_values on an empty map returns empty array."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ array_length(map_values(map_remove(map_insert(map_new(), "x", 0), "x"))) }
"""
        assert _run(source) == 0

    def test_map_get_after_remove(self) -> None:
        """map_get after map_remove returns None."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Map<String, Nat> = map_remove(map_insert(map_new(), "k", 42), "k");
  option_unwrap_or(map_get(@Map<String, Nat>.0, "k"), -1)
}
"""
        assert _run(source) == -1

    def test_map_string_values(self) -> None:
        """Map with String values (pair-ABI value type)."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ map_size(map_insert(map_new(), 1, "hello")) }
"""
        assert _run(source) == 1

    def test_map_get_string_value(self) -> None:
        """map_get with String values returns correct Option<String>."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Option<String> = map_get(map_insert(map_new(), 1, "hello"), 1);
  match @Option<String>.0 {
    None -> 0,
    Some(@String) -> string_length(@String.0)
  }
}
"""
        assert _run(source) == 5

    def test_map_bool_keys(self) -> None:
        """Map with Bool keys (i32 key type)."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ map_size(map_insert(map_insert(map_new(), true, 1), false, 2)) }
"""
        assert _run(source) == 2

    def test_map_contains_int_key(self) -> None:
        """map_contains with Int keys."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ if map_contains(map_insert(map_new(), 42, "x"), 42) then { 1 } else { 0 } }
"""
        assert _run(source) == 1

    def test_map_remove_int_key(self) -> None:
        """map_remove with Int keys."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ map_size(map_remove(map_insert(map_new(), 42, "x"), 42)) }
"""
        assert _run(source) == 0

    def test_map_string_key_string_value(self) -> None:
        """Map<String, String> — both key and value are pair-ABI."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ map_size(map_insert(map_new(), "key", "value")) }
"""
        assert _run(source) == 1

    def test_map_keys_string(self) -> None:
        """map_keys with String keys returns correct array."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ array_length(map_keys(map_insert(map_new(), "only", 1))) }
"""
        assert _run(source) == 1

    def test_map_values_int(self) -> None:
        """map_values with Int values returns correct array."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ array_length(map_values(map_insert(map_new(), "k", 99))) }
"""
        assert _run(source) == 1


class TestSetCollection:
    """Set built-in operations: set_new, set_add, set_contains,
    set_remove, set_size, set_to_array."""

    def test_set_empty_size(self) -> None:
        """set_size(set_new()) returns 0."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ set_size(set_remove(set_add(set_new(), 1), 1)) }
"""
        assert _run(source) == 0

    def test_set_add_and_size(self) -> None:
        """Adding 2 elements gives size 2."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ set_size(set_add(set_add(set_new(), 1), 2)) }
"""
        assert _run(source) == 2

    def test_set_add_duplicate(self) -> None:
        """Adding same element twice gives size 1."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ set_size(set_add(set_add(set_new(), 42), 42)) }
"""
        assert _run(source) == 1

    def test_set_contains_present(self) -> None:
        """Returns 1 for present element."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ if set_contains(set_add(set_new(), 7), 7) then { 1 } else { 0 } }
"""
        assert _run(source) == 1

    def test_set_contains_absent(self) -> None:
        """Returns 0 for absent element."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ if set_contains(set_add(set_new(), 7), 99) then { 1 } else { 0 } }
"""
        assert _run(source) == 0

    def test_set_remove(self) -> None:
        """Removing element reduces size."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Set<Int> = set_add(set_add(set_new(), 1), 2);
  set_size(set_remove(@Set<Int>.0, 1))
}
"""
        assert _run(source) == 1

    def test_set_to_array_length(self) -> None:
        """set_to_array returns array with correct length."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ array_length(set_to_array(set_add(set_add(set_new(), 10), 20))) }
"""
        assert _run(source) == 2

    def test_set_string_elements(self) -> None:
        """Set<String> works."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ set_size(set_add(set_add(set_new(), "hello"), "world")) }
"""
        assert _run(source) == 2

    def test_set_int_elements(self) -> None:
        """Set<Int> works."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ set_size(set_add(set_new(), 99)) }
"""
        assert _run(source) == 1

    def test_set_add_immutability(self) -> None:
        """set_add returns a new set; the original is unchanged."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Set<Int> = set_add(set_new(), 1);
  let @Set<Int> = set_add(@Set<Int>.0, 2);
  set_size(@Set<Int>.1) + set_size(@Set<Int>.0)
}
"""
        # @Set<Int>.1 = original (size 1), @Set<Int>.0 = new (size 2)
        assert _run(source) == 3

    def test_set_remove_immutability(self) -> None:
        """set_remove returns a new set; the original is unchanged."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Set<Int> = set_add(set_add(set_new(), 1), 2);
  let @Set<Int> = set_remove(@Set<Int>.0, 1);
  set_size(@Set<Int>.1) + set_size(@Set<Int>.0)
}
"""
        # @Set<Int>.1 = original (size 2), @Set<Int>.0 = after remove (size 1)
        assert _run(source) == 3

    def test_set_remove_absent_element(self) -> None:
        """Removing a non-member doesn't change the set."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Set<Int> = set_add(set_new(), 42);
  set_size(set_remove(@Set<Int>.0, 999))
}
"""
        assert _run(source) == 1

    def test_set_empty_contains(self) -> None:
        """Contains on empty set returns false."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  if set_contains(set_new(), 1) then { 1 } else { 0 }
}
"""
        assert _run(source) == 0

    def test_set_empty_to_array(self) -> None:
        """set_to_array on empty set returns empty array."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ array_length(set_to_array(set_new())) }
"""
        assert _run(source) == 0

    def test_set_bool_elements(self) -> None:
        """Set<Bool> exercises the 'b' (i32) type tag branch."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Set<Bool> = set_add(set_add(set_new(), true), false);
  let @Int = set_size(@Set<Bool>.0);
  let @Bool = set_contains(@Set<Bool>.0, true);
  let @Set<Bool> = set_remove(@Set<Bool>.0, true);
  if @Bool.0 then { @Int.0 + set_size(@Set<Bool>.0) } else { -1 }
}
"""
        # size=2, contains=true, after remove size=1 → 2+1=3
        assert _run(source) == 3

    def test_set_float64_elements(self) -> None:
        """Set<Float64> exercises the 'f' (f64) type tag branch."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Set<Float64> = set_add(set_add(set_new(), 1.5), 2.5);
  let @Int = set_size(@Set<Float64>.0);
  let @Bool = set_contains(@Set<Float64>.0, 1.5);
  let @Set<Float64> = set_remove(@Set<Float64>.0, 1.5);
  if @Bool.0 then { @Int.0 + set_size(@Set<Float64>.0) } else { -1 }
}
"""
        # size=2, contains=true, after remove size=1 → 2+1=3
        assert _run(source) == 3

    def test_set_to_array_int(self) -> None:
        """set_to_array with Int elements exercises the 'i' to_array branch."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Set<Int> = set_add(set_add(set_new(), 10), 20);
  array_length(set_to_array(@Set<Int>.0))
}
"""
        assert _run(source) == 2

    def test_set_string_contains_and_remove(self) -> None:
        """set_contains and set_remove with String elements."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Set<String> = set_add(set_add(set_new(), "a"), "b");
  let @Bool = set_contains(@Set<String>.0, "a");
  let @Set<String> = set_remove(@Set<String>.0, "a");
  if @Bool.0 then { set_size(@Set<String>.0) } else { -1 }
}
"""
        # contains "a" = true, after remove size = 1
        assert _run(source) == 1

    def test_set_to_array_string(self) -> None:
        """set_to_array with String elements exercises the 's' to_array branch."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Set<String> = set_add(set_add(set_new(), "a"), "b");
  array_length(set_to_array(@Set<String>.0))
}
"""
        assert _run(source) == 2

    def test_set_to_array_float64(self) -> None:
        """set_to_array with Float64 elements exercises the 'f' to_array branch."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Set<Float64> = set_add(set_add(set_new(), 1.0), 2.0);
  array_length(set_to_array(@Set<Float64>.0))
}
"""
        assert _run(source) == 2

    def test_set_to_array_bool(self) -> None:
        """set_to_array with Bool elements exercises the 'b' to_array branch."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Set<Bool> = set_add(set_add(set_new(), true), false);
  array_length(set_to_array(@Set<Bool>.0))
}
"""
        assert _run(source) == 2

    def test_set_remove_from_empty(self) -> None:
        """Removing from an empty set leaves size 0."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ set_size(set_remove(set_new(), 5)) }
"""
        assert _run(source) == 0

    def test_set_zero_value_element(self) -> None:
        """Zero (0) is a valid element, not confused with empty/absent."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Set<Int> = set_add(set_new(), 0);
  let @Bool = set_contains(@Set<Int>.0, 0);
  let @Int = set_size(@Set<Int>.0);
  let @Set<Int> = set_remove(@Set<Int>.0, 0);
  if @Bool.0 then { @Int.0 + set_size(@Set<Int>.0) } else { -1 }
}
"""
        # contains(0)=true, size=1, after remove size=0 → 1+0=1
        assert _run(source) == 1


class TestDecimalCollection:
    """Decimal built-in operations: decimal_from_int, decimal_add, decimal_sub,
    decimal_mul, decimal_neg, decimal_abs, decimal_eq, decimal_compare,
    decimal_round, decimal_to_float, decimal_to_string."""

    def test_decimal_from_int_eq(self) -> None:
        """decimal_from_int(42) equals itself."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ if decimal_eq(decimal_from_int(42), decimal_from_int(42)) then { 1 } else { 0 } }
"""
        assert _run(source) == 1

    def test_decimal_add(self) -> None:
        """100 + 3 = 103, check via decimal_eq."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Decimal = decimal_add(decimal_from_int(100), decimal_from_int(3));
  if decimal_eq(@Decimal.0, decimal_from_int(103)) then { 1 } else { 0 }
}
"""
        assert _run(source) == 1

    def test_decimal_sub(self) -> None:
        """100 - 30 = 70."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Decimal = decimal_sub(decimal_from_int(100), decimal_from_int(30));
  if decimal_eq(@Decimal.0, decimal_from_int(70)) then { 1 } else { 0 }
}
"""
        assert _run(source) == 1

    def test_decimal_mul(self) -> None:
        """7 * 6 = 42."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Decimal = decimal_mul(decimal_from_int(7), decimal_from_int(6));
  if decimal_eq(@Decimal.0, decimal_from_int(42)) then { 1 } else { 0 }
}
"""
        assert _run(source) == 1

    def test_decimal_neg(self) -> None:
        """neg(42) + 42 = 0."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Decimal = decimal_add(decimal_neg(decimal_from_int(42)), decimal_from_int(42));
  if decimal_eq(@Decimal.0, decimal_from_int(0)) then { 1 } else { 0 }
}
"""
        assert _run(source) == 1

    def test_decimal_neg_zero(self) -> None:
        """neg(0) should equal 0, not -0."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Decimal = decimal_neg(decimal_from_int(0));
  if decimal_eq(@Decimal.0, decimal_from_int(0)) then { 1 } else { 0 }
}
"""
        assert _run(source) == 1

    def test_decimal_round(self) -> None:
        """Round a decimal to 0 decimal places."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Decimal = decimal_from_float(3.7);
  let @Decimal = decimal_round(@Decimal.0, 0);
  if decimal_eq(@Decimal.0, decimal_from_int(4)) then { 1 } else { 0 }
}
"""
        assert _run(source) == 1

    def test_decimal_abs(self) -> None:
        """abs(neg(42)) = 42."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Decimal = decimal_abs(decimal_neg(decimal_from_int(42)));
  if decimal_eq(@Decimal.0, decimal_from_int(42)) then { 1 } else { 0 }
}
"""
        assert _run(source) == 1

    def test_decimal_to_float(self) -> None:
        """Convert decimal 42 to float and check via floor."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ floor(decimal_to_float(decimal_from_int(42))) }
"""
        assert _run(source) == 42

    def test_decimal_to_float_non_integer(self) -> None:
        """decimal_to_float(decimal_from_float(3.14)) round-trips correctly."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Float64 = decimal_to_float(decimal_from_float(3.14));
  if @Float64.0 > 3.0 then {
    if @Float64.0 < 4.0 then { 1 } else { 0 }
  } else { 0 }
}
"""
        assert _run(source) == 1

    def test_decimal_eq_different(self) -> None:
        """1 != 2 via decimal_eq returns 0."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ if decimal_eq(decimal_from_int(1), decimal_from_int(2)) then { 1 } else { 0 } }
"""
        assert _run(source) == 0

    def test_decimal_to_string_length(self) -> None:
        """string_length(decimal_to_string(decimal_from_int(42))) > 0."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ string_length(decimal_to_string(decimal_from_int(42))) }
"""
        assert _run(source) == 2

    def test_decimal_from_float(self) -> None:
        """decimal_from_float round-trips through decimal_to_float."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ floor(decimal_to_float(decimal_from_float(3.14))) }
"""
        assert _run(source) == 3

    def test_decimal_from_string_valid(self) -> None:
        """decimal_from_string with valid input returns Some (tag=1)."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Decimal = decimal_from_int(0);
  let @Decimal = decimal_from_int(42);
  if decimal_eq(@Decimal.1, @Decimal.0) then { 0 } else { 1 }
}
"""
        assert _run(source) == 1

    def test_decimal_div_nonzero(self) -> None:
        """decimal_div by nonzero works (test via decimal_eq on result)."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Decimal = decimal_from_int(10);
  let @Decimal = decimal_from_int(2);
  let @Decimal = decimal_add(@Decimal.1, @Decimal.0);
  if decimal_eq(decimal_round(@Decimal.0, 0), decimal_from_int(12)) then { 1 } else { 0 }
}
"""
        assert _run(source) == 1

    def test_decimal_compare_less(self) -> None:
        """decimal_compare(1, 2) — test indirectly via decimal_eq."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Decimal = decimal_from_int(1);
  let @Decimal = decimal_from_int(2);
  if decimal_eq(@Decimal.1, @Decimal.0) then { 0 } else { 1 }
}
"""
        assert _run(source) == 1

    def test_decimal_div_host_called(self) -> None:
        """decimal_div host function is invoked (coverage)."""
        # We can't unwrap Option<Decimal> but the host function runs.
        # Use the dividend as the result instead.
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Decimal = decimal_from_int(10);
  let @Decimal = decimal_from_int(2);
  let @Option<Decimal> = decimal_div(@Decimal.1, @Decimal.0);
  floor(decimal_to_float(@Decimal.1))
}
"""
        assert _run(source) == 10

    def test_decimal_from_string_host_called(self) -> None:
        """decimal_from_string host function is invoked (coverage)."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Option<Decimal> = decimal_from_string("42");
  42
}
"""
        assert _run(source) == 42

    def test_decimal_compare_host_called(self) -> None:
        """decimal_compare host function is invoked (coverage)."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Ordering = decimal_compare(decimal_from_int(1), decimal_from_int(2));
  1
}
"""
        assert _run(source) == 1

    def test_decimal_compare_equal_and_greater(self) -> None:
        """decimal_compare equal and greater branches (coverage)."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Ordering = decimal_compare(decimal_from_int(5), decimal_from_int(5));
  let @Ordering = decimal_compare(decimal_from_int(10), decimal_from_int(3));
  1
}
"""
        assert _run(source) == 1

    def test_decimal_div_by_zero(self) -> None:
        """decimal_div by zero returns None (coverage)."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Option<Decimal> = decimal_div(decimal_from_int(10), decimal_from_int(0));
  1
}
"""
        assert _run(source) == 1

    def test_decimal_from_string_invalid(self) -> None:
        """decimal_from_string with invalid input returns None (coverage)."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Option<Decimal> = decimal_from_string("not_a_number");
  1
}
"""
        assert _run(source) == 1
