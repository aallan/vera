"""Tests for vera.codegen — WASM code generation.

Test helpers follow the established pattern:
    _compile(source) → CompileResult
    _compile_ok(source) → CompileResult (assert no errors)
    _run(source, fn, args) → int result
    _run_io(source, fn, args) → captured stdout string
    _run_trap(source, fn, args) → assert WASM trap
"""

from __future__ import annotations

import json
import re

import pytest
import wasmtime

from vera.codegen import (
    CompileResult,
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


def _run_refine_trap(
    source: str, fn: str | None = None, args: list[int] | None = None
) -> None:
    """Compile, execute, and assert a *refinement-guard* trap specifically — a
    `$vera.contract_fail` ``RuntimeError`` carrying 'Refinement violation', not
    merely *some* runtime trap (which an unrelated fault — e.g. an
    out-of-bounds index — could also raise).  Use this for refinement
    runtime-guard tests so they prove the guard fired, not just that the
    program trapped for any reason."""
    result = _compile_ok(source)
    with pytest.raises(RuntimeError, match="Refinement violation"):
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
        # "hello" is 5 bytes; GC adds 81920 (16K shadow stack + 64K
        # worklist after #348's quadrupling of the worklist), so
        # heap_ptr should start at 5 + 81920 = 81925.  Match the
        # declaration and its initializer in a single substring so a
        # stale `i32.const 81925` elsewhere in the WAT (e.g. a future
        # constant in $alloc that happens to land on the same value)
        # can't satisfy the assertion on its own.
        assert (
            '(global $heap_ptr (export "heap_ptr") (mut i32) (i32.const 81925))'
            in result.wat
        )

    def test_heap_ptr_zero_without_strings(self) -> None:
        """Without strings, heap starts at GC offset 81920 (16K stack + 64K worklist)."""
        source = """\
private data Flag { On, Off }

public fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{ 42 }
"""
        result = _compile_ok(source)
        # Combined declaration + initializer match (see
        # test_heap_ptr_starts_after_strings for the rationale).
        assert (
            '(global $heap_ptr (export "heap_ptr") (mut i32) (i32.const 81920))'
            in result.wat
        )

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


class TestUserUnitFnInStatementPosition556:
    """#556 — calling a user-defined ``@Unit``-returning function in
    statement position (followed by ``;`` and a separate final
    expression) used to fail WASM validation with ``type mismatch:
    expected a type but nothing on stack``.

    The user-visible bug class was actually closed by #584's fix in
    v0.0.135 (``_is_void_expr`` in ``vera/wasm/context.py`` now
    recognises user-defined ``@Unit`` fns via the ``_fn_ret_types``
    registry).  But the specific repro shape from #556 — a *pure*
    helper (no IO effect) followed by a unit-literal final expression,
    rather than another effectful statement — wasn't pinned by the
    existing conformance test ``ch07_unit_fn_nontail.vera`` (which
    covers IO-effect variants).  This class adds the missing
    coverage so the exact #556 repro can't silently regress.
    """

    def test_pure_unit_helper_then_unit_literal(self) -> None:
        """The exact repro from issue #556: a pure ``@Unit``-returning
        helper called in statement position, followed by a trailing
        ``()`` as the block's final expression.  Both ``check`` and
        ``compile`` must succeed; the resulting WAT must call the
        helper and not emit a stray ``drop``.
        """
        source = """\
private fn pure_helper(@Nat -> @Unit)
  requires(true) ensures(true) effects(pure)
{
  ()
}

public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  pure_helper(1);
  ()
}
"""
        result = _compile_ok(source)
        # The helper must be called.
        assert "call $pure_helper" in result.wat, (
            f"Expected `call $pure_helper` in WAT; got:\n{result.wat}"
        )
        # No stray drop on the Unit-returning call — that's what
        # tripped the validator pre-#584.
        main_func = result.wat.split('(func $main')[1].split('(func ')[0]
        assert "drop" not in main_func, (
            f"Expected no `drop` in `$main` (Unit-returning user fn "
            f"in statement position must not leave a stack value "
            f"that needs dropping).  $main body:\n{main_func}"
        )

    def test_pure_unit_helper_in_where_block(self) -> None:
        """The where-block variant reported in the #556 follow-up
        comment: helper lives in a ``where { ... }`` block, called in
        statement position, followed by a unit-literal.  Same shape,
        same fix.
        """
        source = _IO_PRELUDE + """\
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  helper(1);
  ()
}
where {
  fn helper(@Nat -> @Unit)
    requires(true) ensures(true) effects(<IO>)
  {
    IO.print(nat_to_string(@Nat.0))
  }
}
"""
        # Runs end-to-end — exercises the full pipeline including
        # where-block hoisting, so a regression in either layer
        # (Unit-fn detection or where-block name resolution) is
        # caught.
        assert _run_io(source, fn="main") == "1"


class TestTailCallOptimization517:
    """#517 — WASM `return_call` emission for tail-position calls.

    Pre-fix, every Vera ``call`` site emitted plain WASM ``call``
    regardless of tail-position status, so a tail-recursive function
    pushed one WASM frame per iteration and trapped with "call stack
    exhausted" at ~tens of thousands of frames.  The documented
    "iteration is tail recursion" idiom from `SKILL.md` thus
    silently failed past ~5-10K iterations.

    The fix is a per-fn analyzer (`vera/codegen/tail_position.py`)
    that marks `id(FnCall)` AST nodes in syntactic tail position;
    `_translate_call` emits ``return_call $foo`` instead of
    ``call $foo`` when the call's id is in the marked set AND the
    callee's WASM return type matches the caller's (required for
    WASM `return_call` semantics — the signature must match).

    Initially, allocating functions reverted ``return_call`` →
    ``call`` in a post-process step because `return_call` discards
    the current frame and skips the GC epilogue, leaking shadow-
    stack slots.  #549 replaces that fallback with a GC-aware
    variant: the post-process now PREPENDS
    ``local.get $gc_sp_save; global.set $gc_sp`` before each
    ``return_call``, restoring the shadow-stack pointer to the
    caller's entry baseline so the callee's prologue saves a clean
    new baseline.  Args are already on the WASM operand stack at
    the return_call site; the restore only touches the
    ``$gc_sp`` global, so args transfer atomically to the callee.

    Functions with a non-trivial runtime postcondition STILL revert
    ``return_call`` → ``call`` (the postcondition check runs after
    the call returns; ``return_call`` would skip it).
    """

    def test_tail_recursive_iteration_succeeds_at_50k(self) -> None:
        """The canonical 50K-iteration loop runs to completion."""
        source = """\
private fn count_down(@Nat -> @Nat)
  requires(true) ensures(true) decreases(@Nat.0) effects(pure)
{
  if @Nat.0 == 0 then { 0 } else { count_down(@Nat.0 - 1) }
}

public fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  nat_to_int(count_down(50000))
}
"""
        # Pre-fix this trapped at ~30K iterations on the WASM stack.
        # Post-fix, return_call keeps the stack flat and the function
        # returns 0 cleanly.
        assert _run(source, fn="f") == 0

    def test_tail_recursive_iteration_succeeds_at_1m(self) -> None:
        """Stress test: 1M iterations also runs to completion.

        The pre-fix bug was at ~30K WASM frames (default wasmtime
        stack size).  Post-fix, the only constraint is wall-clock
        time — 1M iterations of a single arithmetic op completes in
        well under a second.  This test exists to pin "iteration in
        constant stack space" rather than just "iteration deeper
        than the broken limit", so a future regression that
        reintroduced linear stack growth would fail here even if it
        happened to push the limit higher than 50K.
        """
        source = """\
private fn count_down(@Nat -> @Nat)
  requires(true) ensures(true) decreases(@Nat.0) effects(pure)
{
  if @Nat.0 == 0 then { 0 } else { count_down(@Nat.0 - 1) }
}

public fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  nat_to_int(count_down(1000000))
}
"""
        assert _run(source, fn="f") == 0

    def test_return_call_emitted_for_tail_position_call(self) -> None:
        """Structural: tail-recursive call site emits `return_call`."""
        source = """\
private fn count_down(@Nat -> @Nat)
  requires(true) ensures(true) decreases(@Nat.0) effects(pure)
{
  if @Nat.0 == 0 then { 0 } else { count_down(@Nat.0 - 1) }
}

public fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  nat_to_int(count_down(10))
}
"""
        result = _compile_ok(source)
        # The recursive call inside the else branch is in tail
        # position (it's the trailing expression of the else-block,
        # which is the trailing expression of the if, which is the
        # trailing expression of the function body).  The non-
        # tail call to nat_to_int below is also in tail position
        # in `f`, but nat_to_int is a host-translator builtin
        # without a WAT $-prefixed name, so it doesn't get the
        # return_call treatment.  count_down's recursive call
        # does — assert at least one return_call emission.
        assert "return_call $count_down" in result.wat, (
            f"Expected return_call $count_down in WAT.  WAT excerpt:\n"
            f"{result.wat[:2000]}"
        )

    def test_no_return_call_for_non_tail_position(self) -> None:
        """Structural: a call bound by `let` is NOT in tail position.

        Sibling regression to the `return_call` emission test
        above.  The analyzer must NOT mark calls in non-tail
        positions; otherwise WASM `return_call` would discard the
        caller's frame and the let-binding would lose access to
        the result it needs to bind.
        """
        source = """\
private fn count_down(@Nat -> @Nat)
  requires(true) ensures(true) decreases(@Nat.0) effects(pure)
{
  if @Nat.0 == 0 then { 0 } else { count_down(@Nat.0 - 1) }
}

public fn caller(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Nat = count_down(10);
  @Nat.0 + 1
}
"""
        result = _compile_ok(source)
        # In `caller`, the call to `count_down(10)` is the value of
        # a let binding — NOT tail position.  The trailing
        # `@Nat.0 + 1` consumes the bound value.  Assert that the
        # WAT contains a plain `call $count_down` from `caller`
        # AND a `return_call $count_down` from the recursive call
        # inside count_down's else-branch.  Both must coexist.
        assert "call $count_down" in result.wat
        # Look for the let-bound call: it should be plain `call`,
        # not `return_call`.  Find the function body of `caller`
        # and inspect.
        f_body_start = result.wat.find("(func $caller")
        assert f_body_start >= 0, "caller function not found in WAT"
        f_body_end = result.wat.find("(func ", f_body_start + 1)
        if f_body_end < 0:
            f_body_end = len(result.wat)
        caller_body = result.wat[f_body_start:f_body_end]
        # Inside caller's body, the count_down call must be plain
        # `call`, never `return_call`.  Pre-fix safety: a buggy
        # analyzer that marked non-tail calls would emit
        # `return_call $count_down` here and the let-binding
        # would lose its value.
        assert "return_call $count_down" not in caller_body, (
            f"caller's count_down call should NOT be return_call "
            f"(it's bound by `let`, NOT tail position).  Body:\n"
            f"{caller_body}"
        )
        # Positive sibling assertion — `count_down`'s recursive call
        # IS in tail position (the trailing expression of the
        # else-branch, transitively the trailing expression of the
        # function body via `if`-transparency), so the optimization
        # must fire there even though it doesn't fire in `caller`.
        # Without this check, a buggy analyzer that marked NOTHING
        # would silently pass `assert "return_call $count_down" not
        # in caller_body` while regressing the actual TCO behaviour.
        cd_body_start = result.wat.find("(func $count_down")
        assert cd_body_start >= 0, "count_down function not found"
        cd_body_end = result.wat.find("(func ", cd_body_start + 1)
        if cd_body_end < 0:
            cd_body_end = len(result.wat)
        count_down_body = result.wat[cd_body_start:cd_body_end]
        assert "return_call $count_down" in count_down_body, (
            f"count_down's recursive call should be return_call "
            f"(tail position via if-else transparency).  Body:\n"
            f"{count_down_body}"
        )

    def test_postcondition_function_falls_back_to_plain_call(self) -> None:
        """A function with a non-trivial `ensures` reverts return_call.

        Postcondition checks emit instructions AFTER the function
        body in the WAT assembly (`local.set $ret`, condition
        check, trap on failure, `local.get $ret` to push back).
        WASM `return_call` discards the current frame and skips
        all of those — silently violating the contract.

        The fallback in `_compile_fn` reverts every `return_call`
        → `call` when `post_instrs` is non-empty (CodeRabbit
        finding on PR #550 round 2).  Pre-fix this would have
        shipped as a soundness hole: a tail-recursive function
        with a runtime postcondition would skip the postcondition
        check on every iteration and the contract would silently
        fail.  Trivial postconditions like `ensures(true)` are
        elided by `_compile_postconditions` and don't trigger the
        fallback (no instructions are emitted, so nothing is
        skipped).
        """
        # A function with a non-trivial postcondition.  The
        # ensures clause (`@Nat.result >= 0`) is trivially true
        # for `@Nat` (refinement-typed non-negative), but the
        # codegen treats any non-`true` ensures as non-trivial
        # and emits the runtime check.
        source = """\
private fn count_down(@Nat -> @Nat)
  requires(true)
  ensures(@Nat.result >= 0)
  decreases(@Nat.0)
  effects(pure)
{
  if @Nat.0 == 0 then { 0 } else { count_down(@Nat.0 - 1) }
}

public fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  nat_to_int(count_down(10))
}
"""
        result = _compile_ok(source)
        cd_body_start = result.wat.find("(func $count_down")
        assert cd_body_start >= 0
        cd_body_end = result.wat.find("(func ", cd_body_start + 1)
        if cd_body_end < 0:
            cd_body_end = len(result.wat)
        count_down_body = result.wat[cd_body_start:cd_body_end]
        # The recursive call is in syntactic tail position, so the
        # analyzer MARKS it.  But the postcondition check needs to
        # run after every recursive call's return — `return_call`
        # would skip it.  Post-process must have reverted the
        # emission to plain `call`.
        assert "call $count_down" in count_down_body
        assert "return_call $count_down" not in count_down_body, (
            f"count_down has a non-trivial postcondition (ensures "
            f"@Nat.result >= 0); return_call would skip the runtime "
            f"check.  Post-process should have reverted to plain "
            f"call.  Body:\n{count_down_body}"
        )

    def test_allocating_function_uses_gc_aware_tco_549(self) -> None:
        """#549: allocating fns emit `return_call` + $gc_sp restore.

        WASM `return_call` discards the current frame, which means
        the GC epilogue (restore `$gc_sp`, unwind shadow stack)
        never runs.  For an allocating function with tail calls,
        that would leak shadow-stack slots once per iteration and
        trap on the next `$alloc` once gc_sp passes the worklist
        boundary.

        Pre-#549: the post-process reverted every `return_call` →
        `call` when `ctx.needs_alloc` was True, sacrificing WASM
        call-stack depth (tail recursion eventually trapped with
        `call stack exhausted`) so the GC epilogue could run and
        bound shadow-stack usage.

        Post-#549: the post-process instead PREPENDS a `$gc_sp`
        restore (`local.get $gc_sp_save; global.set $gc_sp`)
        immediately before each `return_call`, so the callee's
        prologue saves a clean new baseline and the shadow stack
        stays bounded across iterations.  Args are already on the
        WASM operand stack at the return_call site; the restore
        only touches the `$gc_sp` global, so args transfer
        atomically to the callee.

        This test pins the new contract: an allocating function
        with a tail call must emit `return_call $foo` PRECEDED by
        the `$gc_sp` restore sequence.
        """
        # Function that allocates (constructor call) AND has a
        # tail-recursive call shape.  The analyzer marks the
        # recursive call as tail-position; the post-process
        # patches the emission because needs_alloc is True.
        source = """\
private data Box { MkBox(Int) }

private fn build(@Int -> @Box)
  requires(true) ensures(true) decreases(@Int.0) effects(pure)
{
  if @Int.0 == 0 then { MkBox(0) } else { build(@Int.0 - 1) }
}

public fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  match build(3) { MkBox(@Int) -> @Int.0 }
}
"""
        result = _compile_ok(source)
        # build allocates (the MkBox constructor) AND has a tail-
        # recursive call.  Post-process must have KEPT the
        # `return_call $build` (TCO preserved) but prepended the
        # $gc_sp restore (shadow-stack invariant preserved).
        #
        # Use boundary-safe regex (\b after `$build`) so a future
        # symbol like `$build_helper` couldn't false-match these
        # checks.  WAT symbol chars are `[A-Za-z0-9_]` plus `$`;
        # `\b` correctly excludes `$build_x` while still matching
        # `$build ` or `$build(`.
        build_match = re.search(r"\(func \$build\b", result.wat)
        assert build_match is not None, (
            "Could not locate `(func $build` in WAT"
        )
        build_start = build_match.start()
        next_fn = re.search(r"\(func \$", result.wat[build_start + 1:])
        build_end = (
            build_start + 1 + next_fn.start()
            if next_fn is not None
            else len(result.wat)
        )
        build_body = result.wat[build_start:build_end]
        assert re.search(r"return_call \$build\b", build_body), (
            f"Allocating function `build` did not emit return_call. "
            f"#549's GC-aware TCO should preserve return_call for "
            f"allocating fns. Body:\n{build_body}"
        )
        # Parse the GC prologue to capture the exact local index
        # that holds $gc_sp_save.  The prologue is the two
        # instructions that open every allocating function:
        #     global.get $gc_sp
        #     local.set <N>
        # The preamble at each return_call site must reload from
        # this SAME local — anything else (a typo, a wrong index
        # picked up from an unrelated local-alloc) would leave the
        # callee's prologue saving an inconsistent baseline.
        lines = build_body.splitlines()
        prologue_get_idx = next(
            (i for i, ln in enumerate(lines)
             if ln.strip() == "global.get $gc_sp"),
            None,
        )
        assert prologue_get_idx is not None, (
            f"no `global.get $gc_sp` prologue found in build body. "
            f"Body:\n{build_body}"
        )
        prologue_set = lines[prologue_get_idx + 1].strip()
        assert prologue_set.startswith("local.set "), (
            f"expected `local.set <N>` immediately after the "
            f"prologue's `global.get $gc_sp`, got: {prologue_set!r}. "
            f"Body:\n{build_body}"
        )
        gc_sp_save_local = prologue_set[len("local.set "):]
        expected_preamble_get = f"local.get {gc_sp_save_local}"
        # Find every `return_call $build` site and verify the two
        # instructions immediately before it are the exact preamble:
        #     local.get <gc_sp_save_local>
        #     global.set $gc_sp
        return_call_indices = [
            i for i, line in enumerate(lines)
            if re.search(r"return_call \$build\b", line)
        ]
        assert return_call_indices, "no return_call $build site found"
        for idx in return_call_indices:
            assert idx >= 2, (
                f"return_call at line {idx} has no room for the "
                f"$gc_sp restore preamble. Body:\n{build_body}"
            )
            prev1 = lines[idx - 1].strip()
            prev2 = lines[idx - 2].strip()
            assert prev1 == "global.set $gc_sp", (
                f"Expected 'global.set $gc_sp' immediately before "
                f"return_call at line {idx}, got: {prev1!r}. "
                f"Body:\n{build_body}"
            )
            assert prev2 == expected_preamble_get, (
                f"Expected exact preamble '{expected_preamble_get}' "
                f"(matching the GC prologue's saved local) two lines "
                f"before return_call at line {idx}, got: {prev2!r}. "
                f"Body:\n{build_body}"
            )

    def test_allocating_function_gc_aware_tco_patches_both_branches(
        self,
    ) -> None:
        """#549: every tail-position `return_call` gets the preamble.

        The single-branch test above pins that the patch fires at
        a single tail-recursive call site.  This test pins that
        the patch loop fires at MULTIPLE sites in the same
        function — a buggy implementation that bails after the
        first match (e.g. `break` inside the patch loop) or that
        only handles top-level emissions but not if/else-nested
        ones would still pass the single-branch test.

        The function below uses a `match` with two ADT arms, each
        ending in a tail-recursive `build` call.  The analyzer
        marks both arms as tail position (see
        `test_analyzer_marks_match_arm_bodies`), so the codegen
        emits two `return_call $build` sites with DIFFERENT
        leading-whitespace prefixes (one for each match arm).
        Both must have the `local.get N; global.set $gc_sp`
        preamble; the local index N must be the same one captured
        by the GC prologue.
        """
        source = """\
private data Choice { Left, Right }

private fn build(@Int, @Choice -> @Array<Int>)
  requires(@Int.0 >= 0) ensures(true) decreases(@Int.0) effects(pure)
{
  if @Int.0 == 0 then { [0] }
  else {
    match @Choice.0 {
      Left -> build(@Int.0 - 1, Left),
      Right -> build(@Int.0 - 1, Right)
    }
  }
}

public fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  array_length(build(3, Left))
}
"""
        result = _compile_ok(source)
        build_match = re.search(r"\(func \$build\b", result.wat)
        assert build_match is not None, (
            "Could not locate `(func $build` in WAT"
        )
        build_start = build_match.start()
        next_fn = re.search(r"\(func \$", result.wat[build_start + 1:])
        build_end = (
            build_start + 1 + next_fn.start()
            if next_fn is not None
            else len(result.wat)
        )
        build_body = result.wat[build_start:build_end]
        # Capture the exact $gc_sp_save local from the prologue.
        lines = build_body.splitlines()
        prologue_get_idx = next(
            (i for i, ln in enumerate(lines)
             if ln.strip() == "global.get $gc_sp"),
            None,
        )
        assert prologue_get_idx is not None, (
            f"no `global.get $gc_sp` prologue.  Body:\n{build_body}"
        )
        prologue_set = lines[prologue_get_idx + 1].strip()
        assert prologue_set.startswith("local.set ")
        gc_sp_save_local = prologue_set[len("local.set "):]
        expected_preamble_get = f"local.get {gc_sp_save_local}"
        # Find every return_call site and require the same
        # preamble at each.  This catches a regression where the
        # patch only fires on the first site (e.g. accidental
        # `break`) or where only a subset of nested positions get
        # the restore.
        return_call_indices = [
            i for i, line in enumerate(lines)
            if re.search(r"return_call \$build\b", line)
        ]
        assert len(return_call_indices) >= 2, (
            f"Expected at least 2 return_call sites (one per "
            f"match arm), got {len(return_call_indices)}.  "
            f"Body:\n{build_body}"
        )
        for idx in return_call_indices:
            assert idx >= 2, (
                f"return_call at line {idx} has no room for "
                f"preamble.  Body:\n{build_body}"
            )
            prev1 = lines[idx - 1].strip()
            prev2 = lines[idx - 2].strip()
            assert prev1 == "global.set $gc_sp", (
                f"site {idx} missing `global.set $gc_sp`; got "
                f"{prev1!r}.  Body:\n{build_body}"
            )
            assert prev2 == expected_preamble_get, (
                f"site {idx} preamble mismatch: expected "
                f"{expected_preamble_get!r}, got {prev2!r}.  "
                f"Both return_call sites must reload the SAME "
                f"local that the prologue saved.  Body:\n"
                f"{build_body}"
            )

    def test_allocating_function_with_postcondition_still_reverts(
        self,
    ) -> None:
        """Postcondition-bearing allocating fns still revert to call.

        The GC-aware TCO patch from #549 covers the
        ``needs_alloc and not post_instrs`` case.  When the
        function carries a non-trivial runtime postcondition
        check, the post-process still reverts ``return_call`` →
        ``call`` because the postcondition check needs to run
        after the call returns — ``return_call`` would skip it.

        This pins the precedence: post_instrs revert takes priority
        over the GC-aware patch.  The function below both allocates
        (the array literal in the base case sets needs_alloc) AND
        carries a runtime postcondition (`@Int.result >= 0`).  The
        post-process must therefore revert to plain ``call``, even
        though #549's path would otherwise patch in a GC restore.
        """
        source = """\
private fn build(@Nat -> @Int)
  requires(true)
  ensures(@Int.result >= 0)
  decreases(@Nat.0)
  effects(pure)
{
  -- Base case allocates an array literal (sets needs_alloc on
  -- the codegen context); recursive case is in tail position.
  if @Nat.0 == 0 then { array_length([0, 0, 0]) }
  else { build(@Nat.0 - 1) }
}

public fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  build(3)
}
"""
        result = _compile_ok(source)
        # Boundary-safe extraction (\b after `$build`) — see the
        # rationale in test_allocating_function_uses_gc_aware_tco_549
        # above.
        build_match = re.search(r"\(func \$build\b", result.wat)
        assert build_match is not None, (
            "Could not locate `(func $build` in WAT"
        )
        build_start = build_match.start()
        next_fn = re.search(r"\(func \$", result.wat[build_start + 1:])
        build_end = (
            build_start + 1 + next_fn.start()
            if next_fn is not None
            else len(result.wat)
        )
        build_body = result.wat[build_start:build_end]
        # post_instrs are present, so return_call must revert to
        # plain call (so the postcondition check actually runs).
        # `\bcall \$build\b` rules out both `return_call` (leading
        # `\b` requires non-word char before `c`) AND `$build_x`
        # (trailing `\b` requires non-word char after `d`).
        assert re.search(r"\bcall \$build\b", build_body), (
            f"Expected plain `call $build` in post-revert body. "
            f"Body:\n{build_body}"
        )
        assert not re.search(r"return_call \$build\b", build_body), (
            f"build has a runtime postcondition; return_call would "
            f"skip it. Post-process should have reverted to plain "
            f"call. Body:\n{build_body}"
        )
        # Tighten: the GC-restore preamble (`local.get <N>;
        # global.set $gc_sp`) must NOT precede the reverted
        # `call $build`.  The preamble belongs to #549's GC-aware
        # TCO path; once we've taken the postcondition-revert path
        # the preamble has no purpose (we're keeping the frame, not
        # discarding it via return_call), and injecting it anyway
        # would corrupt the shadow-stack invariant for the
        # remainder of the function.  This pins the dispatch
        # precedence: post_instrs revert > GC-aware patch (the
        # branches are mutually exclusive, not additive).
        #
        # Note: `local.get ...; global.set $gc_sp` legitimately
        # appears in the GC EPILOGUE at the end of every allocating
        # function (it restores $gc_sp before returning).  We can't
        # forbid the sequence outright; we can only forbid it
        # immediately preceding a `call $build` site.
        lines = build_body.splitlines()
        # Boundary-safe regex distinguishes plain `call $build`
        # from `return_call $build` AND excludes `$build_anything`.
        call_indices = [
            i for i, line in enumerate(lines)
            if re.search(r"\bcall \$build\b", line)
        ]
        assert call_indices, "no plain call $build site found"
        for idx in call_indices:
            if idx < 2:
                continue
            prev1 = lines[idx - 1].strip()
            prev2 = lines[idx - 2].strip()
            assert not (
                prev1 == "global.set $gc_sp"
                and prev2.startswith("local.get ")
            ), (
                f"Postcondition-revert path mistakenly injected the "
                f"#549 GC-restore preamble before `call $build` at "
                f"line {idx}.  Preamble lines: {prev2!r}, {prev1!r}. "
                f"Dispatch precedence violated: post_instrs revert "
                f"and GC-aware patch should be mutually exclusive. "
                f"Body:\n{build_body}"
            )

    def test_analyzer_marks_block_trailing_expression(self) -> None:
        """Unit test: analyzer marks Block.expr as tail position."""
        from vera.codegen.tail_position import compute_tail_call_sites
        from vera.parser import parse_to_ast
        program = parse_to_ast("""\
public fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  f()
}
""")
        decl = program.declarations[0].decl
        sites = compute_tail_call_sites(decl)
        # The single FnCall in the body is the trailing expression
        # of the block — analyzer marks it.
        assert len(sites) == 1

    def test_analyzer_marks_both_branches_of_tail_if(self) -> None:
        """Unit test: both then/else branches of a tail-position if."""
        from vera.codegen.tail_position import compute_tail_call_sites
        from vera.parser import parse_to_ast
        program = parse_to_ast("""\
public fn f(@Bool -> @Int)
  requires(true) ensures(true) effects(pure)
{
  if @Bool.0 then { f(false) } else { f(true) }
}
""")
        decl = program.declarations[0].decl
        sites = compute_tail_call_sites(decl)
        # Two FnCalls (one per branch) — both should be marked.
        assert len(sites) == 2

    def test_analyzer_marks_match_arm_bodies(self) -> None:
        """Unit test: every arm body of a tail-position match is tail position.

        ``MatchExpr`` is tail-transparent in the same way ``IfExpr``
        is — if the match expression itself is in tail position
        (i.e. it's the trailing expression of the function body),
        every arm body is in tail position.  The scrutinee is NOT,
        and call arguments inside an arm body are NOT — those are
        non-transparent in the same way.

        Pre-this-test, MatchExpr handling in the analyzer
        (``visit_tail`` in ``vera/codegen/tail_position.py``)
        existed but had no explicit test pinning the behaviour;
        a regression that dropped or mis-handled the MatchExpr
        case would have slipped past CI silently.  This test
        constructs a function whose body is a match with two arms
        — one arm wraps its tail call around a non-tail argument
        call — and asserts the analyzer marks the two arm bodies
        but NOT the inner argument call.
        """
        from vera import ast
        from vera.codegen.tail_position import compute_tail_call_sites
        from vera.parser import parse_to_ast
        program = parse_to_ast("""\
private fn arg_producer(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ 42 }

private fn arm_handler(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 }

public fn f(@Option<Int> -> @Int)
  requires(true) ensures(true) effects(pure)
{
  match @Option<Int>.0 {
    None -> arm_handler(arg_producer(())),
    Some(@Int) -> arm_handler(@Int.0)
  }
}
""")
        f_decl = program.declarations[2].decl
        sites = compute_tail_call_sites(f_decl)

        # Locate the specific call ids by walking the AST so the
        # assertion below pins WHICH calls got marked, not just how
        # many — same exhaustiveness pattern as
        # ``test_analyzer_does_not_mark_call_args``.  Body shape:
        #
        #   Block(statements=[], expr=MatchExpr(
        #     scrutinee=SlotRef,
        #     arms=[
        #       Arm(pattern=None, body=FnCall("arm_handler",
        #             [FnCall("arg_producer", [UnitLit])])),
        #       Arm(pattern=Some(@Int), body=FnCall("arm_handler",
        #             [SlotRef])),
        #     ]))
        match_expr = f_decl.body.expr
        assert isinstance(match_expr, ast.MatchExpr)
        assert len(match_expr.arms) == 2

        none_arm_call = match_expr.arms[0].body
        some_arm_call = match_expr.arms[1].body
        assert isinstance(none_arm_call, ast.FnCall)
        assert isinstance(some_arm_call, ast.FnCall)
        assert none_arm_call.name == "arm_handler"
        assert some_arm_call.name == "arm_handler"

        nested_arg_call = none_arm_call.args[0]
        assert isinstance(nested_arg_call, ast.FnCall)
        assert nested_arg_call.name == "arg_producer"

        # Both arm bodies (the outer ``arm_handler(...)`` calls)
        # are in tail position via match-transparency.  The nested
        # ``arg_producer(())`` call inside the None arm is an
        # argument — non-transparent, NOT tail.  An exhaustive
        # ``sites == {...}`` check pins both the inclusion AND the
        # exclusion in one assertion.
        assert id(none_arm_call) in sites, (
            f"None-arm body call should be tail position; "
            f"sites={sites!r}, expected id={id(none_arm_call)}"
        )
        assert id(some_arm_call) in sites, (
            f"Some-arm body call should be tail position; "
            f"sites={sites!r}, expected id={id(some_arm_call)}"
        )
        assert id(nested_arg_call) not in sites, (
            f"Nested argument call inside None arm should NOT be "
            f"tail position; sites={sites!r}, "
            f"unexpected id={id(nested_arg_call)}"
        )
        assert sites == {id(none_arm_call), id(some_arm_call)}, (
            f"Expected exactly the two arm-body calls in sites; "
            f"got {sites!r}"
        )

    def test_analyzer_does_not_mark_let_value_calls(self) -> None:
        """Unit test: a call as a let value is NOT tail position."""
        from vera.codegen.tail_position import compute_tail_call_sites
        from vera.parser import parse_to_ast
        program = parse_to_ast("""\
private fn helper(-> @Int)
  requires(true) ensures(true) effects(pure)
{ 42 }

public fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Int = helper();
  @Int.0 + 1
}
""")
        f_decl = program.declarations[1].decl
        sites = compute_tail_call_sites(f_decl)
        # The let value is NOT tail; the trailing `@Int.0 + 1` is
        # an addition (BinaryExpr), not a call.  No FnCalls in tail
        # position.
        assert sites == set()

    def test_analyzer_does_not_mark_call_args(self) -> None:
        """Unit test: args to a tail-position call are NOT themselves tail."""
        from vera.codegen.tail_position import compute_tail_call_sites
        from vera.parser import parse_to_ast
        program = parse_to_ast("""\
private fn inner(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 }

private fn arg_producer(-> @Int)
  requires(true) ensures(true) effects(pure)
{ 42 }

public fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  inner(arg_producer())
}
""")
        from vera import ast
        f_decl = program.declarations[2].decl
        sites = compute_tail_call_sites(f_decl)

        # Locate the two call ids explicitly so the assertion below
        # checks WHICH call got marked, not just how many.  The
        # body is `Block(statements=[], expr=FnCall("inner", [FnCall("arg_producer", [])]))`
        # so the outer call is `f_decl.body.expr`, and the inner
        # arg-producer call is its first argument.
        outer_call = f_decl.body.expr
        assert isinstance(outer_call, ast.FnCall)
        assert outer_call.name == "inner"
        inner_arg_call = outer_call.args[0]
        assert isinstance(inner_arg_call, ast.FnCall)
        assert inner_arg_call.name == "arg_producer"

        # The outer call IS in tail position (trailing expression of
        # the function body).  The argument call is NOT — its result
        # is consumed by `inner`'s parameter binding.  A buggy
        # analyzer that marked argument calls would emit
        # `return_call $arg_producer` and the discarded frame would
        # mean `inner` never receives its argument.
        assert id(outer_call) in sites, (
            f"Outer call `inner(...)` should be marked tail position; "
            f"sites={sites!r}, outer call id={id(outer_call)}"
        )
        assert id(inner_arg_call) not in sites, (
            f"Argument call `arg_producer()` should NOT be marked "
            f"tail position; sites={sites!r}, "
            f"arg call id={id(inner_arg_call)}"
        )
        # And nothing else either — both ids accounted for.
        assert sites == {id(outer_call)}

    def test_analyzer_does_not_mark_call_in_block_statement(self) -> None:
        """Unit test: a call inside a Block statement is NOT tail position.

        ``Block`` is tail-transparent for its trailing expression
        ONLY — calls inside ``LetStmt.value`` / ``ExprStmt.expr`` /
        ``LetDestruct.value`` are NOT in tail position, even when
        the block itself is.  The analyzer's Block handler only
        recurses into ``block.expr``; statements are skipped.

        This test pins the ExprStmt case specifically (the
        ``LetStmt.value`` case is covered by
        ``test_analyzer_does_not_mark_let_value_calls``).  A
        regression that started visiting statements would mark the
        side-effect call below in tail position, which would mean
        WASM ``return_call`` discards the current frame and the
        block's trailing expression (``42``) never executes.
        """
        from vera import ast
        from vera.codegen.tail_position import compute_tail_call_sites
        from vera.parser import parse_to_ast
        program = parse_to_ast("""\
private fn side_effect(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ 0 }

public fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  side_effect(());
  42
}
""")
        f_decl = program.declarations[1].decl
        sites = compute_tail_call_sites(f_decl)

        # The block has one ExprStmt (the side_effect call) and a
        # trailing IntLit.  Locate the ExprStmt's call to assert it
        # is NOT marked.  AST shape:
        #
        #   Block(statements=[ExprStmt(expr=FnCall("side_effect", [UnitLit]))],
        #         expr=IntLit(42))
        block = f_decl.body
        assert isinstance(block, ast.Block)
        assert len(block.statements) == 1
        side_effect_stmt = block.statements[0]
        assert isinstance(side_effect_stmt, ast.ExprStmt)
        side_effect_call = side_effect_stmt.expr
        assert isinstance(side_effect_call, ast.FnCall)
        assert side_effect_call.name == "side_effect"

        # Trailing expression is IntLit(42), not a call — so the
        # analyzer should mark NOTHING.  The ExprStmt's call must
        # NOT be in sites (it's a statement, not the trailing
        # expression).
        assert id(side_effect_call) not in sites, (
            f"ExprStmt-position call should NOT be tail position; "
            f"sites={sites!r}, unexpected id={id(side_effect_call)}"
        )
        assert sites == set(), (
            f"Expected empty sites (only statement call, no tail "
            f"calls); got {sites!r}"
        )

    def test_analyzer_does_not_mark_call_in_if_condition(self) -> None:
        """Unit test: a call inside an IfExpr condition is NOT tail position.

        ``IfExpr`` is tail-transparent for its branches only —
        the condition is evaluated first, its result is consumed
        by the if-dispatch, and only THEN one of the branches
        runs.  A call in the condition is therefore non-tail.
        The analyzer's IfExpr handler only recurses into
        ``then_branch`` and ``else_branch``; the condition is
        skipped.
        """
        from vera import ast
        from vera.codegen.tail_position import compute_tail_call_sites
        from vera.parser import parse_to_ast
        program = parse_to_ast("""\
private fn predicate(@Unit -> @Bool)
  requires(true) ensures(true) effects(pure)
{ true }

public fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  if predicate(()) then { 1 } else { 2 }
}
""")
        f_decl = program.declarations[1].decl
        sites = compute_tail_call_sites(f_decl)

        # Locate the predicate() call in the if condition.  Body
        # shape: Block(statements=[], expr=IfExpr(condition=FnCall(...),
        # then_branch=Block(...), else_branch=Block(...))).
        if_expr = f_decl.body.expr
        assert isinstance(if_expr, ast.IfExpr)
        cond_call = if_expr.condition
        assert isinstance(cond_call, ast.FnCall)
        assert cond_call.name == "predicate"

        # Both branches return literals (no calls), so the analyzer
        # should mark NOTHING.  The condition call must NOT be in
        # sites — a regression that recursed into the condition with
        # the parent's tail status would mark it and ``return_call``
        # would discard the frame before the if-dispatch ran.
        assert id(cond_call) not in sites, (
            f"IfExpr-condition call should NOT be tail position; "
            f"sites={sites!r}, unexpected id={id(cond_call)}"
        )
        assert sites == set(), (
            f"Expected empty sites (no tail calls — both branches "
            f"are literals); got {sites!r}"
        )

    def test_analyzer_does_not_mark_call_in_match_scrutinee(self) -> None:
        """Unit test: a call inside a MatchExpr scrutinee is NOT tail position.

        ``MatchExpr`` is tail-transparent for its arm bodies only —
        the scrutinee is evaluated first, its result is consumed
        by the match-dispatch (constructor tag check + field
        binding), and only THEN one of the arms runs.  A call in
        the scrutinee is therefore non-tail.  The analyzer's
        MatchExpr handler only recurses into each arm's body;
        the scrutinee is skipped.
        """
        from vera import ast
        from vera.codegen.tail_position import compute_tail_call_sites
        from vera.parser import parse_to_ast
        program = parse_to_ast("""\
private fn make_option(@Unit -> @Option<Int>)
  requires(true) ensures(true) effects(pure)
{ None }

public fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  match make_option(()) {
    None -> 0,
    Some(@Int) -> @Int.0
  }
}
""")
        f_decl = program.declarations[1].decl
        sites = compute_tail_call_sites(f_decl)

        # Locate the make_option() call in the match scrutinee.
        # Body shape: Block(statements=[], expr=MatchExpr(
        #   scrutinee=FnCall(...), arms=[...])).
        match_expr = f_decl.body.expr
        assert isinstance(match_expr, ast.MatchExpr)
        scrutinee_call = match_expr.scrutinee
        assert isinstance(scrutinee_call, ast.FnCall)
        assert scrutinee_call.name == "make_option"

        # Both arms return literals/slot ref (no calls), so the
        # analyzer should mark NOTHING.  The scrutinee call must
        # NOT be in sites — a regression that recursed into the
        # scrutinee with the parent's tail status would mark it
        # and ``return_call`` would discard the frame before the
        # match-dispatch ran (the constructor tag check would have
        # nothing to inspect).
        assert id(scrutinee_call) not in sites, (
            f"MatchExpr-scrutinee call should NOT be tail position; "
            f"sites={sites!r}, unexpected id={id(scrutinee_call)}"
        )
        assert sites == set(), (
            f"Expected empty sites (no tail calls — both arms are "
            f"literals/slot ref); got {sites!r}"
        )


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

    def test_gc_collect_bounds_check_against_heap_ptr(self) -> None:
        """Regression for #515: $gc_collect must bound the conservative
        scan against $heap_ptr.

        The conservative-GC worklist push in Phase 2 accepts a shadow
        stack value as a heap pointer based on three guards (in heap
        range, properly aligned, below $heap_ptr).  None of those
        guards prove the word at val-4 is an actual object header.  A
        non-pointer i32 in payload data (e.g. a bit-packed Nat row in
        Conway-style code) can satisfy all three, in which case the
        marker reads garbage as obj_size and walks $obj_ptr+scan_ptr
        past $heap_ptr, trapping at the linear-memory boundary inside
        $gc_collect itself.

        Two layers of defence are now emitted:
          - Layer 2 (early skip): before marking or scanning, verify
            obj_ptr + obj_size <= heap_ptr.
          - Layer 1 (per-iter): each scan-loop iteration also checks
            obj_ptr + scan_ptr + 4 <= heap_ptr before issuing the
            i32.load.

        This test asserts both bounds checks survive in the emitted
        WAT.  A behavioural reproducer for #515 is heavily layout-
        sensitive (string-pool offsets, allocation order); the
        structural assertion is the durable regression guard.

        The assertions look for the actual opcode pattern that
        implements each bound check, not just the marker comment.
        Otherwise a refactor that left the comment in place but
        deleted the underlying check would silently pass — the
        comment is a discoverability anchor, the opcodes are the
        contract.
        """
        source = """\
private data Box { MkBox(Int) }

public fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  match MkBox(42) { MkBox(@Int) -> @Int.0 }
}
"""
        result = _compile_ok(source)
        wat = result.wat
        assert "func $gc_collect" in wat

        # Helper: extract the next N non-comment, non-blank tokens of
        # WAT after `marker_text`.  Comments start with `;;` (line) or
        # `(;` (block) — only line comments appear in the GC code.
        # Joining tokens with single spaces gives us a normalised
        # pattern that's stable against whitespace changes in the
        # emitter but fails fast if any opcode is missing or out of
        # order.
        def _opcodes_after(text: str, marker: str, n: int) -> str:
            i = text.find(marker)
            assert i >= 0, f"Marker {marker!r} not found in WAT"
            # The marker sits inside a `;;` comment — the rest of its
            # line is comment text, not WAT.  Advance to the start of
            # the line after the marker so we tokenise only emitted
            # opcodes, never comment prose.
            line_end = text.find("\n", i)
            tail = text[line_end + 1:] if line_end >= 0 else ""
            tokens: list[str] = []
            for raw_line in tail.splitlines():
                stripped = raw_line.strip()
                if not stripped or stripped.startswith(";;"):
                    continue
                # Strip trailing inline comments if any (defensive).
                code = stripped.split(";;", 1)[0].strip()
                if not code:
                    continue
                tokens.extend(code.split())
                if len(tokens) >= n:
                    break
            return " ".join(tokens[:n])

        # Layer 2: the bound-check pattern is —
        #   local.get $obj_ptr ; local.get $obj_size ; i32.add ;
        #   global.get $heap_ptr ; i32.gt_u ; if ; br $m_loop
        # which is 11 whitespace-split tokens (each `local.get $foo`
        # splits into two: opcode + identifier).
        layer2_expected = (
            "local.get $obj_ptr local.get $obj_size i32.add "
            "global.get $heap_ptr i32.gt_u if br $m_loop"
        )
        layer2 = _opcodes_after(
            wat, "Layer 2 (issue #515)", len(layer2_expected.split()),
        )
        assert layer2 == layer2_expected, (
            f"Layer 2 opcode pattern drifted: {layer2!r}"
        )

        # Layer 1: the per-iter check pattern is —
        #   local.get $obj_ptr ; local.get $scan_ptr ; i32.add ;
        #   i32.const 4 ; i32.add ; global.get $heap_ptr ;
        #   i32.gt_u ; br_if $sc_done
        # which is 13 whitespace-split tokens.  The `br_if` (no `if`
        # block) is the cheap variant — exits the surrounding
        # `block $sc_done` directly without an if/end pair.
        layer1_expected = (
            "local.get $obj_ptr local.get $scan_ptr i32.add "
            "i32.const 4 i32.add global.get $heap_ptr "
            "i32.gt_u br_if $sc_done"
        )
        layer1 = _opcodes_after(
            wat, "Layer 1 (issue #515)", len(layer1_expected.split()),
        )
        assert layer1 == layer1_expected, (
            f"Layer 1 opcode pattern drifted: {layer1!r}"
        )


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
        assert '(import "vera" "state_get_Int"' in result.wat
        assert '(import "vera" "state_put_Int"' in result.wat
        assert '(import "vera" "state_push_Int"' in result.wat
        assert '(import "vera" "state_pop_Int"' in result.wat

    def test_nested_same_type_state_handlers(self) -> None:
        """Nested handle[State<Int>] of the same type have independent cells (#417)."""
        src = """\
public fn test(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  handle[State<Int>](@Int = 10) {
    get(@Unit) -> { resume(@Int.0) },
    put(@Int) -> { resume(()) }
  } in {
    put(99);
    handle[State<Int>](@Int = 1) {
      get(@Unit) -> { resume(@Int.0) },
      put(@Int) -> { resume(()) }
    } in {
      put(2);
      ()
    };
    get(())
  }
}
"""
        assert _run(src, "test") == 99

    def test_nested_state_inner_does_not_corrupt_outer(self) -> None:
        """Inner handler put does not affect outer handler state (#417)."""
        src = """\
public fn test(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  handle[State<Int>](@Int = 5) {
    get(@Unit) -> { resume(@Int.0) },
    put(@Int) -> { resume(()) }
  } in {
    handle[State<Int>](@Int = 100) {
      get(@Unit) -> { resume(@Int.0) },
      put(@Int) -> { resume(()) }
    } in {
      put(999);
      ()
    };
    get(())
  }
}
"""
        assert _run(src, "test") == 5

    def test_nested_state_outer_readable_after_inner(self) -> None:
        """After inner handler exits, outer handler value is restored (#417).

        The inner handler returns an Int (not Unit) so state_pop_Int is called
        with a live WASM value on the stack — verifying it is truly stack-neutral.
        The outer block captures the inner result via let, then reads outer state.
        """
        src = """\
public fn test(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  handle[State<Int>](@Int = 42) {
    get(@Unit) -> { resume(@Int.0) },
    put(@Int) -> { resume(()) }
  } in {
    let @Int = handle[State<Int>](@Int = 0) {
      get(@Unit) -> { resume(@Int.0) },
      put(@Int) -> { resume(()) }
    } in {
      put(7);
      get(())
    };
    get(())
  }
}
"""
        assert _run(src, "test") == 42

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

    def test_exn_qualified_throw_caught(self) -> None:
        """Exn.throw (qualified form) compiles and runs identically to bare throw."""
        src = """\
effect Exn<E> {
  op throw(E -> Never);
}
private fn require_non_negative(@Int -> @Int)
  requires(true) ensures(@Int.result >= 0) effects(<Exn<Int>>)
{
  if @Int.0 < 0 then { Exn.throw(@Int.0) } else { @Int.0 }
}
public fn test(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  handle[Exn<Int>] {
    throw(@Int) -> 0
  } in {
    require_non_negative(0 - 3)
  }
}
"""
        assert _run(src, fn="test") == 0

    def test_exn_qualified_throw_no_throw(self) -> None:
        """Exn.throw (qualified form) — non-throwing path returns correct value."""
        src = """\
effect Exn<E> {
  op throw(E -> Never);
}
private fn require_non_negative(@Int -> @Int)
  requires(true) ensures(@Int.result >= 0) effects(<Exn<Int>>)
{
  if @Int.0 < 0 then { Exn.throw(@Int.0) } else { @Int.0 }
}
public fn test(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  handle[Exn<Int>] {
    throw(@Int) -> 0
  } in {
    require_non_negative(5)
  }
}
"""
        assert _run(src, fn="test") == 5

    def test_state_qualified_get_put(self) -> None:
        """State.get / State.put (qualified forms) compile and run correctly."""
        src = """\
public fn test(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  handle[State<Int>](@Int = 0) {
    get(@Unit) -> { resume(@Int.0) },
    put(@Int)  -> { resume(()) }
  } in {
    State.put(State.get(()) + 1);
    State.put(State.get(()) + 1);
    State.get(())
  }
}
"""
        assert _run(src, fn="test") == 2

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

    def test_exn_string_throw_caught(self) -> None:
        """Exn<String> throw+catch: pair type (ptr, len) uses (param i32 i32) tag."""
        src = """\
effect Exn<E> {
  op throw(E -> Never);
}
public fn test(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  handle[Exn<String>] {
    throw(@String) -> { string_length(@String.0) }
  } in {
    throw("hello")
  }
}
"""
        assert _run(src, fn="test") == 5

    def test_exn_string_no_throw(self) -> None:
        """Exn<String> handler with non-throwing body: pair type locals allocated."""
        src = """\
effect Exn<E> {
  op throw(E -> Never);
}
public fn test(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  handle[Exn<String>] {
    throw(@String) -> { 0 - 1 }
  } in {
    string_length("world")
  }
}
"""
        assert _run(src, fn="test") == 5

    def test_exn_string_handler_returns_string(self) -> None:
        """Handler clause returns a String (result_wt == i32_pair → result i32 i32)."""
        src = """\
effect Exn<E> {
  op throw(E -> Never);
}
public fn test(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @String = handle[Exn<String>] {
    throw(@String) -> { @String.0 }
  } in {
    throw("caught")
  };
  IO.print(@String.0)
}
"""
        # Pin the ABI-level encoding: tag uses (param i32 i32) for the String
        # payload, and the outer block/try_table carry (result i32 i32) because
        # the handler clause returns a String.
        result = _compile_ok(src)
        assert "(tag $exn_String (param i32 i32))" in result.wat
        assert "result i32 i32" in result.wat
        # Verify runtime behaviour
        assert _run_io(src, fn="test") == "caught"

    def test_exn_string_empty_payload(self) -> None:
        """throw("") correctly passes a zero-length ptr/len pair through the tag."""
        src = """\
effect Exn<E> {
  op throw(E -> Never);
}
public fn test(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  handle[Exn<String>] {
    throw(@String) -> { string_length(@String.0) }
  } in {
    throw("")
  }
}
"""
        assert _run(src, fn="test") == 0


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


class TestRefinementRuntimeGuards:
    """#746: refined params/returns carry a runtime predicate guard, so an
    unverified compile traps (via ``$vera.contract_fail``) on a violating
    value rather than silently storing it.  The function boundary (param entry
    + return exit) is where the refinement invariant is relied upon; call
    arguments are covered transitively by the callee's param guard."""

    _PRE = "type PosInt = { @Int | @Int.0 > 0 };\n"

    def test_refined_param_guard_traps_on_negative(self) -> None:
        src = self._PRE + """
public fn use_it(@PosInt -> @Int)
  requires(true) ensures(true) effects(pure)
{ @PosInt.0 }
"""
        _run_refine_trap(src, fn="use_it", args=[-5])
        assert _run(src, fn="use_it", args=[7]) == 7

    def test_refined_param_guard_traps_on_zero(self) -> None:
        src = self._PRE + """
public fn use_it(@PosInt -> @Int)
  requires(true) ensures(true) effects(pure)
{ @PosInt.0 }
"""
        _run_refine_trap(src, fn="use_it", args=[0])

    def test_refined_return_guard_traps(self) -> None:
        src = self._PRE + """
public fn mk(@Int -> @PosInt)
  requires(true) ensures(true) effects(pure)
{ @Int.0 }
"""
        _run_refine_trap(src, fn="mk", args=[-5])
        assert _run(src, fn="mk", args=[7]) == 7

    def test_call_argument_guarded_transitively(self) -> None:
        """A violating call argument traps via the callee's param guard — no
        separate call-site guard is needed."""
        src = self._PRE + """
public fn use_it(@PosInt -> @Int)
  requires(true) ensures(true) effects(pure)
{ @PosInt.0 }

public fn caller(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ use_it(@Int.0) }
"""
        _run_refine_trap(src, fn="caller", args=[-3])
        assert _run(src, fn="caller", args=[9]) == 9

    def test_valid_value_passes_param_and_return_guards(self) -> None:
        """A satisfying value flows through both the entry and exit guards."""
        src = self._PRE + """
public fn id_pos(@PosInt -> @PosInt)
  requires(true) ensures(true) effects(pure)
{ @PosInt.0 }
"""
        assert _run(src, fn="id_pos", args=[42]) == 42
        _run_refine_trap(src, fn="id_pos", args=[-1])

    def test_refined_string_param_guard_traps(self) -> None:
        src = """
type NonEmpty = { @String | string_length(@String.0) > 0 };
public fn use_s(@NonEmpty -> @Int)
  requires(true) ensures(true) effects(pure)
{ string_length(@NonEmpty.0) }
public fn entry(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ use_s("") }
"""
        _run_refine_trap(src, fn="entry")

    def test_refined_string_return_guard_traps(self) -> None:
        src = """
type NonEmpty = { @String | string_length(@String.0) > 0 };
public fn mk(@String -> @NonEmpty)
  requires(true) ensures(true) effects(pure)
{ @String.0 }
public fn entry(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ string_length(mk("")) }
"""
        _run_refine_trap(src, fn="entry")

    def test_generic_refined_return_guarded_after_monomorphization(self) -> None:
        """A generic function with a *concrete* refined return is runtime-guarded
        on its monomorphised instance (the static obligation is skipped for
        generics — #555 — but codegen monomorphises and the return guard
        fires)."""
        src = self._PRE + """
public forall<T> fn coerce(@T -> @PosInt)
  requires(true) ensures(true) effects(pure)
{ 0 - 1 }
public fn entry(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ coerce(5) }
"""
        _run_refine_trap(src, fn="entry")

    _ARR = (
        "type NonEmptyArray = "
        "{ @Array<Int> | array_length(@Array<Int>.0) > 0 };\n"
    )

    def test_array_param_guard_traps_on_empty(self) -> None:
        """A refinement over a non-primitive (`Array`) base is runtime-guarded
        too — the predicate is compiled to WASM directly (Z3 cannot decide
        `array_length`, but codegen can), so an empty array into a
        `@NonEmptyArray` parameter traps.

        The body returns ``array_length(...)`` rather than indexing
        ``[0]``: absent the guard, an empty array would return 0 normally
        instead of trapping on an out-of-bounds index, so the trap on
        ``count([])`` isolates the *guard* as the sole cause."""
        src = self._ARR + """
public fn count(@NonEmptyArray -> @Int)
  requires(true) ensures(true) effects(pure)
{ array_length(@NonEmptyArray.0) }
public fn empty(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ count([]) }
public fn nonempty(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ count([42, 7]) }
"""
        _run_refine_trap(src, fn="empty")
        assert _run(src, fn="nonempty") == 2

    def test_array_return_guard_traps_on_empty(self) -> None:
        """A refined `@NonEmptyArray` return is runtime-guarded at exit."""
        src = self._ARR + """
public fn mk(@Array<Int> -> @NonEmptyArray)
  requires(true) ensures(true) effects(pure)
{ @Array<Int>.0 }
public fn entry(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ let @NonEmptyArray = mk([]); 0 }
"""
        _run_refine_trap(src, fn="entry")

    def test_param_guard_fires_before_precondition(self) -> None:
        """The refined-parameter guard runs *before* explicit preconditions:
        a `requires` that itself depends on the refined param must not trap
        first.  Passing `0` to a `@NonZero` parameter reports the refinement
        violation (a contract-fail ``RuntimeError``) rather than the
        precondition's `10 / 0` integer-divide-by-zero WASM trap (CR
        re-review of 100f938)."""
        src = """
type NonZero = { @Int | @Int.0 != 0 };
public fn risky(@NonZero -> @Int)
  requires(10 / @NonZero.0 > 0) ensures(true) effects(pure)
{ @NonZero.0 }
public fn entry(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ risky(0) }
"""
        result = _compile_ok(src)
        # The contract-fail channel raises RuntimeError carrying the
        # refinement message; a div-by-zero (i.e. precondition-first) would
        # instead surface as a bare wasmtime trap, failing this match.
        with pytest.raises(RuntimeError, match="Refinement violation"):
            execute(result, fn_name="entry")

    def test_return_guard_fires_before_ensures(self) -> None:
        """The refined-return guard runs *before* explicit ensures (symmetric
        with the param ordering): an `ensures(...)` that divides by the result
        must not trap first.  `coerce(0)` narrowing `0` into a `@NonZero`
        return reports the refinement violation, not the ensures' `100 / 0`
        integer-divide-by-zero (CR full-review of a48cd2c).  The ensures is a
        tautology (`x == x`) so it verifies, yet still emits the dividing
        expression at run time."""
        src = """
type NonZero = { @Int | @Int.0 != 0 };
public fn coerce(@Int -> @NonZero)
  requires(true)
  ensures(100 / @NonZero.result == 100 / @NonZero.result) effects(pure)
{ @Int.0 }
public fn entry(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ coerce(0) }
"""
        # Guard-first -> "Refinement violation"; ensures-first -> a bare
        # div-by-zero trap that would fail this match.
        _run_refine_trap(src, fn="entry")


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
        """Executing a String-returning function decodes the (ptr, len) pair
        back into the original Python str (not a bare heap pointer).

        Pre-fix this test asserted ``isinstance(value, int)`` because the
        CLI displayed only the first half of the i32_pair return.  After
        the alias-codegen burndown PR (v0.0.135), execute() decodes the
        UTF-8 bytes from linear memory so `vera run` on a String-returning
        `main` shows the actual string instead of a confusing pointer.
        """
        src = '''
public fn hello(-> @String)
  requires(true) ensures(true) effects(pure)
{ "hello" }
'''
        result = _compile_ok(src)
        exec_result = execute(result, fn_name="hello")
        assert exec_result.value == "hello"

    def test_string_alias_return_execution(self) -> None:
        """Aliased String returns decode the same way as direct String —
        `type Greeting = String` participates in `fn_string_returns`
        because `_return_type_is_string` resolves aliases.  Locks in the
        cooperation between #583's alias work and the String-decode path.
        """
        src = '''
type Greeting = String;

public fn hello(-> @Greeting)
  requires(true) ensures(true) effects(pure)
{ "hello" }
'''
        result = _compile_ok(src)
        exec_result = execute(result, fn_name="hello")
        assert exec_result.value == "hello"

    def test_array_return_unchanged(self) -> None:
        """Array<T> returns deliberately keep the bare-pointer fallback —
        their bytes-at-ptr aren't UTF-8 and decoding them would require
        element-type-aware formatting (separate scope).  Locks in the
        intentional asymmetry with String returns.
        """
        src = '''
public fn nums(-> @Array<Int>)
  requires(true) ensures(true) effects(pure)
{ [1, 2, 3] }
'''
        result = _compile_ok(src)
        exec_result = execute(result, fn_name="nums")
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

    def test_nested_alias_array_length_559(self) -> None:
        """#559 — `type Row = Array<Int>; type Grid = Array<Row>;`
        with `array_length(@Grid.0[0])` compiles and runs.

        Pre-fix `_alias_array_element` returned `NamedType("Row")`
        as the element type of `@Grid.0`.  Downstream WASM-type
        lookups treated `Row` as a scalar (it's an alias name, not
        the canonical `Array<Int>` shape) and emitted a load-as-i32
        + ``i64.extend_i32_u`` against what is actually a heap
        pointer to a (ptr, len) pair — WASM validation rejected the
        module with ``type mismatch: expected a type but nothing on
        stack``.  Post-fix the helper canonicalises the returned
        element type, so the chained-indexing branch in
        ``_infer_index_element_type_expr`` and the downstream size
        lookups both see ``NamedType("Array", (Int,))`` and emit
        the correct i32_pair load.
        """
        src = """
type Row = Array<Int>;
type Grid = Array<Row>;

public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Grid = [[10]];
  array_length(@Grid.0[0])
}
"""
        assert _run(src) == 1

    def test_nested_alias_2d_index_559(self) -> None:
        """#559 — 2D index through nested aliases.

        Verifies the chained-indexing branch in
        ``_infer_index_element_type_expr`` succeeds for
        ``@Grid.0[0][1]``: the inner IndexExpr's element type must
        be canonicalised to ``Array<Int>`` so the outer's check
        ``inner_te.name == "Array"`` matches.
        """
        src = """
type Row = Array<Int>;
type Grid = Array<Row>;

public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Grid = [[10, 20], [30, 40]];
  @Grid.0[1][0]
}
"""
        assert _run(src) == 30

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

    # IO.read_char — pins the stdin_buf fixture short-circuit in
    # host_read_char.  Subprocess-based tests in test_cli.py cover
    # the real-pipe (non-TTY) path; these in-process tests pin
    # the StringIO fixture path that production code can hit via
    # `execute(stdin=...)`.  The TTY-raw-mode and Windows-msvcrt
    # paths are out of reach for automated testing without a
    # headless PTY harness — documented in the host_read_char
    # comment block.

    def test_io_read_char_stdin_buf_single(self) -> None:
        """stdin_buf path returns the first character on read_char."""
        source = """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  match IO.read_char(()) {
    Ok(@String) -> IO.print(@String.0),
    Err(@String) -> IO.print(@String.0)
  }
}
"""
        result = _compile_ok(source)
        exec_result = execute(result, fn_name="main", stdin="A")
        assert exec_result.stdout == "A"
        assert exec_result.stderr == ""

    def test_io_read_char_stdin_buf_empty(self) -> None:
        """Empty stdin_buf returns Err("EOF"), not a crash or hang."""
        source = """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  match IO.read_char(()) {
    Ok(@String) -> IO.print(string_concat("got: ", @String.0)),
    Err(@String) -> IO.print(@String.0)
  }
}
"""
        result = _compile_ok(source)
        exec_result = execute(result, fn_name="main", stdin="")
        assert exec_result.stdout == "EOF"
        assert exec_result.stderr == ""

    def test_io_read_char_stdin_buf_sequential(self) -> None:
        """Two reads from the same stdin_buf advance the cursor.

        Pins that `stdin_buf.read(1)` consumes characters in order.
        Catches regressions that would replace `.read(1)` with
        `.getvalue()[0]` or similar non-advancing reads.
        """
        source = """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @String = match IO.read_char(()) {
    Ok(@String) -> @String.0,
    Err(@String) -> "X"
  };
  let @String = match IO.read_char(()) {
    Ok(@String) -> @String.0,
    Err(@String) -> "X"
  };
  IO.print(string_concat(@String.1, @String.0))
}
"""
        result = _compile_ok(source)
        exec_result = execute(result, fn_name="main", stdin="AB")
        assert exec_result.stdout == "AB"
        assert exec_result.stderr == ""

    def test_io_read_char_stdin_buf_then_eof(self) -> None:
        """Read-succeeds-then-EOF: first call Ok, second call Err."""
        source = """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @String = match IO.read_char(()) {
    Ok(@String) -> @String.0,
    Err(@String) -> "E1"
  };
  let @String = match IO.read_char(()) {
    Ok(@String) -> string_concat("got: ", @String.0),
    Err(@String) -> @String.0
  };
  IO.print(string_concat(@String.1, "|"));
  IO.print(@String.0)
}
"""
        result = _compile_ok(source)
        exec_result = execute(result, fn_name="main", stdin="A")
        assert exec_result.stdout == "A|EOF"
        assert exec_result.stderr == ""

    def test_io_read_char_stdin_buf_utf8(self) -> None:
        """Multi-byte UTF-8 is read as one Unicode character.

        StringIO's `read(1)` returns one character (not one byte),
        so `é` (2-byte UTF-8) round-trips intact through the
        stdin_buf path.  Platform-independent (no reliance on the
        host's stdin encoding, unlike the subprocess tests).
        """
        source = """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  match IO.read_char(()) {
    Ok(@String) -> IO.print(@String.0),
    Err(@String) -> IO.print(@String.0)
  }
}
"""
        result = _compile_ok(source)
        exec_result = execute(result, fn_name="main", stdin="é")
        assert exec_result.stdout == "é"
        assert exec_result.stderr == ""

    def test_io_read_char_stdin_buf_passes_eot_literally(self) -> None:
        """Piped `\\x04` (Ctrl-D / EOT) stays a literal byte.

        The Unix TTY cbreak branch maps `\\x04` to EOF (so a user
        pressing Ctrl-D in a real-time CLI gets EOF semantics
        despite ICANON being disabled).  The non-TTY paths must
        NOT do that mapping — a pipe is a byte stream and the
        producer chose to include `\\x04`.  This pins the
        intentional asymmetry: stdin_buf returns `Ok("\\x04")`,
        not `Err("EOF")`.
        """
        source = """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  match IO.read_char(()) {
    Ok(@String) -> IO.print(string_concat("byte: ", @String.0)),
    Err(@String) -> IO.print(string_concat("err: ", @String.0))
  }
}
"""
        result = _compile_ok(source)
        exec_result = execute(result, fn_name="main", stdin="\x04")
        assert exec_result.stdout == "byte: \x04"
        assert exec_result.stderr == ""

    def test_io_read_file_success(self) -> None:
        """IO.read_file reads a file and returns Ok(contents)."""
        import tempfile
        import os
        with tempfile.NamedTemporaryFile(
            mode="w", suffix=".txt", delete=False, encoding="utf-8",
        ) as f:
            f.write("file contents")
            f.flush()
            tmp_path = f.name
        # Hardcode the path in the Vera source (can't pass String args
        # to WASM functions from the host).  Convert to POSIX form so
        # backslashes in Windows paths (e.g. `C:\Users\...`) don't
        # collide with Vera's string-literal escape grammar — `\U`
        # would trip [E009] "invalid escape sequence" at parse time.
        # Windows file APIs accept forward slashes natively.  (#642)
        vera_path = tmp_path.replace(os.sep, "/")
        source = f"""\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{{
  match IO.read_file("{vera_path}") {{
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
        import tempfile
        import os
        tmp_dir = tempfile.mkdtemp()
        tmp_file = os.path.join(tmp_dir, "vera_test.txt")
        # Write a file from Vera, then read it back.  Convert to POSIX
        # form so backslashes in Windows paths don't trip Vera's
        # string-literal escape grammar — see `test_io_read_file_success`
        # for the same fix and #642 for the original repro.
        vera_path = tmp_file.replace(os.sep, "/")
        source = f"""\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{{
  match IO.write_file("{vera_path}", "hello from vera") {{
    Ok(_) -> {{
      match IO.read_file("{vera_path}") {{
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

    # ----------------------------------------------------------------
    # IO.sleep, IO.time, IO.stderr — added in #463.
    # ----------------------------------------------------------------

    def test_io_time_returns_positive_nat(self) -> None:
        """IO.time() returns current Unix time in ms — bracketed by host clock.

        Captures the Python-side time in milliseconds immediately
        before and after execution, then asserts the Vera program's
        reading falls inside that window.  Doesn't depend on a
        hard-coded epoch threshold, so it can't false-negative on
        hosts with skewed or frozen clocks.
        """
        import time as _time_mod
        source = """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Nat = IO.time(());
  IO.print(nat_to_string(@Nat.0))
}
"""
        result = _compile_ok(source)
        before_ms = int(_time_mod.time() * 1000)
        exec_result = execute(result, fn_name="main")
        after_ms = int(_time_mod.time() * 1000)
        vera_ms = int(exec_result.stdout)
        assert before_ms <= vera_ms <= after_ms, (
            f"IO.time() returned {vera_ms}, expected value in "
            f"[{before_ms}, {after_ms}]"
        )

    def test_io_sleep_completes(self) -> None:
        """IO.sleep(ms) returns without trapping; program continues.

        Doesn't test timing precision — that's host-dependent and
        flaky under load.  The contract is just that sleep returns
        and subsequent statements execute.
        """
        source = """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print("before ");
  IO.sleep(1);
  IO.print("after")
}
"""
        result = _compile_ok(source)
        exec_result = execute(result, fn_name="main")
        assert exec_result.stdout == "before after"

    def test_io_sleep_zero_is_noop(self) -> None:
        """IO.sleep(0) is a no-op — doesn't block, doesn't error."""
        source = """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.sleep(0);
  IO.print("ok")
}
"""
        result = _compile_ok(source)
        exec_result = execute(result, fn_name="main")
        assert exec_result.stdout == "ok"

    def test_io_stderr_captured_when_requested(self) -> None:
        """IO.stderr output is captured into ExecuteResult.stderr.

        Confirms the stderr/stdout separation: IO.print goes to
        stdout, IO.stderr goes to stderr, neither crosses over.
        """
        source = """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print("to stdout");
  IO.stderr("to stderr");
  IO.print(" more stdout")
}
"""
        result = _compile_ok(source)
        exec_result = execute(
            result, fn_name="main", capture_stderr=True,
        )
        assert exec_result.stdout == "to stdout more stdout"
        assert exec_result.stderr == "to stderr"

    def test_io_stderr_default_not_captured(self) -> None:
        """Without capture_stderr=True, stderr field is empty string.

        Preserves the pre-#463 ExecuteResult shape: tests that don't
        opt in to capture don't see anything in ``stderr``, even if
        the Vera program wrote to it (that output went to the real
        sys.stderr).  Also asserts stdout is empty — a program that
        only calls IO.stderr must not leak any bytes into the stdout
        stream.
        """
        source = """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.stderr("uncaptured")
}
"""
        result = _compile_ok(source)
        exec_result = execute(result, fn_name="main")
        assert exec_result.stderr == ""
        assert exec_result.stdout == ""

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
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @String = "world";
  IO.print("hello \\(@String.0)")
}
"""
        assert _run_io(source, fn="main") == "hello world"

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

    def test_string_returning_fncall_inside_interpolation_602(self) -> None:
        """#602 — interpolating a String-returning function call directly.

        Pre-fix: `_infer_fncall_vera_type` had no `i32_pair` branch in
        the WAT-type → Vera-type fallback, so a user fn returning
        `String` mapped to `None` here.  `_translate_interpolated_string`
        then fell through to the `to_string(...)` Int-conversion
        wrapper, which reads its arg as `i64` — but the FnCall pushed
        `i32_pair`.  WASM validation rejected the module with
        `expected i64, found i32` at the offending offset.

        Post-fix: the inference path consults `_fn_ret_type_exprs`
        (the same registry added by #614) when WAT type is `i32_pair`,
        returns the proper `String` Vera-type name, and the
        interpolation desugars to `string_concat(make_str(()), "\\n")`
        with both args correctly typed as i32_pair.
        """
        source = _IO_PRELUDE + """\
private fn make(-> @String)
  requires(true) ensures(true) effects(pure)
{ "hello" }

public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print("\\(make(()))\\n")
}
"""
        assert _run_io(source, fn="main") == "hello\n"

    def test_array_returning_fncall_indexed_inside_interpolation(self) -> None:
        """Sibling case: an `Array<T>`-returning fn indexed into Int,
        used in interpolation.  Same `i32_pair` return type as the
        String case but the index strips back to an `Int` element —
        exercises both halves of the inference path together.
        """
        source = _IO_PRELUDE + """\
private fn make_arr(-> @Array<Int>)
  requires(true) ensures(true) effects(pure)
{ [10, 20, 30] }

public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print("\\(make_arr(())[0])")
}
"""
        assert _run_io(source, fn="main") == "10"

    def test_inline_refinement_string_in_interpolation(self) -> None:
        """A fn declared with an inline refinement return type
        (`@{ @String | predicate }`) used in interpolation.

        Surfaced during PR #627's review (CodeRabbit, third trigger
        in the same bug class as #602 and the type-alias case).
        `_register_fn` stores the literal AST, so `_fn_ret_type_exprs`
        holds a `RefinementType` directly.  My initial alias-resolving
        fix only handled `NamedType` — `isinstance(ret_te, ast.NamedType)`
        was False for a `RefinementType`, fell through to None, same
        original #602 trap.

        Fix: extracted the inference into `_resolve_i32_pair_ret_te`
        which handles both `NamedType` (with alias resolution) and
        `RefinementType` (unwrap to base, then resolve).
        """
        source = _IO_PRELUDE + """\
private fn make(-> @{ @String | string_length(@String.0) > 0 })
  requires(true) ensures(true) effects(pure)
{ "hello" }

public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print("\\(make(()))\\n")
}
"""
        assert _run_io(source, fn="main") == "hello\n"

    def test_nested_refinement_string_in_interpolation(self) -> None:
        """Fifth trigger of the #602 bug class — surfaced by the
        silent-failure-hunter agent during PR #629's review.

        The grammar admits `refinement_type` over any `type_expr`, so
        a return type can wrap refinements in refinements:
        `@{ @{ @String | p1 } | p2 }`.  PR #629's initial fix used
        `if isinstance(ret_te, ast.RefinementType): base = ret_te.base_type`
        — only one level of unwrap.  A nested refinement still fell
        through to None, reproducing the original #602 trap.

        Fix (in this PR's review pass): replaced the one-level unwrap
        with a `while` loop that handles arbitrary nesting depth.
        Same change applied symmetrically to the IndexExpr-of-FnCall
        inference path.
        """
        source = _IO_PRELUDE + """\
private fn make(-> @{ @{ @String | string_length(@String.0) > 0 } | string_length(@String.0) < 100 })
  requires(true) ensures(true) effects(pure)
{ "hello" }

public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print("\\(make(()))\\n")
}
"""
        assert _run_io(source, fn="main") == "hello\n"

    def test_apply_fn_nested_refinement_in_interpolation(self) -> None:
        """Seventh trigger of the #602 bug class — surfaced by the
        silent-failure-hunter agent during PR #629's review.

        Path: `apply_fn(@FnAlias.0, ())` inside an interpolation,
        where the `FnType` alias's return type is a *nested*
        refinement.  Three separate inference sites in
        `vera/wasm/inference.py` all walk the FnType's
        `return_type` and only handled `NamedType` directly:

        - `_infer_fncall_vera_type` (apply_fn branch) — for the
          interpolation argument's vera-type lookup
        - `_resolve_generic_fn_return` — for generic-instantiated
          FnType returns
        - `_fn_type_return_wasm` — for the WASM-canonical return type

        Pre-fix, the apply_fn branch returned None for nested
        refinements, the interpolation fell through to the
        `to_string(...)` wrapper, and at validation time WASM
        rejected the i32→i64 mismatch (`expected i64, found i32`)
        that's been the canonical surface of this bug class since
        #602.

        Fix: `while isinstance(ret, ast.RefinementType): ret =
        ret.base_type` at all three sites — same shape as the
        FnCall path, applied symmetrically to the FnType-alias
        path.
        """
        source = _IO_PRELUDE + """\
type Maker = fn(Unit -> { @{ @String | string_length(@String.0) > 0 } | string_length(@String.0) < 100 }) effects(pure);

private fn make_maker(@Unit -> @Maker)
  requires(true) ensures(true) effects(pure)
{ fn(@Unit -> @String) effects(pure) { "hello" } }

public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Maker = make_maker(());
  IO.print("\\(apply_fn(@Maker.0, ()))\\n")
}
"""
        assert _run_io(source, fn="main") == "hello\n"

    def test_apply_fn_anon_inline_string_in_interpolation(self) -> None:
        """Ninth trigger of the #602 bug class — surfaced by
        CodeRabbit during PR #629's final review pass, less than an
        hour after filing #630 (the structural close-out for this
        bug class).  Empirical confirmation that the trigger rate
        outpaces local fix throughput — exactly the argument made
        for centralising canonicalisation.

        Path: `apply_fn(fn(@Unit -> @String) effects(pure) { ... },
        ())` — apply_fn called directly on an inline `AnonFn`
        literal rather than a `SlotRef` to a let-bound closure.
        Pre-fix `_infer_fncall_vera_type` only handled the SlotRef
        arg shape; the AnonFn case fell through, return value was
        None, and downstream interpolation re-triggered the canonical
        `expected i64, found i32` WASM-validation surface.

        Fix: added an `elif isinstance(closure_arg, ast.AnonFn)`
        branch alongside the SlotRef branch in
        `_infer_fncall_vera_type`.  Simpler than the SlotRef path
        (no alias substitution — AnonFn has `return_type: TypeExpr`
        directly), but the same RefinementType-unwrap +
        `_format_named_type_canonical` shape applies.
        """
        source = _IO_PRELUDE + """\
private fn helper(@Unit -> @String)
  requires(true) ensures(true) effects(pure)
{ "hello" }

public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print("\\(apply_fn(fn(@Unit -> @String) effects(pure) { helper(()) }, ()))\\n")
}
"""
        assert _run_io(source, fn="main") == "hello\n"

    def test_apply_fn_anon_nested_refinement_in_interpolation(
        self,
    ) -> None:
        """Tenth trigger of the #602 bug class — surfaced by
        CodeRabbit on PR #629 immediately after the 9th was fixed.
        Inverse surface: `expected i32, found i64` rather than the
        usual `expected i64, found i32`, because this site is on
        the *WASM-type* inference half of the dispatcher
        (`_infer_apply_fn_return_type`, which infers the
        `call_indirect` sig) rather than the Vera-type-name half
        (`_infer_fncall_vera_type`, which the 9th trigger hit).

        Path: `apply_fn(fn(@Unit -> @{ @{ @String | p1 } | p2 })
        effects(pure) { ... }, ())` — inline `AnonFn` declaring a
        nested-refinement return.  Pre-fix
        `_infer_apply_fn_return_type`'s `AnonFn` branch had a
        single-level `if isinstance(ret, ast.RefinementType): base
        = ret.base_type` unwrap with a `# pragma: no cover —
        closure returns are not refinement types` claim — both
        empirically disproved.  Single-level unwrap on a nested
        refinement leaves `base` as another `RefinementType`, the
        `NamedType` check misses, and the method falls through to
        `return "i64"` — the call site emitted `i32_pair`, hence
        the inverse-direction WASM-validation surface.

        Fix: replaced the single-level `if`-unwrap with the
        established `while`-loop shape used at every other
        type-walking site, and removed the disproven
        `# pragma: no cover` claim.

        Queued for obsolescence by [#630](https://github.com/aallan/vera/issues/630)
        when the centralised `_canonical_vera_type` lands; this
        test will continue to pin the trigger through that
        refactor.
        """
        source = _IO_PRELUDE + """\
private fn helper(@Unit -> @String)
  requires(true) ensures(true) effects(pure)
{ "hello" }

public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print("\\(apply_fn(fn(@Unit -> @{ @{ @String | string_length(@String.0) > 0 } | string_length(@String.0) < 100 }) effects(pure) { helper(()) }, ()))\\n")
}
"""
        assert _run_io(source, fn="main") == "hello\n"

    def test_apply_fn_aliased_string_in_interpolation(self) -> None:
        """Eighth trigger of the #602 bug class — surfaced by
        CodeRabbit during PR #629's final review pass.

        Path: `apply_fn(@Maker.0, ())` inside an interpolation,
        where `Maker = fn(Unit -> Str) effects(pure)` and
        `type Str = String;`.  Pre-fix `_infer_fncall_vera_type`'s
        apply_fn branch called `_format_named_type` on
        `NamedType("Str")` which returned the alias name "Str" —
        downstream `_translate_interpolated_string` checks
        `vera_type == "String"`, the alias name missed, and the
        value fell through to the `to_string(...)` wrapper over an
        `i32_pair`, reproducing the canonical `expected i64, found
        i32` WASM-validation surface of this bug class.

        Fix: introduced `_format_named_type_canonical` (resolves
        `te.name` through the alias chain via
        `_resolve_base_type_name`, then formats with original
        `type_args`).  Replaced both `_format_named_type` calls in
        the apply_fn branch — substitution and fallback — with the
        canonical variant, mirroring the canonicalisation already
        done in `_resolve_i32_pair_ret_te` for the regular FnCall
        path.
        """
        source = _IO_PRELUDE + """\
type Str = String;
type Maker = fn(Unit -> Str) effects(pure);

private fn make_maker(@Unit -> @Maker)
  requires(true) ensures(true) effects(pure)
{ fn(@Unit -> @String) effects(pure) { "hello" } }

public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Maker = make_maker(());
  IO.print("\\(apply_fn(@Maker.0, ()))\\n")
}
"""
        assert _run_io(source, fn="main") == "hello\n"

    def test_refinement_over_type_alias_in_interpolation(self) -> None:
        """Sibling case to nested-refinement — refinement applied to a
        type alias.  Worked already because `_resolve_base_type_name`
        recursively follows alias chains.  Test pins the working
        behaviour so a future change to the alias-resolution path
        can't regress it silently.
        """
        source = _IO_PRELUDE + """\
type Str = String;

private fn make(-> @{ @Str | string_length(@Str.0) > 0 })
  requires(true) ensures(true) effects(pure)
{ "hello" }

public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print("\\(make(()))\\n")
}
"""
        assert _run_io(source, fn="main") == "hello\n"

    def test_inline_refinement_array_in_indexed_interpolation(self) -> None:
        """A fn declared with a *nested* refinement return type over
        `Array<T>`, indexed inside an interpolation.

        Parallel instance of the same RefinementType gap, but in
        `_infer_index_element_type_expr`'s FnCall branch (the path
        added by #614).  Pre-fix the IndexExpr-of-FnCall element-type
        inference failed for refinement-returning fns, the enclosing
        function got dropped from the output module, and at top level
        the symptom was the [E602] "main body contains unsupported
        expressions — skipped" warning.

        Uses the nested-refinement shape (`@{ @{ @Array<Int> | p1 } |
        p2 }`) so this test exercises the `while`-loop unwrap added
        in PR #629's review pass alongside the parallel string-side
        nested test — without the loop, the array branch would only
        peel one level and fall through.

        Fix: same RefinementType `while`-loop unwrap applied to
        `_infer_index_element_type_expr`'s FnCall branch.
        """
        source = _IO_PRELUDE + """\
private fn make(-> @{ @{ @Array<Int> | array_length(@Array<Int>.0) > 0 } | array_length(@Array<Int>.0) < 100 })
  requires(true) ensures(true) effects(pure)
{ [10, 20, 30] }

public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print("\\(make(())[1])\\n")
}
"""
        assert _run_io(source, fn="main") == "20\n"

    def test_type_alias_string_in_interpolation(self) -> None:
        """A fn returning a type alias of `String` (e.g. `type Str =
        String; fn make(-> @Str)`) used in interpolation.

        Surfaced during PR #627's review (CodeRabbit, post-#602 fix):
        my initial fix returned `ret_te.name` directly from the
        `_fn_ret_type_exprs` registry — which stores the *declared*
        TypeExpr `NamedType("Str")`, not the resolved
        `NamedType("String")`.  Downstream `_translate_interpolated_string`
        checks `vera_type == "String"` (and the conversion-map check)
        — both miss for `"Str"` — so the value fell through to the
        `to_string(...)` fallback wrapper, reproducing the original
        #602 trap (`expected i64, found i32` at WASM validation) for
        a *different* trigger.

        Fix: resolve aliases via `_resolve_base_type_name` before
        returning.  Same shape applies symmetrically to the generic-
        branch `i32_pair` lookup added in `d78b4dc`, which now also
        canonicalises (currently latent — see code comment).
        """
        source = _IO_PRELUDE + """\
type Str = String;

private fn make(-> @Str)
  requires(true) ensures(true) effects(pure)
{ "hello" }

public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print("\\(make(()))\\n")
}
"""
        assert _run_io(source, fn="main") == "hello\n"

    def test_no_to_string_wrap_on_string_returning_fncall_602(self) -> None:
        """Structural assertion for the #602 fix.

        Pre-fix: `_infer_fncall_vera_type` returned None for a user fn
        whose WAT return type was `i32_pair`, so
        `_translate_interpolated_string` wrapped the FnCall with
        `to_string(...)`.  That wrapping was the *cause* of the WASM
        validation trap (`to_string` reads its arg as `i64` but
        `i32_pair` is two `i32`s).

        Post-fix the wrap should never occur for a `String`-returning
        FnCall — the inference walker now returns `"String"`, the
        early `vera_type == "String"` branch fires, and the FnCall
        flows directly into `string_concat` un-wrapped.

        This is a *structural* test that locks the fix at the codegen
        layer.  The companion runtime test
        (`test_string_returning_fncall_inside_interpolation_602`)
        catches behavioural regressions; this one catches inference
        regressions whose downstream output happens to look right by
        coincidence.
        """
        source = _IO_PRELUDE + """\
private fn make(-> @String)
  requires(true) ensures(true) effects(pure)
{ "hello" }

public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  -- Two parts so the desugar produces `string_concat(make(()), "\\n")`
  -- (a single-part interpolation short-circuits to `translate_expr(p)`
  -- without going through string_concat).
  IO.print("\\(make(()))\\n")
}
"""
        wat = _compile_ok(source).wat
        # Pull out main's body so a `to_string` reference elsewhere
        # in the module (e.g. helper fns from the prelude) doesn't
        # produce a false negative.
        main_match = re.search(
            r"\(func \$main.*?(?=\n\s*\(func |\n\s*\)\s*$)",
            wat,
            re.DOTALL,
        )
        assert main_match is not None, "main function not found in WAT"
        main_body = main_match.group(0)
        # `to_string` was the bug's wrapper — its absence is the
        # load-bearing structural property of the fix.  (`string_concat`
        # is inlined as byte-copy loops in the WAT rather than emitted
        # as a separate `call $string_concat`, so we don't assert on
        # it directly.)
        assert "call $to_string" not in main_body, (
            "Pre-#602 bug shape: `String`-returning FnCall in "
            "interpolation should NOT be wrapped with `to_string`. "
            "If this assertion fires, `_infer_fncall_vera_type` has "
            "regressed for `i32_pair` returns."
        )

    def test_escaped_backslash_before_paren_is_literal(self) -> None:
        r"""``"\\("`` (a literal backslash followed by a literal
        ``(``) must be treated as two literal characters, NOT as an
        interpolation opener.

        Pre-#649-review-pass-2 the two helpers in
        ``vera/transform.py`` disagreed: ``_has_interpolation``
        correctly skipped escaped pairs (so a string with only
        ``\\(`` was treated as having no interpolation at all), but
        ``_split_interpolation`` rescanned the second character as a
        fresh start and mis-parsed the ``\\(`` as the opener of an
        interpolation segment.  The result for a string like
        ``"a\\(b"`` was a parse-time crash (no matching ``)``) where
        the user expected a literal ``a\(b``.  CodeRabbit flagged
        the divergence on PR #649.

        This test verifies the escape-skipping logic is now
        consistent across both helpers by compiling a program that
        prints a literal backslash-paren sequence and asserting the
        output preserves the literal characters.
        """
        source = _IO_PRELUDE + """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print("a\\\\(b)c")
}
"""
        # In the Python source above, "a\\\\(b)c" is a 9-char Python
        # string literal that produces the 7-char Vera source-text
        # `a\\(b)c` — which is the 5-char Vera string value
        # `a\(b)c` after escape decoding.  The compiler must accept
        # this without trying to interpret `\(` as an interpolation
        # opener (because the preceding `\\` already consumed the
        # backslash).
        assert _run_io(source, fn="main") == "a\\(b)c", (
            "Expected literal `a\\(b)c`; the `\\\\(` escape pair "
            "should be two literal characters, not an interpolation "
            "opener."
        )


class TestE615LoudInterpolationFallthrough630:
    """[#630](https://github.com/aallan/vera/issues/630) Tier 2 — the
    `_translate_interpolated_string` silent-fallthrough path now emits
    a specific [E615] diagnostic and drops the function with [E602]
    instead of silently miscompiling.

    Pre-#630: when `_infer_vera_type` returned None or a name not in
    `_INTERP_TO_STRING`, the segment got wrapped in `to_string(...)`
    which reads its argument as `i64`.  An `i32_pair` (String/Array)
    or any non-`i64`-shaped value then produced invalid WASM at
    validation (`expected i64, found i32`) — the load-bearing
    silent-amplifier behind the ten triggers of the #602 bug class
    accumulated across PRs #627, #629.

    Post-#630: the canonicaliser closes most of the inference gaps
    on the producer side (Tier 1).  This test pins the consumer-side
    half (Tier 2): for a residual gap the canonicaliser doesn't
    cover, the failure manifests as a clean compile-time skip with
    a specific E-code, not invalid WASM.
    """

    def test_e615_fires_on_adt_in_interpolation(self) -> None:
        """Interpolating an ADT-typed slot — `IO.print("\\(@Option<Int>.0)")`
        — yields a non-recognised `vera_type` name (`"Option<Int>"`)
        and trips the post-#630 E615 fallthrough.

        Pre-#630 this would have wrapped the slot in `to_string(...)`
        and produced invalid WASM at instantiation; post-#630 it
        emits [E615] and the function is skipped with [E602] before
        any invalid emission.
        """
        source = _IO_PRELUDE + """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Option<Int> = Some(42);
  IO.print("\\(@Option<Int>.0)\\n")
}
"""
        result = _compile(source)
        # No errors — the program parses + type-checks cleanly.
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert not errors, (
            f"Expected no errors, got: {errors}"
        )
        # E615 fires on the interpolation segment.
        warnings = [
            d for d in result.diagnostics if d.severity == "warning"
        ]
        e615 = [d for d in warnings if d.error_code == "E615"]
        assert e615, (
            f"Expected an [E615] diagnostic; got warnings: {warnings}"
        )
        assert "interpolate" in e615[0].description.lower(), (
            f"E615 message should mention interpolation; got: "
            f"{e615[0].description}"
        )
        # Function gets dropped with the existing [E602] mechanism —
        # E615 is the *specific* annotation, E602 is the loud skip.
        e602 = [d for d in warnings if d.error_code == "E602"]
        assert e602, (
            f"Expected an [E602] skip diagnostic alongside E615; "
            f"warnings were: {warnings}"
        )
        # E615 must precede the *matching* E602 — the one for the
        # function that contained the offending interpolation — so
        # the specific-cause-then-generic-skip narrative reads
        # correctly per function.  Other E602s may interleave
        # (e.g. prelude combinators that are independently skipped
        # via #604), so we filter to the E602 mentioning `main` and
        # assert the per-function ordering invariant only.
        main_e602 = [d for d in e602 if "main" in d.description]
        assert main_e602, (
            f"Expected an [E602] mentioning `main`; e602: {e602}"
        )
        e615_idx = warnings.index(e615[0])
        main_e602_idx = warnings.index(main_e602[0])
        assert e615_idx < main_e602_idx, (
            f"E615 should precede the matching E602 (main) in the "
            f"warnings stream; got E615 at index {e615_idx}, "
            f"main's E602 at {main_e602_idx}"
        )
        # The E615 has a source location attached pointing at the
        # offending interpolation segment.  Source layout:
        #
        #     line 1: effect IO {
        #     line 2:   op print(String -> Unit);
        #     line 3: }
        #     line 4: public fn main(-> @Unit)
        #     line 5:   requires(true) ensures(true) effects(<IO>)
        #     line 6: {
        #     line 7:   let @Option<Int> = Some(42);
        #     line 8:   IO.print("\(@Option<Int>.0)\n")
        #     line 9: }
        #
        # The SlotRef ``@Option<Int>.0`` starts at line 8, column 15
        # (cols 1-2 indent, 3-4 ``IO``, 5 ``.``, 6-10 ``print``,
        # 11 ``(``, 12 ``"``, 13-14 ``\(``, 15 ``@``).  Pre-#634 the
        # span landed on line 3 (the synthetic parse-wrapper's
        # content line) because spans inside interpolated expressions
        # were never remapped from wrapper coordinates back to
        # original-source coordinates.  Closes #634.
        assert e615[0].location.line == 8, (
            f"E615 should point at the string literal on line 8 "
            f"(post-#634 span remap); got line "
            f"{e615[0].location.line}"
        )
        assert e615[0].location.column == 15, (
            f"E615 should point at column 15 (start of the SlotRef "
            f"inside the interpolation segment); got column "
            f"{e615[0].location.column}"
        )
        # `main` is not in exports because the body was dropped.
        assert "main" not in result.exports, (
            f"main should be skipped; exports: {result.exports}"
        )

    def test_e615_in_closure_body_emits_diagnostic(self) -> None:
        """Closure-body parallel of the top-level E615 path.
        Pre-this-PR the harvest in `_compile_fn` only ran for top-
        level functions; `_compile_lifted_closure` returned None
        without emitting [E615], silently dropping the closure from
        the function table.  The call_indirect at the use site then
        referenced a missing entry and WASM validation rejected the
        module — same silent-drop shape that #614/#615 fixed for
        translation failures, but for the post-#630 interpolation
        path inside closure bodies.

        Fix in PR #631: extracted the harvest into
        `CodeGenerator._harvest_interp_inference_failures` and
        called it from both functions.py and closures.py — closure
        bodies now emit [E615] for inference failures.

        Fix in PR #631 (review pass, closing #636):
        `_lift_pending_closures` now reports whether any closure
        body failed; `_compile_fn` checks the flag and drops the
        enclosing top-level fn with a specific [E602] noting the
        closure-failure cause.  Pre-fix the enclosing fn was
        emitted with a `call_indirect` to a missing function-table
        entry, producing a WASM-validation trap with no
        source-located parent-fn diagnostic.

        (silent-failure-hunter finding C1 + later CodeRabbit follow-up
        on PR #631.)
        """
        source = _IO_PRELUDE + """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Option<Int> = Some(42);
  apply_fn(fn(@Unit -> @Unit) effects(<IO>) {
    IO.print("\\(@Option<Int>.0)\\n")
  }, ())
}
"""
        result = _compile(source)
        warnings = [
            d for d in result.diagnostics if d.severity == "warning"
        ]
        e615 = [d for d in warnings if d.error_code == "E615"]
        # The closure-body harvest must emit at least one [E615].
        # Pre-#631 the closure was silently dropped with no [E615]
        # anywhere.
        assert e615, (
            f"Expected at least one [E615] from the closure body; "
            f"warnings were: {warnings}"
        )
        # The enclosing fn must be dropped via [E602].  Pre-#636
        # main remained in exports despite the closure failure,
        # producing a runtime WASM-validation trap; post-#636 the
        # parent is dropped cleanly.
        e602_main = [
            d for d in warnings
            if d.error_code == "E602" and "main" in d.description
        ]
        assert e602_main, (
            f"Expected an [E602] for `main` after closure failure; "
            f"warnings were: {warnings}"
        )
        assert "main" not in result.exports, (
            f"main should be dropped when its closure body fails to "
            f"compile (#636); exports: {result.exports}"
        )

    def test_per_function_isolation_of_failures_list(self) -> None:
        """`_interp_inference_failures` lives on `WasmContext`,
        which `_compile_fn` constructs fresh per top-level function.
        This test pins per-function isolation: a clean function
        compiled **after** a function that triggers E615 must not
        inherit the failure list and falsely emit E615.

        Test layout: `clean_before` → `dirty` → `clean_after`.
        Both `clean_*` functions must remain in exports.  Without
        the `clean_after` (only `clean_before`), a forward leak
        from `dirty` would never reach a clean function and the
        test would silently pass even with broken isolation —
        the pre-PR-#631-review-pass version of this test had this
        gap (CodeRabbit finding 2 on PR #631).

        Pre-#630: not testable because the silent fallthrough
        wrapped with `to_string`; cross-function leak wouldn't
        manifest as [E615] regardless.  Post-#630: load-bearing —
        if a future refactor reuses a context across functions or
        forgets to clear the failure list, this test fires.

        (comment-analyzer finding I4 + later CodeRabbit finding 2
        on PR #631.)
        """
        source = _IO_PRELUDE + """\
public fn clean_before(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print("clean_before\\n")
}

public fn dirty(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Option<Int> = Some(42);
  IO.print("\\(@Option<Int>.0)\\n")
}

public fn clean_after(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print("clean_after\\n")
}
"""
        result = _compile(source)
        warnings = [
            d for d in result.diagnostics if d.severity == "warning"
        ]
        e615 = [d for d in warnings if d.error_code == "E615"]
        # E615 fires exactly once — for `dirty` (Option<Int> in
        # interpolation).  If `clean_after` inherited `dirty`'s
        # failure list, we'd see a second E615 (or `clean_after`
        # would be dropped via E602).
        assert e615, (
            f"Expected [E615] for `dirty`; got warnings: {warnings}"
        )
        assert len(e615) == 1, (
            f"Expected exactly one [E615]; got {len(e615)}: {e615}"
        )
        # Both clean functions must remain in exports.  The
        # `clean_after` assertion is the one that catches forward
        # leakage — pre-fix would still pass `clean_before` but
        # fail this.
        assert "clean_before" in result.exports, (
            f"clean_before should be exported; "
            f"exports: {result.exports}"
        )
        assert "clean_after" in result.exports, (
            f"clean_after should be exported (no inference failures "
            f"in its own body, must not inherit dirty's failure "
            f"list); exports: {result.exports}"
        )
        # `dirty` is dropped via the [E602] mechanism.
        assert "dirty" not in result.exports, (
            f"dirty should be skipped; exports: {result.exports}"
        )

    def test_e615_fires_on_result_in_interpolation(self) -> None:
        """Adjacent E615 shape — `Result<T,E>` in interpolation.
        Distinct from Option (separate ADT), pre-emptively pinned
        so that a future change to canonicalisation or interpolation
        narrowing that broadens `Option<T>` handling doesn't
        accidentally regress the parallel `Result` path.

        Pins the full loud-skip surface (parallel to the ADT test):
        E615 fires for the inference miss, E602 fires for the
        function skip, and `main` is dropped from `result.exports`.

        (test-analyzer finding C3 + later CodeRabbit follow-up on
        PR #631.)
        """
        source = _IO_PRELUDE + """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Result<Int, String> = Ok(42);
  IO.print("\\(@Result<Int, String>.0)\\n")
}
"""
        result = _compile(source)
        warnings = [
            d for d in result.diagnostics if d.severity == "warning"
        ]
        e615 = [d for d in warnings if d.error_code == "E615"]
        assert e615, (
            f"Expected [E615] for Result<Int, String> interpolation; "
            f"got warnings: {warnings}"
        )
        # Loud-skip surface: E602 must also fire for `main`, and
        # main must be dropped from exports.  Parallel to the ADT
        # test's assertions — without these, a regression that
        # emits E615 but fails to propagate the function-skip
        # would silently slip past this test.
        e602_main = [
            d for d in warnings
            if d.error_code == "E602" and "main" in d.description
        ]
        assert e602_main, (
            f"Expected an [E602] for `main` after Result-in-"
            f"interpolation E615; warnings: {warnings}"
        )
        assert "main" not in result.exports, (
            f"main should be skipped when interpolation E615 fires; "
            f"exports: {result.exports}"
        )

    def test_multiple_e615_in_one_interpolation(self) -> None:
        """One [E615] per failing segment — not "first failure
        aborts loop".  Pre-this-PR the silent-fallthrough returned
        None on the first failure, so a user with N bad segments
        in one interpolation got one [E615] per recompile, N
        round-trips total.  Now the loop continues and records every
        failing segment, then bails at the end if any failed.

        (silent-failure-hunter finding H2 on PR #631.)
        """
        source = _IO_PRELUDE + """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Option<Int> = Some(1);
  let @Result<Int, String> = Ok(2);
  IO.print("\\(@Option<Int>.0) and \\(@Result<Int, String>.0)\\n")
}
"""
        result = _compile(source)
        warnings = [
            d for d in result.diagnostics if d.severity == "warning"
        ]
        e615 = [d for d in warnings if d.error_code == "E615"]
        # Two failing segments → exactly two distinct E615
        # diagnostics.  Pinning the exact count (rather than `>= 2`)
        # catches a duplicate-emit regression where the harvest
        # accidentally walks the failures list more than once or
        # the per-segment recording emits N>1 entries per failure.
        assert len(e615) == 2, (
            f"Expected exactly 2 [E615] diagnostics for two failing "
            f"interpolation segments; got {len(e615)}: {e615}"
        )
        # Per-segment span fidelity (#634).  Source layout:
        #
        #     line 9:   IO.print("\(@Option<Int>.0) and \(@Result<Int, String>.0)\n")
        #     cols ^^   ^^      ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
        #     12 ".  13-14 \(.  15 @Option starts.
        #     35-36 \(.  37 @Result starts.
        #
        # Both diagnostics must land on line 9; their columns must
        # differ and match the column of their respective SlotRef.
        # Pre-#634 both would have landed on line 3 (the synthetic
        # parse-wrapper's content line) with column 3 — the bug this
        # test pins as fixed.
        assert all(d.location.line == 9 for d in e615), (
            f"Both E615s should point at line 9; got lines "
            f"{[d.location.line for d in e615]}"
        )
        cols = sorted(d.location.column for d in e615)
        assert cols == [15, 37], (
            f"Per-segment column fidelity broken — expected first "
            f"SlotRef at col 15 (`@Option<Int>.0`) and second at col "
            f"37 (`@Result<Int, String>.0`); got {cols}"
        )

    def test_canonical_named_type_terminal_args_propagation(
        self,
    ) -> None:
        """The canonicaliser preserves `type_args` from the
        *terminal* `NamedType`, not the outermost — and walks
        through parameterised alias substitution to get there.
        For `type Box<T> = Array<T>`, indexing a fn that returns
        `@Box<Int>` must resolve to the `Int` element type: the
        walker substitutes the alias's `T` parameter with the
        concrete `Int` from the call site, follows to
        `Array<Int>`, and reports `Int` as the IndexExpr element
        type.

        Pre-PR-#631-review-pass the walker captured
        `outer_type_args` from the first NamedType reached and
        ignored `_type_alias_params` entirely.  Both gaps closed
        in this PR's review pass — the walker now (a) reads
        type_args from the terminal NamedType and (b) substitutes
        parameterised-alias type params before continuing.

        Note: a more direct test using `type Id<T> = T;` (per
        CodeRabbit's suggestion) hits a parallel
        parameterised-alias gap in `_type_expr_to_wasm_type`
        (codegen/core.py compilability check) that's outside
        #630's scope and tracked as a follow-up.  `Box<T> =
        Array<T>` exercises the walker substitution path
        end-to-end via the IndexExpr-of-FnCall element-type
        lookup, which doesn't go through the compilability
        check.

        (CodeRabbit finding 3 + code-reviewer finding I1 + later
        CodeRabbit findings 1 + 5 on PR #631.)
        """
        source = _IO_PRELUDE + """\
type Box<T> = Array<T>;

private fn make_box(@Unit -> @Box<Int>)
  requires(true) ensures(true) effects(pure)
{ [10, 20, 30] }

public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print("\\(make_box(())[1])\\n")
}
"""
        # Runs end-to-end — IndexExpr-of-FnCall element-type inference
        # walks Box<Int> → (substitute T→Int) → Array<Int> via the
        # canonicaliser, returns the Int element type, and `[1]`
        # selects 20.
        assert _run_io(source, fn="main") == "20\n"

    def test_e616_apply_fn_unhandled_closure_arg_shape(self) -> None:
        """`apply_fn(make_mapper(()), 7)` where `make_mapper` is a
        FnCall returning a closure — the apply_fn return-type
        dispatcher only recognises `SlotRef` (into a `FnType` alias)
        and inline `AnonFn` literals.  Any other shape (FnCall,
        IfExpr, etc.) used to default the call_indirect sig to
        `i64`, mismatching the actual `i32_pair` (or other) emit
        and producing a WASM-validation trap with no source-located
        diagnostic.

        Closes #632 — the apply_fn / call_indirect parallel of
        #630's interpolation-side `[E615]` work.  Now the failure
        records the offending closure_arg on
        `_apply_fn_inference_failures` and the harvest emits a
        specific `[E616]` before the enclosing fn is dropped via
        `[E602]`.
        """
        source = _IO_PRELUDE + """\
type Maker = fn(Int -> String) effects(pure);

private fn make_mapper(@Unit -> @Maker)
  requires(true) ensures(true) effects(pure)
{ fn(@Int -> @String) effects(pure) { "hello" } }

public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print(apply_fn(make_mapper(()), 7))
}
"""
        result = _compile(source)
        warnings = [
            d for d in result.diagnostics if d.severity == "warning"
        ]
        e616 = [d for d in warnings if d.error_code == "E616"]
        assert e616, (
            f"Expected an [E616] for the unhandled apply_fn "
            f"closure-arg shape; warnings: {warnings}"
        )
        assert "apply_fn" in e616[0].description.lower() or (
            "closure" in e616[0].description.lower()
        ), (
            f"E616 message should mention apply_fn / closure; got: "
            f"{e616[0].description}"
        )
        # E616 must precede the matching E602 in the warnings
        # stream so the specific-cause-then-generic-skip narrative
        # reads correctly per function.  Filter to the E602
        # mentioning `main` so unrelated prelude E602s don't
        # confound (parallel to the E615 ordering assertion in
        # `test_e615_fires_on_adt_in_interpolation`).
        e602_main = [
            d for d in warnings
            if d.error_code == "E602" and "main" in d.description
        ]
        assert e602_main, (
            f"Expected an [E602] for `main` after E616; warnings: "
            f"{warnings}"
        )
        e616_idx = warnings.index(e616[0])
        main_e602_idx = warnings.index(e602_main[0])
        assert e616_idx < main_e602_idx, (
            f"E616 should precede the matching E602 (main) in the "
            f"warnings stream; got E616 at index {e616_idx}, main's "
            f"E602 at {main_e602_idx}"
        )
        # `main` is dropped via [E602] (the call_indirect would
        # have referenced a missing return-type signature).
        assert "main" not in result.exports, (
            f"main should be skipped when apply_fn can't infer "
            f"the closure return type; exports: {result.exports}"
        )

    def test_e635_parameterised_alias_compilability(self) -> None:
        """`type Id<T> = T;` instantiated with a parameterised type
        arg — `private fn make_list(@Unit -> @Id<Array<Int>>)`.
        Pre-fix, `_type_expr_to_wasm_type` (the compilability
        check) recursed on `_type_aliases["Id"] = NamedType("T")`
        without binding `T` to `Array<Int>`, classifying the
        return type as `"unsupported"` and dropping `make_list`
        via `[E605]`.

        Closes #635 — parallel of the walker fix landed in PR #631
        for `_canonical_named_type`, applied to the compilability
        check's separate code path.  The compilability check now
        substitutes parameterised-alias type params via
        `substitute_type_vars` before recursing.
        """
        source = _IO_PRELUDE + """\
type Id<T> = T;

private fn make_list(@Unit -> @Id<Array<Int>>)
  requires(true) ensures(true) effects(pure)
{ [10, 20, 30] }

public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print("\\(make_list(())[1])\\n")
}
"""
        # Runs end-to-end — make_list compiles cleanly via the
        # parameterised-alias substitution, IndexExpr inference
        # walks Id<Array<Int>> → (substitute T→Array<Int>) →
        # Array<Int>, returns Int element type.
        assert _run_io(source, fn="main") == "20\n"

    def test_fntype_return_uses_closure_pointer_abi(self) -> None:
        """A higher-order fn returning a `FnType`-aliased closure
        — `type Outer = fn(Int -> Inner) effects(pure)` where
        `Inner` is itself a `FnType` alias.  Pre-fix
        `_canonical_wasm_type` returned `"i64"` (the walker
        couldn't reach a NamedType, fell to the default), producing
        a `call_indirect` sig mismatch at WASM validation.

        Closes the FnType-return half of the bug class — the
        codegen base's `_type_expr_to_wasm_type` already handled
        FnType correctly via an explicit branch; the inference
        walker's silent default to `"i64"` was the asymmetric gap.

        Fix: `_canonical_wasm_type` falls back to a `_reaches_fn_type`
        check when the walker returns None; if the walk would have
        terminated at a `FnType`, return `"i32"` (closure-pointer
        ABI) instead of the `"i64"` default.

        (CodeRabbit finding 3, third review pass on PR #631.)
        """
        source = _IO_PRELUDE + """\
type Inner = fn(Int -> Int) effects(pure);
type Outer = fn(Int -> Inner) effects(pure);

private fn make_outer(@Unit -> @Outer)
  requires(true) ensures(true) effects(pure)
{
  fn(@Int -> @Inner) effects(pure) {
    fn(@Int -> @Int) effects(pure) { @Int.0 + @Int.1 }
  }
}

public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Outer = make_outer(());
  let @Inner = apply_fn(@Outer.0, 5);
  IO.print(int_to_string(apply_fn(@Inner.0, 3)))
}
"""
        # 5 + 3 = 8; runs end-to-end via correct closure-pointer ABI.
        assert _run_io(source, fn="main") == "8"

    def test_closure_orphans_not_committed_on_partial_fail(
        self,
    ) -> None:
        """When `_lift_pending_closures` fails on any closure in
        the worklist, the parent fn is dropped (#636) — but the
        successful sibling closures must NOT be left in the
        module-level `_closure_fns_wat` / `_closure_table` state,
        otherwise their entries shift table indices for
        *subsequent* top-level fns' closures.

        Concretely: `bad` has one closure that fails E615, `good`
        compiled afterwards has its own closure.  Without
        commit-on-success, `bad`'s would-be orphan would land in
        `_closure_table` and `good`'s closure_id would no longer
        match its actual table index, producing a `call_indirect`
        to the wrong function at runtime.

        Fix: accumulate worklist results in local buffers; only
        extend `_closure_fns_wat` / `_closure_table` /
        `_fn_source_map` / `_closure_sigs` if every closure
        succeeded.

        (CodeRabbit finding 1, third review pass on PR #631.)
        """
        source = _IO_PRELUDE + """\
public fn bad(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Option<Int> = Some(42);
  apply_fn(fn(@Unit -> @Unit) effects(<IO>) {
    IO.print("\\(@Option<Int>.0)\\n")
  }, ())
}

public fn good(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Array<Int> = array_map(
    [10, 20, 30],
    fn(@Int -> @Int) effects(pure) { @Int.0 + 1 }
  );
  IO.print(int_to_string(@Array<Int>.0[1]))
}
"""
        result = _compile(source)
        # `bad` is dropped via the closure-fail propagation (#636).
        assert "bad" not in result.exports, (
            f"bad should be dropped; exports: {result.exports}"
        )
        # `good` must remain — its closure is independent.
        assert "good" in result.exports, (
            f"good should be exported; exports: {result.exports}"
        )
        # Run `good` to confirm its closure references the correct
        # table entry.  Pre-fix `bad`'s orphan closure would have
        # been at table index 0, shifting `good`'s closure to index
        # 1 while its closure_id stored in the closure struct
        # remained 1 (because `_next_closure_id` is module-monotonic)
        # — call_indirect would target index 1 expecting `$anon_1`
        # but actually find `good`'s closure (originally meant for
        # index 1 with $anon_2 closure_id).  In this specific
        # fixture either trap or wrong output; the `_run_io` below
        # exercises the path.
        from vera.codegen import execute
        exec_result = execute(result, fn_name="good")
        # `good` is `Unit`-returning so no value to assert beyond
        # not trapping.
        assert exec_result.value is None or exec_result.value == 0, (
            f"good() should run cleanly; got: {exec_result.value!r}"
        )

    def test_array_map_refinement_returning_closure(self) -> None:
        """`_infer_closure_return_vera_type` in `calls_arrays.py`
        was previously bare-NamedType-only; the #630 migration
        broadened it to handle refinements + alias chains via
        `_canonical_named_type`.  This test pins the broader
        behaviour: an `array_map` over an inline closure whose
        return type is a refinement should compile and execute,
        not silently fail inference.

        Pre-PR-#631-review-pass: no test exercised this path.
        Post-fix: the canonicaliser walks the refinement to its
        base name; `array_map`'s element-type inference returns
        `"String"` and the loop emits the correct String-element
        copy operations.

        (test-analyzer finding C2 on PR #631.)
        """
        source = _IO_PRELUDE + """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Array<String> = array_map(
    [1, 2, 3],
    fn(@Int -> @{ @String | string_length(@String.0) > 0 })
      effects(pure) { "x" }
  );
  IO.print(@Array<String>.0[0])
}
"""
        # Should run cleanly — pre-fix, the closure-return inference
        # silently returned None on the refinement, leading to wrong
        # element size in the array_map loop.
        assert _run_io(source, fn="main") == "x"


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
        """decimal_to_float(decimal_from_float(3.5)) round-trips exactly."""
        source = """
public fn main(-> @Float64)
  requires(true) ensures(true) effects(pure)
{ decimal_to_float(decimal_from_float(3.5)) }
"""
        assert _run_float(source) == 3.5

    def test_decimal_to_string_exact(self) -> None:
        """decimal_to_string renders the correct string."""
        source = _IO_PRELUDE + """
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{ IO.print(decimal_to_string(decimal_from_int(42))) }
"""
        assert _run_io(source, fn="main") == "42"

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

    def test_decimal_from_int_different_values(self) -> None:
        """Two different decimal_from_int values are not equal."""
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

    def test_decimal_add_and_round(self) -> None:
        """decimal_add + decimal_round round-trip."""
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

    def test_decimal_neg_large_value(self) -> None:
        """decimal_neg on a large value: neg(1000000) + 1000000 = 0."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Decimal = decimal_from_int(1000000);
  let @Decimal = decimal_add(decimal_neg(@Decimal.0), @Decimal.0);
  if decimal_eq(@Decimal.0, decimal_from_int(0)) then { 1 } else { 0 }
}
"""
        assert _run(source) == 1

    def test_decimal_div_host_called(self) -> None:
        """decimal_div host import is wired and invoked."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Option<Decimal> = decimal_div(decimal_from_int(10), decimal_from_int(2));
  let @Decimal = option_unwrap_or(@Option<Decimal>.0, decimal_from_int(0));
  if decimal_eq(@Decimal.0, decimal_from_int(5)) then { 1 } else { 0 }
}
"""
        result = _compile_ok(source)
        assert '"decimal_div"' in result.wat
        assert _run(source) == 1

    def test_decimal_from_string_host_called(self) -> None:
        """decimal_from_string host import is wired and invoked."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Option<Decimal> = decimal_from_string("42");
  match @Option<Decimal>.0 {
    None -> 0,
    Some(@Decimal) -> if decimal_eq(@Decimal.0, decimal_from_int(42)) then { 1 } else { 0 }
  }
}
"""
        result = _compile_ok(source)
        assert '"decimal_from_string"' in result.wat
        assert _run(source) == 1

    def test_decimal_compare_host_called(self) -> None:
        """decimal_compare host import is wired and invoked."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Ordering = decimal_compare(decimal_from_int(1), decimal_from_int(2));
  match @Ordering.0 {
    Less -> 1,
    Equal -> 0,
    Greater -> 0
  }
}
"""
        result = _compile_ok(source)
        assert '"decimal_compare"' in result.wat
        assert _run(source) == 1

    def test_decimal_compare_equal_and_greater(self) -> None:
        """decimal_compare equal and greater branches (coverage)."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Ordering = decimal_compare(decimal_from_int(5), decimal_from_int(5));
  let @Int = match @Ordering.0 {
    Less -> 0,
    Equal -> 1,
    Greater -> 0
  };
  let @Ordering = decimal_compare(decimal_from_int(10), decimal_from_int(3));
  let @Int = match @Ordering.0 {
    Less -> 0,
    Equal -> 0,
    Greater -> 1
  };
  @Int.1 + @Int.0
}
"""
        assert _run(source) == 2

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

    def test_decimal_chained_arithmetic(self) -> None:
        """Chained decimal ops exercise WASM type inference paths."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  if decimal_eq(
    decimal_add(decimal_from_int(1), decimal_from_int(2)),
    decimal_from_int(3))
  then { 1 } else { 0 }
}
"""
        assert _run(source) == 1

    def test_decimal_to_float_chained(self) -> None:
        """decimal_to_float result feeds into floor (f64 inference)."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ floor(decimal_to_float(decimal_add(decimal_from_int(3), decimal_from_int(4)))) }
"""
        assert _run(source) == 7

    def test_decimal_to_string_chained(self) -> None:
        """decimal_to_string result feeds into string_length (i32_pair inference)."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ string_length(decimal_to_string(decimal_add(decimal_from_int(1), decimal_from_int(2)))) }
"""
        assert _run(source) == 1

    def test_decimal_eq_chained(self) -> None:
        """decimal_eq result feeds into if (Bool/i32 inference)."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Bool = decimal_eq(decimal_from_int(5), decimal_from_int(5));
  if @Bool.0 then { 1 } else { 0 }
}
"""
        assert _run(source) == 1

    def test_decimal_if_expr_result_type(self) -> None:
        """Decimal in if-expression exercises _infer_block_result_type."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Decimal = if decimal_eq(decimal_from_int(1), decimal_from_int(1))
    then { decimal_from_int(42) }
    else { decimal_from_int(0) };
  if decimal_eq(@Decimal.0, decimal_from_int(42)) then { 1 } else { 0 }
}
"""
        assert _run(source) == 1

    def test_map_if_expr_result_type(self) -> None:
        """Map handle in if-expression exercises _infer_block_result_type."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Map<String, Int> = if 1 == 1
    then { map_insert(map_new(), "a", 1) }
    else { map_new() };
  map_size(@Map<String, Int>.0)
}
"""
        assert _run(source) == 1

    def test_set_if_expr_result_type(self) -> None:
        """Set handle in if-expression exercises _infer_block_result_type."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Set<Int> = if 1 == 1
    then { set_add(set_new(), 42) }
    else { set_new() };
  set_size(@Set<Int>.0)
}
"""
        assert _run(source) == 1

    def test_decimal_if_expr_else_branch(self) -> None:
        """Decimal if-expr else branch is exercised."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Decimal = if 1 == 2
    then { decimal_from_int(99) }
    else { decimal_from_int(0) };
  if decimal_eq(@Decimal.0, decimal_from_int(0)) then { 1 } else { 0 }
}
"""
        assert _run(source) == 1

    def test_map_if_expr_else_branch(self) -> None:
        """Map if-expr else branch returns empty map."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Map<String, Int> = if 1 == 2
    then { map_insert(map_new(), "a", 1) }
    else { map_new() };
  map_size(@Map<String, Int>.0)
}
"""
        assert _run(source) == 0

    def test_set_if_expr_else_branch(self) -> None:
        """Set if-expr else branch returns empty set."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Set<Int> = if 1 == 2
    then { set_add(set_new(), 42) }
    else { set_new() };
  set_size(@Set<Int>.0)
}
"""
        assert _run(source) == 0

    def test_map_get_in_if_expr(self) -> None:
        """map_get result type inferred in if-expression context."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Map<String, Int> = map_insert(map_new(), "k", 42);
  let @Option<Int> = if 1 == 1
    then { map_get(@Map<String, Int>.0, "k") }
    else { None };
  option_unwrap_or(@Option<Int>.0, 0)
}
"""
        assert _run(source) == 42

    def test_map_size_in_if_expr(self) -> None:
        """map_size result type (i64) inferred in if-expression."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Map<String, Int> = map_insert(map_new(), "k", 1);
  if map_size(@Map<String, Int>.0) == 1 then { 1 } else { 0 }
}
"""
        assert _run(source) == 1

    def test_set_contains_in_if_expr(self) -> None:
        """set_contains result type (i32) inferred in if-expression."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Set<Int> = set_add(set_new(), 7);
  if set_contains(@Set<Int>.0, 7) then { 1 } else { 0 }
}
"""
        assert _run(source) == 1

    def test_map_keys_in_if_expr(self) -> None:
        """map_keys result type (i32_pair) inferred in if-expression."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Map<String, Int> = map_insert(map_new(), "x", 1);
  let @Array<String> = if 1 == 1
    then { map_keys(@Map<String, Int>.0) }
    else { map_keys(map_new()) };
  array_length(@Array<String>.0)
}
"""
        assert _run(source) == 1

    def test_set_to_array_in_if_expr(self) -> None:
        """set_to_array result type (i32_pair) inferred in if-expression."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Set<Int> = set_add(set_new(), 5);
  let @Array<Int> = if 1 == 1
    then { set_to_array(@Set<Int>.0) }
    else { set_to_array(set_new()) };
  array_length(@Array<Int>.0)
}
"""
        assert _run(source) == 1

    def test_map_contains_in_if_expr(self) -> None:
        """map_contains in if-expression exercises Bool inference."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Map<String, Int> = map_insert(map_new(), "k", 1);
  if map_contains(@Map<String, Int>.0, "k") then { 1 } else { 0 }
}
"""
        assert _run(source) == 1

    def test_set_size_in_if_expr(self) -> None:
        """set_size result type (i64) inferred in if-expression."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Set<Int> = set_add(set_add(set_new(), 1), 2);
  if set_size(@Set<Int>.0) == 2 then { 1 } else { 0 }
}
"""
        assert _run(source) == 1


class TestJsonCollection:
    """Json ADT built-in operations: json_parse, json_stringify,
    json_get, json_has_field, json_array_length, json_keys, json_type."""

    def test_json_parse_wat_import(self) -> None:
        """json_parse generates a WASM host import."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Result<Json, String> = json_parse("null");
  1
}
"""
        result = _compile_ok(source)
        assert '"json_parse"' in result.wat

    def test_json_stringify_wat_import(self) -> None:
        """json_stringify generates a WASM host import."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ string_length(json_stringify(JNull)) }
"""
        result = _compile_ok(source)
        assert '"json_stringify"' in result.wat

    def test_json_no_imports_when_unused(self) -> None:
        """Programs not using json_parse/json_stringify have no Json imports."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ json_array_length(JNull) }
"""
        result = _compile_ok(source)
        assert '"json_parse"' not in result.wat
        assert '"json_stringify"' not in result.wat

    def test_json_null_array_length(self) -> None:
        """json_array_length(JNull) returns 0."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ json_array_length(JNull) }
"""
        assert _run(source) == 0

    def test_json_type_null(self) -> None:
        """json_type(JNull) returns 'null'."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ if string_contains(json_type(JNull), "null") then { string_length(json_type(JNull)) } else { 0 } }
"""
        assert _run(source) == 4

    def test_json_type_bool(self) -> None:
        """json_type(JBool(true)) returns 'bool'."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ if string_contains(json_type(JBool(true)), "bool") then { string_length(json_type(JBool(true))) } else { 0 } }
"""
        assert _run(source) == 4

    def test_json_type_number(self) -> None:
        """json_type(JNumber(0.0)) returns 'number'."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ if string_contains(json_type(JNumber(0.0)), "number") then { string_length(json_type(JNumber(0.0))) } else { 0 } }
"""
        assert _run(source) == 6

    def test_json_type_string(self) -> None:
        """json_type(JString('hi')) returns 'string'."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ if string_contains(json_type(JString("hi")), "string") then { string_length(json_type(JString("hi"))) } else { 0 } }
"""
        assert _run(source) == 6

    def test_json_type_array(self) -> None:
        """json_type(JArray([])) returns 'array'."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ if string_contains(json_type(JArray([])), "array") then { string_length(json_type(JArray([]))) } else { 0 } }
"""
        assert _run(source) == 5

    def test_json_type_object(self) -> None:
        """json_type(JObject(map_new())) returns 'object'."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ if string_contains(json_type(JObject(map_new())), "object") then { string_length(json_type(JObject(map_new()))) } else { 0 } }
"""
        assert _run(source) == 6

    def test_json_array_length(self) -> None:
        """JArray with 3 elements has length 3."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ json_array_length(JArray([JNull, JBool(true), JNumber(1.0)])) }
"""
        assert _run(source) == 3

    def test_json_parse_array(self) -> None:
        """json_parse('[1,2,3]') returns array of length 3."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Result<Json, String> = json_parse("[1, 2, 3]");
  match @Result<Json, String>.0 {
    Ok(@Json) -> json_array_length(@Json.0),
    Err(@String) -> 0
  }
}
"""
        assert _run(source) == 3

    def test_json_parse_object(self) -> None:
        """json_parse('{"a":1}') returns object with field 'a'."""
        source = '''
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Result<Json, String> = json_parse("{\\"a\\": 1}");
  match @Result<Json, String>.0 {
    Ok(@Json) -> if json_has_field(@Json.0, "a") then { 1 } else { 0 },
    Err(@String) -> 0
  }
}
'''
        assert _run(source) == 1

    def test_json_parse_invalid(self) -> None:
        """json_parse with invalid JSON returns Err."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Result<Json, String> = json_parse("not json");
  match @Result<Json, String>.0 {
    Ok(@Json) -> 0,
    Err(@String) -> 1
  }
}
"""
        assert _run(source) == 1

    def test_json_stringify_null(self) -> None:
        """json_stringify(JNull) returns 'null' (length 4)."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ string_length(json_stringify(JNull)) }
"""
        assert _run(source) == 4

    def test_json_stringify_bool(self) -> None:
        """json_stringify(JBool(true)) returns 'true' (length 4)."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ string_length(json_stringify(JBool(true))) }
"""
        assert _run(source) == 4

    def test_json_stringify_number(self) -> None:
        """json_stringify(JNumber(42.0)) returns '42.0' (length 4)."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ string_length(json_stringify(JNumber(42.0))) }
"""
        assert _run(source) == 4

    def test_json_get_present(self) -> None:
        """json_get on JObject with present key returns Some."""
        source = '''
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Result<Json, String> = json_parse("{\\"count\\": 42}");
  match @Result<Json, String>.0 {
    Ok(@Json) ->
      match json_get(@Json.0, "count") {
        Some(@Json) ->
          match @Json.0 {
            JNumber(@Float64) -> floor(@Float64.0),
            JNull -> 0,
            JBool(@Bool) -> 0,
            JString(@String) -> 0,
            JArray(@Array<Json>) -> 0,
            JObject(@Map<String, Json>) -> 0
          },
        None -> 0
      },
    Err(@String) -> 0
  }
}
'''
        assert _run(source) == 42

    def test_json_get_absent(self) -> None:
        """json_get on JObject with absent key returns None."""
        source = '''
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Result<Json, String> = json_parse("{\\"a\\": 1}");
  match @Result<Json, String>.0 {
    Ok(@Json) ->
      match json_get(@Json.0, "missing") {
        Some(@Json) -> 0,
        None -> 1
      },
    Err(@String) -> 0
  }
}
'''
        assert _run(source) == 1

    def test_json_keys(self) -> None:
        """json_keys on JObject returns array of key strings."""
        source = '''
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Result<Json, String> = json_parse("{\\"a\\": 1, \\"b\\": 2}");
  match @Result<Json, String>.0 {
    Ok(@Json) -> array_length(json_keys(@Json.0)),
    Err(@String) -> 0
  }
}
'''
        assert _run(source) == 2

    def test_json_has_field_false(self) -> None:
        """json_has_field on JNull returns false."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ if json_has_field(JNull, "x") then { 1 } else { 0 } }
"""
        assert _run(source) == 0

    def test_json_array_get_present(self) -> None:
        """json_array_get on JArray with valid index returns Some."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Json = JArray([JNumber(10.0), JNumber(20.0)]);
  match json_array_get(@Json.0, 1) {
    Some(@Json) ->
      match @Json.0 {
        JNumber(@Float64) -> floor(@Float64.0),
        JNull -> 0,
        JBool(@Bool) -> 0,
        JString(@String) -> 0,
        JArray(@Array<Json>) -> 0,
        JObject(@Map<String, Json>) -> 0
      },
    None -> 0
  }
}
"""
        assert _run(source) == 20

    def test_json_custom_data_no_combinators(self) -> None:
        """User-defined non-standard data Json skips combinator injection."""
        source = """
private data Json { MyNode(Int) }
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Json = MyNode(42);
  match @Json.0 {
    MyNode(@Int) -> @Int.0
  }
}
"""
        assert _run(source) == 42

    def test_json_array_get_out_of_bounds(self) -> None:
        """json_array_get with out-of-bounds index returns None."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Json = JArray([JNull]);
  match json_array_get(@Json.0, 5) {
    Some(@Json) -> 0,
    None -> 1
  }
}
"""
        assert _run(source) == 1

    def test_json_array_get_negative_index(self) -> None:
        """json_array_get with negative index returns None."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Json = JArray([JNull, JBool(true)]);
  match json_array_get(@Json.0, 0 - 1) {
    Some(@Json) -> 0,
    None -> 1
  }
}
"""
        assert _run(source) == 1

    def test_json_stringify_object(self) -> None:
        """json_stringify(JObject(...)) round-trips through read_json."""
        source = '''
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Json = JObject(map_insert(map_new(), "k", JNumber(1.0)));
  string_length(json_stringify(@Json.0))
}
'''
        result = _run(source)
        assert result > 0

    def test_json_stringify_array(self) -> None:
        """json_stringify(JArray([...])) exercises read_json array path."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Json = JArray([JNull, JBool(true), JNumber(2.0)]);
  string_length(json_stringify(@Json.0))
}
"""
        result = _run(source)
        assert result > 0

    def test_json_stringify_string(self) -> None:
        """json_stringify(JString(...)) exercises read_json string path."""
        source = '''
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ string_length(json_stringify(JString("hello"))) }
'''
        result = _run(source)
        assert result > 0

    def test_json_stringify_bool_false(self) -> None:
        """json_stringify(JBool(false)) returns 'false' (5 chars)."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ string_length(json_stringify(JBool(false))) }
"""
        assert _run(source) == 5

    def test_json_stringify_number_negative(self) -> None:
        """json_stringify(JNumber(-3.5)) exercises read_json f64 path."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ string_length(json_stringify(JNumber(0.0 - 3.5))) }
"""
        result = _run(source)
        assert result > 0

    def test_json_parse_with_string_values(self) -> None:
        """json_parse with string values exercises write_json string path."""
        source = '''
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Result<Json, String> = json_parse("{\\"name\\": \\"Alice\\"}");
  match @Result<Json, String>.0 {
    Ok(@Json) -> if json_has_field(@Json.0, "name") then { 1 } else { 0 },
    Err(@String) -> 0
  }
}
'''
        assert _run(source) == 1

    def test_json_parse_nested_object(self) -> None:
        """json_parse with nested objects exercises write_json object path."""
        source = '''
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Result<Json, String> = json_parse("{\\"inner\\": {\\"x\\": 1}}");
  match @Result<Json, String>.0 {
    Ok(@Json) ->
      match json_get(@Json.0, "inner") {
        Some(@Json) -> if json_has_field(@Json.0, "x") then { 1 } else { 0 },
        None -> 0
      },
    Err(@String) -> 0
  }
}
'''
        assert _run(source) == 1

    def test_json_parse_stringify_roundtrip(self) -> None:
        """Parse then stringify exercises both write_json and read_json."""
        source = '''
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Result<Json, String> = json_parse("[1, true, null]");
  match @Result<Json, String>.0 {
    Ok(@Json) -> string_length(json_stringify(@Json.0)),
    Err(@String) -> 0
  }
}
'''
        result = _run(source)
        assert result > 0


class TestHtmlCollection:
    """HtmlNode ADT built-in operations: html_parse, html_to_string,
    html_query, html_text, html_attr."""

    def test_html_parse_valid(self) -> None:
        """html_parse of valid HTML returns Ok."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Result<HtmlNode, String> = html_parse("<p>hello</p>");
  match @Result<HtmlNode, String>.0 {
    Ok(@HtmlNode) -> 1,
    Err(@String) -> 0
  }
}
"""
        assert _run(source) == 1

    def test_html_text_extraction(self) -> None:
        """html_text extracts text content from parsed HTML."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Result<HtmlNode, String> = html_parse("<p>hello</p>");
  match @Result<HtmlNode, String>.0 {
    Ok(@HtmlNode) -> string_length(html_text(@HtmlNode.0)),
    Err(@String) -> 0
  }
}
"""
        assert _run(source) == 5

    def test_html_to_string_roundtrip(self) -> None:
        """html_to_string serializes back to HTML."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Result<HtmlNode, String> = html_parse("<p>hi</p>");
  match @Result<HtmlNode, String>.0 {
    Ok(@HtmlNode) -> string_length(html_to_string(@HtmlNode.0)),
    Err(@String) -> 0
  }
}
"""
        assert _run(source) > 0

    def test_html_query_by_tag(self) -> None:
        """html_query finds elements by tag name."""
        source = '''
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Result<HtmlNode, String> = html_parse("<div><p>a</p><p>b</p></div>");
  match @Result<HtmlNode, String>.0 {
    Ok(@HtmlNode) -> array_length(html_query(@HtmlNode.0, "p")),
    Err(@String) -> 0
  }
}
'''
        assert _run(source) == 2

    def test_html_attr_present(self) -> None:
        """html_attr returns Some for present attributes."""
        source = '''
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Result<HtmlNode, String> = html_parse("<a href=\\"url\\">link</a>");
  match @Result<HtmlNode, String>.0 {
    Ok(@HtmlNode) -> match html_attr(@HtmlNode.0, "href") {
      Some(@String) -> string_length(@String.0),
      None -> 0
    },
    Err(@String) -> 0 - 1
  }
}
'''
        assert _run(source) == 3

    def test_html_attr_absent(self) -> None:
        """html_attr returns None for missing attributes."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Result<HtmlNode, String> = html_parse("<p>text</p>");
  match @Result<HtmlNode, String>.0 {
    Ok(@HtmlNode) -> match html_attr(@HtmlNode.0, "class") {
      Some(@String) -> 1,
      None -> 0
    },
    Err(@String) -> 0 - 1
  }
}
"""
        assert _run(source) == 0

    def test_html_parse_invalid(self) -> None:
        """Malformed HTML still parses leniently (best-effort)."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Result<HtmlNode, String> = html_parse("<p>unclosed");
  match @Result<HtmlNode, String>.0 {
    Ok(@HtmlNode) -> 1,
    Err(@String) -> 0
  }
}
"""
        assert _run(source) == 1

    def test_html_parse_wat_import(self) -> None:
        """html_parse generates a WASM host import."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Result<HtmlNode, String> = html_parse("<p>x</p>");
  1
}
"""
        result = _compile_ok(source)
        assert '"html_parse"' in result.wat
        assert '"html_to_string"' not in result.wat
        assert '"html_query"' not in result.wat
        assert '"html_text"' not in result.wat

    def test_html_to_string_wat_import(self) -> None:
        """html_to_string generates a WASM host import."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ string_length(html_to_string(HtmlText("x"))) }
"""
        result = _compile_ok(source)
        assert '"html_to_string"' in result.wat
        assert '"html_parse"' not in result.wat
        assert '"html_query"' not in result.wat
        assert '"html_text"' not in result.wat

    def test_html_query_wat_import(self) -> None:
        """html_query generates a WASM host import without html_parse."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ array_length(html_query(HtmlElement("div", map_new(), [HtmlText("x")]), "div")) }
"""
        result = _compile_ok(source)
        assert '"html_query"' in result.wat
        assert '"html_parse"' not in result.wat
        assert '"html_to_string"' not in result.wat
        assert '"html_text"' not in result.wat

    def test_html_text_wat_import(self) -> None:
        """html_text generates a WASM host import."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ string_length(html_text(HtmlText("hello"))) }
"""
        result = _compile_ok(source)
        assert '"html_text"' in result.wat
        assert '"html_parse"' not in result.wat
        assert '"html_to_string"' not in result.wat
        assert '"html_query"' not in result.wat

    def test_html_query_by_class(self) -> None:
        """html_query with class selector."""
        source = '''
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Result<HtmlNode, String> = html_parse("<div class=\\"foo\\">a</div><div>b</div>");
  match @Result<HtmlNode, String>.0 {
    Ok(@HtmlNode) -> array_length(html_query(@HtmlNode.0, ".foo")),
    Err(@String) -> 0
  }
}
'''
        assert _run(source) == 1

    def test_html_query_by_id(self) -> None:
        """html_query with ID selector."""
        source = '''
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Result<HtmlNode, String> = html_parse("<p id=\\"main\\">hi</p><p>bye</p>");
  match @Result<HtmlNode, String>.0 {
    Ok(@HtmlNode) -> array_length(html_query(@HtmlNode.0, "#main")),
    Err(@String) -> 0
  }
}
'''
        assert _run(source) == 1

    def test_html_query_descendant(self) -> None:
        """html_query with descendant selector."""
        source = '''
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Result<HtmlNode, String> = html_parse("<div><p>a</p><p>b</p></div><p>c</p>");
  match @Result<HtmlNode, String>.0 {
    Ok(@HtmlNode) -> array_length(html_query(@HtmlNode.0, "div p")),
    Err(@String) -> 0
  }
}
'''
        assert _run(source) == 2

    def test_html_no_imports_when_unused(self) -> None:
        """Programs not using html builtins have no Html imports."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ 42 }
"""
        result = _compile_ok(source)
        assert '"html_parse"' not in result.wat
        assert '"html_to_string"' not in result.wat
        assert '"html_query"' not in result.wat
        assert '"html_text"' not in result.wat

    def test_html_comment_roundtrip(self) -> None:
        """HtmlComment serializes to <!-- ... --> via html_to_string."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ string_length(html_to_string(HtmlComment("a comment"))) }
"""
        # "<!--a comment-->" = 16 chars
        assert _run(source) == 16

    def test_html_text_escaping(self) -> None:
        """html_to_string escapes & < > in text content."""
        source = '''
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ string_length(html_to_string(HtmlText("a&b"))) }
'''
        # "a&amp;b" = 7 chars
        assert _run(source) == 7

    def test_html_attr_value_escaping(self) -> None:
        """html_to_string escapes quotes in attribute values."""
        source = '''
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Map<String, String> = map_insert(map_new(), "title", "a\\"b");
  string_length(html_to_string(HtmlElement("p", @Map<String, String>.0, [])))
}
'''
        # <p title="a&quot;b"></p> = 24 chars (quote escaped as &quot;)
        assert _run(source) == 24

    def test_html_query_attr_selector(self) -> None:
        """html_query with attribute presence selector [href]."""
        source = '''
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Result<HtmlNode, String> = html_parse("<a href=\\"x\\">link</a><span>no</span>");
  match @Result<HtmlNode, String>.0 {
    Ok(@HtmlNode) -> array_length(html_query(@HtmlNode.0, "[href]")),
    Err(@String) -> 0
  }
}
'''
        assert _run(source) == 1

    def test_html_parse_with_attributes(self) -> None:
        """Parsed element attributes are accessible via html_query + html_attr."""
        source = '''
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Result<HtmlNode, String> = html_parse("<div class=\\"main\\">content</div>");
  match @Result<HtmlNode, String>.0 {
    Ok(@HtmlNode) -> {
      let @Array<HtmlNode> = html_query(@HtmlNode.0, ".main");
      if array_length(@Array<HtmlNode>.0) > 0 then {
        match @Array<HtmlNode>.0[0] {
          HtmlElement(@String, @Map<String, String>, @Array<HtmlNode>) ->
            match map_get(@Map<String, String>.0, "class") {
              Some(@String) -> string_length(@String.0),
              None -> 0
            },
          HtmlText(@String) -> 0,
          HtmlComment(@String) -> 0
        }
      } else { 0 }
    },
    Err(@String) -> 0
  }
}
'''
        # "main" = 4 chars
        assert _run(source) == 4

    def test_html_void_element(self) -> None:
        """Void elements (br, img) serialize without closing tag."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ string_length(html_to_string(HtmlElement("br", map_new(), []))) }
"""
        # "<br>" = 4 chars
        assert _run(source) == 4

    def test_html_parse_comment_roundtrip(self) -> None:
        """Parsed HTML comments survive roundtrip through html_to_string."""
        source = '''
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Result<HtmlNode, String> = html_parse("<!-- hello --><p>text</p>");
  match @Result<HtmlNode, String>.0 {
    Ok(@HtmlNode) -> string_length(html_to_string(@HtmlNode.0)),
    Err(@String) -> 0
  }
}
'''
        result = _run(source)
        assert result > 0  # roundtrip produces non-empty HTML

    def test_html_query_empty_result(self) -> None:
        """html_query with no matches returns empty array."""
        source = '''
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Result<HtmlNode, String> = html_parse("<p>hello</p>");
  match @Result<HtmlNode, String>.0 {
    Ok(@HtmlNode) -> array_length(html_query(@HtmlNode.0, "div")),
    Err(@String) -> 0 - 1
  }
}
'''
        assert _run(source) == 0

    def test_html_nested_elements(self) -> None:
        """html_text extracts text from nested elements."""
        source = '''
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Result<HtmlNode, String> = html_parse("<div><span>hello</span> <em>world</em></div>");
  match @Result<HtmlNode, String>.0 {
    Ok(@HtmlNode) -> string_length(html_text(@HtmlNode.0)),
    Err(@String) -> 0
  }
}
'''
        result = _run(source)
        assert result > 0  # extracts "hello world" text


class TestHttpCollection:
    """Http effect: host-import compilation and mocked execution."""

    def test_http_get_compiles(self) -> None:
        """Http.get generates a WASM host import."""
        source = """
public fn fetch(@String -> @Result<String, String>)
  requires(true) ensures(true) effects(<Http>)
{ Http.get(@String.0) }
"""
        result = _compile_ok(source)
        assert '"http_get"' in result.wat

    def test_http_post_compiles(self) -> None:
        """Http.post generates a WASM host import."""
        source = """
public fn post(@String, @String -> @Result<String, String>)
  requires(true) ensures(true) effects(<Http>)
{ Http.post(@String.0, @String.1) }
"""
        result = _compile_ok(source)
        assert '"http_post"' in result.wat

    def test_http_get_only_imports_get(self) -> None:
        """Program using only Http.get does not import http_post."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(<Http>)
{
  let @Result<String, String> = Http.get("http://example.com");
  42
}
"""
        result = _compile_ok(source)
        assert '"http_get"' in result.wat
        assert '"http_post"' not in result.wat

    def test_http_post_only_imports_post(self) -> None:
        """Program using only Http.post does not import http_get."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(<Http>)
{
  let @Result<String, String> = Http.post("http://example.com", "body");
  42
}
"""
        result = _compile_ok(source)
        assert '"http_post"' in result.wat
        assert '"http_get"' not in result.wat

    def test_http_no_imports_when_unused(self) -> None:
        """Program without Http has no http imports."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ 42 }
"""
        result = _compile_ok(source)
        assert '"http_get"' not in result.wat
        assert '"http_post"' not in result.wat

    def test_http_declared_but_unused(self) -> None:
        """effects(<Http>) declared but no Http ops used — no imports."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(<Http>)
{ 42 }
"""
        result = _compile_ok(source)
        assert '"http_get"' not in result.wat
        assert '"http_post"' not in result.wat

    def test_http_get_mocked_success(self) -> None:
        """Mocked Http.get returns Ok with response body."""
        from unittest.mock import MagicMock, patch

        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(<Http>)
{
  let @Result<String, String> = Http.get("http://example.com");
  match @Result<String, String>.0 {
    Ok(@String) -> string_length(@String.0),
    Err(@String) -> 0
  }
}
"""
        result = _compile_ok(source)
        mock_resp = MagicMock()
        mock_resp.read.return_value = b"hello"
        mock_resp.__enter__ = lambda s: s
        mock_resp.__exit__ = MagicMock(return_value=False)
        with patch("urllib.request.urlopen", return_value=mock_resp):
            exec_result = execute(result)
            assert exec_result.value == 5

    def test_http_get_mocked_failure(self) -> None:
        """Mocked Http.get failure returns Err."""
        from unittest.mock import patch

        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(<Http>)
{
  let @Result<String, String> = Http.get("http://example.com");
  match @Result<String, String>.0 {
    Ok(@String) -> 0,
    Err(@String) -> string_length(@String.0)
  }
}
"""
        result = _compile_ok(source)
        with patch(
            "urllib.request.urlopen",
            side_effect=Exception("connection refused"),
        ):
            exec_result = execute(result)
            assert exec_result.value is not None
            assert exec_result.value > 0

    def test_http_post_mocked(self) -> None:
        """Mocked Http.post returns Ok with response body."""
        from unittest.mock import MagicMock, patch

        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(<Http>)
{
  let @Result<String, String> = Http.post("http://example.com", "data");
  match @Result<String, String>.0 {
    Ok(@String) -> string_length(@String.0),
    Err(@String) -> 0
  }
}
"""
        result = _compile_ok(source)
        mock_resp = MagicMock()
        mock_resp.read.return_value = b"created"
        mock_resp.__enter__ = lambda s: s
        mock_resp.__exit__ = MagicMock(return_value=False)
        with patch("urllib.request.urlopen", return_value=mock_resp):
            exec_result = execute(result)
            assert exec_result.value == 7


class TestInferenceCollection:
    """Inference effect: host-import compilation and mocked execution."""

    _CLASSIFY_SOURCE = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(<Inference>)
{
  let @Result<String, String> = Inference.complete("Is this positive?");
  match @Result<String, String>.0 {
    Ok(@String) -> string_length(@String.0),
    Err(@String) -> 0
  }
}
"""

    def test_inference_complete_compiles(self) -> None:
        """Inference.complete generates a WASM host import."""
        result = _compile_ok(self._CLASSIFY_SOURCE)
        assert '"inference_complete"' in result.wat

    def test_inference_no_import_when_unused(self) -> None:
        """Program without Inference has no inference_complete import."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ 42 }
"""
        result = _compile_ok(source)
        assert '"inference_complete"' not in result.wat

    def test_inference_declared_but_unused(self) -> None:
        """effects(<Inference>) declared but no Inference ops used — no import."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(<Inference>)
{ 42 }
"""
        result = _compile_ok(source)
        assert '"inference_complete"' not in result.wat

    def test_inference_complete_mocked_success(self) -> None:
        """Mocked Inference.complete returns Ok with completion."""
        from unittest.mock import patch

        result = _compile_ok(self._CLASSIFY_SOURCE)
        with patch(
            "vera.codegen.api._call_inference_provider",
            return_value="Positive",
        ):
            exec_result = execute(result, env_vars={"VERA_ANTHROPIC_API_KEY": "sk-test"})
            assert exec_result.value == 8  # len("Positive")

    def test_inference_complete_mocked_failure(self) -> None:
        """Mocked Inference.complete raises exception — returns Err."""
        from unittest.mock import patch

        result = _compile_ok(self._CLASSIFY_SOURCE)
        with patch(
            "vera.codegen.api._call_inference_provider",
            side_effect=Exception("timeout"),
        ):
            exec_result = execute(result, env_vars={"VERA_ANTHROPIC_API_KEY": "sk-test"})
            assert exec_result.value == 0  # Err branch returns 0

    def test_inference_no_api_key_returns_err(self) -> None:
        """Inference.complete with no API key configured returns Err."""
        result = _compile_ok(self._CLASSIFY_SOURCE)
        exec_result = execute(result, env_vars={})
        assert exec_result.value == 0  # Err branch returns 0

    def test_inference_openai_auto_detect(self) -> None:
        """OpenAI key auto-detected when no VERA_INFERENCE_PROVIDER set."""
        from unittest.mock import patch

        result = _compile_ok(self._CLASSIFY_SOURCE)
        with patch(
            "vera.codegen.api._call_inference_provider",
            return_value="Positive",
        ) as mock_provider:
            exec_result = execute(result, env_vars={"VERA_OPENAI_API_KEY": "sk-openai-test"})
            assert exec_result.value == 8  # len("Positive")
            assert mock_provider.call_args[0][0] == "openai"

    def test_inference_moonshot_auto_detect(self) -> None:
        """Moonshot key auto-detected when no other keys are set."""
        from unittest.mock import patch

        result = _compile_ok(self._CLASSIFY_SOURCE)
        with patch(
            "vera.codegen.api._call_inference_provider",
            return_value="Neutral",
        ) as mock_provider:
            exec_result = execute(result, env_vars={"VERA_MOONSHOT_API_KEY": "sk-moonshot-test"})
            assert exec_result.value == 7  # len("Neutral")
            assert mock_provider.call_args[0][0] == "moonshot"

    def test_inference_explicit_provider_override(self) -> None:
        """VERA_INFERENCE_PROVIDER overrides auto-detection."""
        from unittest.mock import patch

        result = _compile_ok(self._CLASSIFY_SOURCE)
        with patch(
            "vera.codegen.api._call_inference_provider",
            return_value="ok",
        ) as mock_provider:
            execute(result, env_vars={
                "VERA_ANTHROPIC_API_KEY": "sk-ant-test",
                "VERA_OPENAI_API_KEY": "sk-openai-test",
                "VERA_INFERENCE_PROVIDER": "openai",
            })
            assert mock_provider.call_args[0][0] == "openai"


class TestInferenceProviderDispatch:
    """Unit tests for _call_inference_provider — covers all provider branches."""

    def _make_response(self, body: str) -> object:
        """Build a minimal mock urllib response."""
        from unittest.mock import MagicMock
        resp = MagicMock()
        resp.read.return_value = body.encode("utf-8")
        resp.__enter__ = lambda s: s
        resp.__exit__ = MagicMock(return_value=False)
        return resp

    def test_anthropic_provider(self) -> None:
        """Anthropic branch uses correct endpoint, headers, and request body shape."""
        import json
        from unittest.mock import patch, MagicMock
        from vera.codegen.api import _call_inference_provider

        body = json.dumps({"content": [{"text": "hello"}]})
        mock_urlopen = MagicMock(return_value=self._make_response(body))
        with patch("urllib.request.urlopen", mock_urlopen):
            result = _call_inference_provider("anthropic", "prompt", "", "sk-ant")
        assert result == "hello"
        req = mock_urlopen.call_args[0][0]
        assert req.full_url == "https://api.anthropic.com/v1/messages"
        # Anthropic-style auth: x-api-key header, not Bearer
        assert req.get_header("X-api-key") == "sk-ant"
        assert req.get_header("Anthropic-version") == "2023-06-01"
        assert req.get_header("Authorization") is None
        sent_body = json.loads(req.data.decode())
        # Anthropic body: includes max_tokens; no "choices" key
        assert "max_tokens" in sent_body
        assert "messages" in sent_body
        assert sent_body["max_tokens"] == 1024

    def test_openai_provider(self) -> None:
        """OpenAI branch uses correct endpoint, bearer auth, and OpenAI-compatible body."""
        import json
        from unittest.mock import patch, MagicMock
        from vera.codegen.api import _call_inference_provider, _PROVIDERS

        body = json.dumps({"choices": [{"message": {"content": "world"}}]})
        mock_urlopen = MagicMock(return_value=self._make_response(body))
        with patch("urllib.request.urlopen", mock_urlopen):
            result = _call_inference_provider("openai", "prompt", "", "sk-openai")
        assert result == "world"
        req = mock_urlopen.call_args[0][0]
        assert req.full_url == _PROVIDERS["openai"].url
        # Bearer auth, not Anthropic-style key header
        assert req.get_header("Authorization") == "Bearer sk-openai"
        assert req.get_header("X-api-key") is None
        assert req.get_header("Content-type") == "application/json"
        sent_body = json.loads(req.data.decode())
        assert sent_body["model"] == _PROVIDERS["openai"].default_model
        assert "messages" in sent_body
        assert "max_tokens" not in sent_body

    def test_moonshot_provider(self) -> None:
        """Moonshot branch uses correct endpoint, default model, OpenAI-compatible format."""
        import json
        from unittest.mock import patch, MagicMock
        from vera.codegen.api import _call_inference_provider

        body = json.dumps({"choices": [{"message": {"content": "moonshot"}}]})
        mock_urlopen = MagicMock(return_value=self._make_response(body))
        with patch("urllib.request.urlopen", mock_urlopen):
            result = _call_inference_provider("moonshot", "prompt", "", "sk-moon")
        assert result == "moonshot"
        req = mock_urlopen.call_args[0][0]
        assert req.full_url == "https://api.moonshot.ai/v1/chat/completions"
        sent_body = json.loads(req.data.decode())
        assert sent_body["model"] == "kimi-k2-0905-preview"

    def test_mistral_provider(self) -> None:
        """Mistral branch uses correct endpoint, default model, OpenAI-compatible format."""
        import json
        from unittest.mock import patch, MagicMock
        from vera.codegen.api import _call_inference_provider

        body = json.dumps({"choices": [{"message": {"content": "mistral"}}]})
        mock_urlopen = MagicMock(return_value=self._make_response(body))
        with patch("urllib.request.urlopen", mock_urlopen):
            result = _call_inference_provider("mistral", "prompt", "", "sk-mistral")
        assert result == "mistral"
        req = mock_urlopen.call_args[0][0]
        assert req.full_url == "https://api.mistral.ai/v1/chat/completions"
        # Bearer auth (OpenAI-compatible), not Anthropic-style key header
        assert req.get_header("Authorization") == "Bearer sk-mistral"
        assert req.get_header("X-api-key") is None
        sent_body = json.loads(req.data.decode())
        assert sent_body["model"] == "mistral-small-latest"
        # OpenAI-compatible body: has "messages", no Anthropic "max_tokens"
        assert "messages" in sent_body
        assert "max_tokens" not in sent_body

    def test_mistral_auto_detect(self) -> None:
        """Mistral key auto-detected when no other keys are set."""
        from unittest.mock import patch

        result_src = _compile_ok(TestInferenceCollection._CLASSIFY_SOURCE)
        with patch(
            "vera.codegen.api._call_inference_provider",
            return_value="ok",
        ) as mock_provider:
            execute(result_src, env_vars={"VERA_MISTRAL_API_KEY": "sk-mistral-test"})
            assert mock_provider.call_args[0][0] == "mistral"

    def test_multi_key_auto_detect_respects_provider_order(self) -> None:
        """When multiple keys are set, _PROVIDERS insertion order determines which wins.

        The auto-detection loop scans _PROVIDERS in order and picks the first
        provider whose key is present in the environment.  With anthropic first
        in the registry, setting both VERA_ANTHROPIC_API_KEY and
        VERA_MOONSHOT_API_KEY must resolve to 'anthropic'.
        """
        from unittest.mock import patch
        from vera.codegen.api import _PROVIDERS

        first_provider = next(iter(_PROVIDERS))  # "anthropic" per current registry
        first_cfg = _PROVIDERS[first_provider]
        second_provider = list(_PROVIDERS)[1]    # "openai"
        second_cfg = _PROVIDERS[second_provider]

        result_src = _compile_ok(TestInferenceCollection._CLASSIFY_SOURCE)
        with patch(
            "vera.codegen.api._call_inference_provider",
            return_value="ok",
        ) as mock_provider:
            execute(result_src, env_vars={
                first_cfg.env_key: "sk-first",
                second_cfg.env_key: "sk-second",
            })
            assert mock_provider.call_args[0][0] == first_provider

    def test_explicit_provider_missing_key_returns_err(self) -> None:
        """Provider set via VERA_INFERENCE_PROVIDER but key env var absent → Err branch.

        Patches _call_inference_provider to confirm the early-fail guard fires
        *before* any provider invocation — exec_result.value == 0 alone is not
        sufficient because the Err branch is also reached on a network failure.
        """
        from unittest.mock import patch

        result_src = _compile_ok(TestInferenceCollection._CLASSIFY_SOURCE)
        with patch(
            "vera.codegen.api._call_inference_provider",
            side_effect=AssertionError("should not be called"),
        ) as mock_provider:
            exec_result = execute(
                result_src,
                env_vars={"VERA_INFERENCE_PROVIDER": "mistral"},
            )
        # Early-fail guard returned Err before reaching the provider
        assert exec_result.value == 0
        mock_provider.assert_not_called()

    def test_custom_model_passed_through(self) -> None:
        """VERA_INFERENCE_MODEL is forwarded to the provider."""
        import json
        from unittest.mock import patch, MagicMock
        from vera.codegen.api import _call_inference_provider

        body = json.dumps({"content": [{"text": "ok"}]})
        mock_urlopen = MagicMock(return_value=self._make_response(body))
        with patch("urllib.request.urlopen", mock_urlopen):
            _call_inference_provider("anthropic", "hi", "claude-opus-4-6", "sk-ant")
        import json as _json
        sent = _json.loads(mock_urlopen.call_args[0][0].data.decode())
        assert sent["model"] == "claude-opus-4-6"

    def test_unknown_provider_raises(self) -> None:
        """Unknown provider string raises ValueError."""
        from vera.codegen.api import _call_inference_provider
        import pytest
        with pytest.raises(ValueError, match="Unknown inference provider"):
            _call_inference_provider("unknown", "p", "", "")


class TestRandomEffect:
    """Tests for the Random effect (#465).

    The three Random ops are non-deterministic, so each test
    constrains the host's behaviour via Python ``random.seed`` to
    make assertions concrete.  All tests run multiple iterations to
    catch off-by-one errors at range boundaries that would only
    surface on specific seeds.
    """

    def test_random_int_in_range(self) -> None:
        """Random.random_int(low, high) returns Int in inclusive [low, high].

        Seeded with ``random.seed(0)`` so the test is deterministic
        — not just \"probably covers the range.\"  After 100 draws
        the produced set must:
          (a) stay strictly within [low, high] on every draw,
          (b) include both boundary values (enforces the inclusive
              semantics — the original `len(produced) >= 4` check
              didn't actually verify that `low` and `high` were hit),
          (c) hit at least 4 of the 6 possible values (distribution
              sanity).
        Also asserts the WAT imports `$vera.random_int` and does
        NOT import `$vera.random_float` or `$vera.random_bool` —
        confirms ``_random_ops_used`` gating is working.
        """
        import random
        random.seed(0)
        low, high = 5, 10
        source = f"""\
public fn main(-> @Int)
  requires(true) ensures(true) effects(<Random>)
{{
  Random.random_int({low}, {high})
}}
"""
        result = _compile_ok(source)
        # WAT import-gating: only random_int should be imported.
        assert "$vera.random_int" in result.wat
        assert "$vera.random_float" not in result.wat
        assert "$vera.random_bool" not in result.wat

        produced = set()
        for _ in range(100):
            v = execute(result, fn_name="main").value
            assert low <= v <= high, f"out of range: {v}"
            produced.add(v)
        # Inclusive-range contract: both boundary values must appear.
        assert low in produced, f"low boundary {low} missing from {produced}"
        assert high in produced, f"high boundary {high} missing from {produced}"
        # Distribution sanity: at least 4 of 6 possible values in 100 draws.
        assert len(produced) >= 4, f"narrow distribution: {produced}"

    def test_random_int_zero_crossing_range(self) -> None:
        """random_int with a negative-to-positive range straddles zero.

        Covers signed-integer handling paths that all-positive ranges
        don't exercise: the Python `random.randint` accepts negative
        bounds transparently, but the WASM i64 marshalling and
        (browser-side) BigInt→Number conversion could in principle
        mishandle the sign bit or the zero crossing.  A `[-2, 2]`
        range forces every one of those 5 distinct values to appear
        to satisfy the boundary+distribution assertions.

        Also asserts WAT gating: only `random_int` imported.
        """
        import random
        random.seed(0)
        low, high = -2, 2
        source = f"""\
public fn main(-> @Int)
  requires(true) ensures(true) effects(<Random>)
{{
  Random.random_int({low}, {high})
}}
"""
        result = _compile_ok(source)
        assert "$vera.random_int" in result.wat
        assert "$vera.random_float" not in result.wat
        assert "$vera.random_bool" not in result.wat

        produced = set()
        for _ in range(100):
            v = execute(result, fn_name="main").value
            assert low <= v <= high, f"out of range: {v}"
            produced.add(v)
        # Both boundaries must appear across the signed range.
        assert low in produced, f"low boundary {low} missing from {produced}"
        assert high in produced, f"high boundary {high} missing from {produced}"
        # Zero specifically must be reachable — catches a bug where
        # the zero value gets dropped or treated as a sentinel.
        assert 0 in produced, f"zero missing from {produced}"
        # Distribution sanity: the range has 5 values; seeded draws
        # of 100 should comfortably cover at least 4.
        assert len(produced) >= 4, f"narrow distribution: {produced}"

    def test_random_int_singleton_range(self) -> None:
        """random_int(n, n) always returns n — degenerate range.

        Also asserts WAT gating: only `random_int` imported, not
        `random_float` or `random_bool`.
        """
        source = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(<Random>)
{
  Random.random_int(7, 7)
}
"""
        result = _compile_ok(source)
        assert "$vera.random_int" in result.wat
        assert "$vera.random_float" not in result.wat
        assert "$vera.random_bool" not in result.wat
        for _ in range(20):
            assert execute(result, fn_name="main").value == 7

    def test_random_float_in_unit_interval(self) -> None:
        """Random.random_float() returns Float64 in [0.0, 1.0).

        Verifies the WASM f64 result is correctly marshalled back
        through wasmtime — Float64 returns are easy to mis-handle.
        Also asserts WAT gating: only `random_float` imported, not
        `random_int` or `random_bool`.
        """
        source = """\
public fn main(-> @Float64)
  requires(true) ensures(true) effects(<Random>)
{
  Random.random_float(())
}
"""
        result = _compile_ok(source)
        assert "$vera.random_float" in result.wat
        assert "$vera.random_int" not in result.wat
        assert "$vera.random_bool" not in result.wat
        for _ in range(50):
            v = execute(result, fn_name="main").value
            assert isinstance(v, float)
            assert 0.0 <= v < 1.0, f"out of [0, 1): {v}"

    def test_random_bool_produces_both(self) -> None:
        """Random.random_bool() produces both true and false in 100 draws.

        Deterministic via ``random.seed(0)``: asserts both `0` and
        `1` appear in the observed set (stronger than the previous
        probabilistic ``25 <= total <= 75`` bound, which could
        flake).  With a fixed seed the set is reproducible and the
        test fails deterministically if the host impl becomes
        degenerate.

        Also asserts WAT gating: only `random_bool` imported, not
        `random_int` or `random_float`.
        """
        import random
        random.seed(0)
        source = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(<Random>)
{
  if Random.random_bool(()) then { 1 } else { 0 }
}
"""
        result = _compile_ok(source)
        assert "$vera.random_bool" in result.wat
        assert "$vera.random_int" not in result.wat
        assert "$vera.random_float" not in result.wat
        observed = {execute(result, fn_name="main").value for _ in range(100)}
        assert {0, 1}.issubset(observed), (
            f"random_bool didn't produce both outcomes in 100 seeded "
            f"draws; observed {observed}"
        )


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


class TestDecimalMonomorphization:
    """Monomorphization of generic functions with Decimal type args (#341)."""

    def test_option_unwrap_or_decimal(self) -> None:
        """option_unwrap_or<Decimal> with Some value."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Option<Decimal> = Some(decimal_from_int(42));
  let @Decimal = option_unwrap_or(@Option<Decimal>.0, decimal_from_int(0));
  if decimal_eq(@Decimal.0, decimal_from_int(42)) then { 1 } else { 0 }
}
"""
        assert _run(source) == 1

    def test_option_unwrap_or_decimal_none(self) -> None:
        """option_unwrap_or<Decimal> with None returns default."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Option<Decimal> = None;
  let @Decimal = option_unwrap_or(@Option<Decimal>.0, decimal_from_int(99));
  if decimal_eq(@Decimal.0, decimal_from_int(99)) then { 1 } else { 0 }
}
"""
        assert _run(source) == 1

    def test_match_option_decimal(self) -> None:
        """match on Option<Decimal> with Some and None arms."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Option<Decimal> = Some(decimal_from_int(7));
  match @Option<Decimal>.0 {
    None -> 0,
    Some(@Decimal) -> if decimal_eq(@Decimal.0, decimal_from_int(7)) then { 1 } else { 0 }
  }
}
"""
        assert _run(source) == 1

    def test_decimal_div_unwrap(self) -> None:
        """decimal_div returns Option<Decimal>, unwrapped with option_unwrap_or."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Option<Decimal> = decimal_div(decimal_from_int(10), decimal_from_int(2));
  let @Decimal = option_unwrap_or(@Option<Decimal>.0, decimal_from_int(0));
  if decimal_eq(@Decimal.0, decimal_from_int(5)) then { 1 } else { 0 }
}
"""
        assert _run(source) == 1

    def test_decimal_div_by_zero_unwrap(self) -> None:
        """decimal_div by zero returns None, option_unwrap_or gives default."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Option<Decimal> = decimal_div(decimal_from_int(10), decimal_from_int(0));
  let @Decimal = option_unwrap_or(@Option<Decimal>.0, decimal_from_int(99));
  if decimal_eq(@Decimal.0, decimal_from_int(99)) then { 1 } else { 0 }
}
"""
        assert _run(source) == 1

    def test_decimal_compare_match(self) -> None:
        """match on Ordering from decimal_compare."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Ordering = decimal_compare(decimal_from_int(1), decimal_from_int(2));
  match @Ordering.0 {
    Less -> 1,
    Equal -> 2,
    Greater -> 3
  }
}
"""
        assert _run(source) == 1

    def test_decimal_compare_equal(self) -> None:
        """decimal_compare returns Equal for equal values."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Ordering = decimal_compare(decimal_from_int(5), decimal_from_int(5));
  match @Ordering.0 {
    Less -> 0,
    Equal -> 1,
    Greater -> 0
  }
}
"""
        assert _run(source) == 1

    def test_decimal_compare_greater(self) -> None:
        """decimal_compare returns Greater."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Ordering = decimal_compare(decimal_from_int(10), decimal_from_int(3));
  match @Ordering.0 {
    Less -> 0,
    Equal -> 0,
    Greater -> 1
  }
}
"""
        assert _run(source) == 1

    def test_decimal_from_string_match(self) -> None:
        """decimal_from_string returns Option<Decimal>, match extracts value."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Option<Decimal> = decimal_from_string("42");
  match @Option<Decimal>.0 {
    None -> 0,
    Some(@Decimal) -> if decimal_eq(@Decimal.0, decimal_from_int(42)) then { 1 } else { 0 }
  }
}
"""
        assert _run(source) == 1

    def test_decimal_from_string_invalid_match(self) -> None:
        """decimal_from_string with invalid input returns None."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Option<Decimal> = decimal_from_string("not_a_number");
  match @Option<Decimal>.0 {
    None -> 1,
    Some(@Decimal) -> 0
  }
}
"""
        assert _run(source) == 1

    def test_decimal_div_inline_unwrap(self) -> None:
        """option_unwrap_or with decimal_div() directly (no let binding).

        Exercises _get_arg_type_info → _BUILTIN_PARAMETERIZED_RETURNS path.
        """
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Decimal = option_unwrap_or(decimal_div(decimal_from_int(10), decimal_from_int(5)), decimal_from_int(0));
  if decimal_eq(@Decimal.0, decimal_from_int(2)) then { 1 } else { 0 }
}
"""
        assert _run(source) == 1

    def test_decimal_from_string_inline_unwrap(self) -> None:
        """option_unwrap_or with decimal_from_string() directly.

        Exercises _get_arg_type_info → _BUILTIN_PARAMETERIZED_RETURNS path.
        """
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Decimal = option_unwrap_or(decimal_from_string("7"), decimal_from_int(0));
  if decimal_eq(@Decimal.0, decimal_from_int(7)) then { 1 } else { 0 }
}
"""
        assert _run(source) == 1

    def test_option_unwrap_or_map(self) -> None:
        """option_unwrap_or<Map<String, Int>> monomorphization."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Option<Map<String, Int>> = Some(map_insert(map_new(), "a", 1));
  let @Map<String, Int> = option_unwrap_or(@Option<Map<String, Int>>.0, map_new());
  map_size(@Map<String, Int>.0)
}
"""
        assert _run(source) == 1

    def test_option_unwrap_or_set(self) -> None:
        """option_unwrap_or<Set<Int>> monomorphization."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Option<Set<Int>> = Some(set_add(set_new(), 42));
  let @Set<Int> = option_unwrap_or(@Option<Set<Int>>.0, set_new());
  set_size(@Set<Int>.0)
}
"""
        assert _run(source) == 1

    def test_match_option_set(self) -> None:
        """match on Option<Set<Int>> — works because match is inline."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Option<Set<Int>> = Some(set_add(set_new(), 42));
  match @Option<Set<Int>>.0 {
    None -> 0,
    Some(@Set<Int>) -> set_size(@Set<Int>.0)
  }
}
"""
        assert _run(source) == 1

    def test_option_unwrap_or_map_none(self) -> None:
        """option_unwrap_or<Map<String, Int>> with None returns default."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Option<Map<String, Int>> = None;
  let @Map<String, Int> = option_unwrap_or(
    @Option<Map<String, Int>>.0,
    map_insert(map_new(), "d", 1)
  );
  map_size(@Map<String, Int>.0)
}
"""
        assert _run(source) == 1

    def test_option_unwrap_or_set_none(self) -> None:
        """option_unwrap_or<Set<Int>> with None returns default."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Option<Set<Int>> = None;
  let @Set<Int> = option_unwrap_or(@Option<Set<Int>>.0, set_add(set_new(), 7));
  set_size(@Set<Int>.0)
}
"""
        assert _run(source) == 1

    def test_option_unwrap_or_mixed_instantiations(self) -> None:
        """Two distinct Map parameterizations in one module."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Option<Map<String, Int>> = Some(map_insert(map_new(), "a", 1));
  let @Map<String, Int> = option_unwrap_or(@Option<Map<String, Int>>.0, map_new());
  let @Option<Map<Int, Int>> = Some(map_insert(map_new(), 42, 2));
  let @Map<Int, Int> = option_unwrap_or(@Option<Map<Int, Int>>.0, map_new());
  map_size(@Map<String, Int>.0) + map_size(@Map<Int, Int>.0)
}
"""
        assert _run(source) == 2


class TestTypedHoles:
    """Typed holes: compile rejects programs with ? placeholders."""

    def test_hole_compile_rejected(self) -> None:
        """Programs with holes produce E614 and cannot compile."""
        src = """\
public fn foo(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ ? }
"""
        result = _compile(src)
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert any(d.error_code == "E614" for d in errors), \
            f"Expected E614, got: {[d.error_code for d in errors]}"
        assert result.wasm_bytes == b""

    def test_hole_nested_compile_rejected(self) -> None:
        """Holes in non-root positions (let bindings) also produce E614."""
        src = """\
public fn bar(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Int = ?;
  @Int.0 + 1
}
"""
        result = _compile(src)
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert any(d.error_code == "E614" for d in errors), \
            f"Expected E614, got: {[d.error_code for d in errors]}"
        assert result.wasm_bytes == b""


class TestClosureI32PairParams:
    """Closures whose parameters or return types are i32_pair (String, Array).

    Regression tests for #359: closure lifting and call_indirect type
    descriptors must emit two consecutive i32 slots for i32_pair types,
    not an unsupported/missing param.
    """

    def test_closure_string_param_compiles(self) -> None:
        """Closure with a String parameter emits valid (param i32 i32) WAT."""
        src = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  apply_fn(fn(@String -> @Int) effects(pure) { string_length(@String.0) }, "hello")
}
"""
        assert _run(src) == 5

    def test_closure_string_return_compiles(self) -> None:
        """Closure with a String return type emits valid (result i32 i32) WAT."""
        src = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @String = apply_fn(fn(@Int -> @String) effects(pure) { "ok" }, 0);
  string_length(@String.0)
}
"""
        assert _run(src) == 2

    def test_closure_array_param_compiles(self) -> None:
        """Closure with an Array<Int> parameter emits valid (param i32 i32) WAT."""
        src = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Array<Int> = [10, 20, 30];
  apply_fn(fn(@Array<Int> -> @Int) effects(pure) { array_length(@Array<Int>.0) }, @Array<Int>.0)
}
"""
        assert _run(src) == 3

    def test_closure_array_return_compiles(self) -> None:
        """Closure with an Array<Int> return type emits valid (result i32 i32) WAT."""
        src = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Array<Int> = apply_fn(fn(@Int -> @Array<Int>) effects(pure) { [1, 2] }, 0);
  array_length(@Array<Int>.0)
}
"""
        assert _run(src) == 2

    def test_array_fold_with_map_accumulator(self) -> None:
        """array_fold over String array with Map<String, Int> accumulator.

        Exercises: (1) i32_pair closure param in the lifted fold fn,
        (2) apply_fn return-type inference with a parameterized accumulator
        so _resolve_generic_call produces array_fold_go$String_Map_String_Int.
        Also exercises the zero-iteration path (empty array).
        """
        src = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Array<String> = ["a", "b", "c"];
  let @Map<String, Int> = map_new();
  let @Map<String, Int> = array_fold(
    @Array<String>.0,
    @Map<String, Int>.0,
    fn(@Map<String, Int>, @String -> @Map<String, Int>) effects(pure) {
      map_insert(@Map<String, Int>.0, @String.0, 1)
    }
  );
  let @Int = map_size(@Map<String, Int>.0);
  let @Array<String> = [];
  let @Map<String, Int> = map_new();
  let @Map<String, Int> = array_fold(
    @Array<String>.0,
    @Map<String, Int>.0,
    fn(@Map<String, Int>, @String -> @Map<String, Int>) effects(pure) {
      map_insert(@Map<String, Int>.0, @String.0, 1)
    }
  );
  let @Int = map_size(@Map<String, Int>.0);
  @Int.1 + @Int.0
}
"""
        assert _run(src) == 3  # 3 + 0


class TestArrayUtilities:
    """#466 phase 1: array_mapi, _reverse, _find, _any, _all,
    _flatten, _sort_by — all iterative WASM, no Eq/Ord dispatch.

    Tests aim to verify *values* not just lengths.  Where Vera lacks a
    direct array-indexing primitive, we fold the result back to a
    single Int (e.g. positional digit packing for ordered sequences,
    or sum for length-preserving ops) so a single ``_run() ==`` check
    pins down the entire output.
    """

    def test_array_mapi_passes_index(self) -> None:
        """array_mapi(range(10,15), |x,i| x + i*100) → [10, 111, 212, 313, 414].

        Sum = 1060.  Uses a non-identity input range so element
        values and indices are distinct: a translator that
        accidentally swapped the (elem, idx) callback arguments
        would compute idx + elem*100 instead, summing to 6010 —
        clearly different from 1060.  The earlier
        ``array_range(0, 5)`` form had element[i] == i, so a
        swapped-args bug would have been masked because both
        orderings produced the same sum.
        """
        src = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Array<Int> = array_mapi(
    array_range(10, 15),
    fn(@Int, @Nat -> @Int) effects(pure) {
      @Int.0 + nat_to_int(@Nat.0) * 100
    }
  );
  array_fold(
    @Array<Int>.0, 0,
    fn(@Int, @Int -> @Int) effects(pure) { @Int.1 + @Int.0 }
  )
}
"""
        # Elements 10, 11, 12, 13, 14 with indices 0, 1, 2, 3, 4:
        #   10 + 0*100 = 10
        #   11 + 1*100 = 111
        #   12 + 2*100 = 212
        #   13 + 3*100 = 313
        #   14 + 4*100 = 414
        # Sum = 1060.  Swapped (idx, elem) ordering gives:
        #   0 + 10*100 = 1000
        #   1 + 11*100 = 1101
        #   2 + 12*100 = 1202
        #   3 + 13*100 = 1303
        #   4 + 14*100 = 1404
        # Sum = 6010.  Test fails clearly under either bug.
        assert _run(src) == 1060

    def test_array_reverse_preserves_elements(self) -> None:
        """array_reverse([1..5]) sums to 15 — same elements, just reordered."""
        src = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Array<Int> = array_reverse(array_range(1, 6));
  array_fold(
    @Array<Int>.0, 0,
    fn(@Int, @Int -> @Int) effects(pure) { @Int.1 + @Int.0 }
  )
}
"""
        assert _run(src) == 15

    def test_array_reverse_actually_reverses(self) -> None:
        """Pack reversed [1..5] = [5,4,3,2,1] as digits → 54321.

        Catches a no-op implementation that returns the input
        unchanged.  Positional digit packing is order-sensitive.
        """
        src = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Array<Int> = array_reverse(array_range(1, 6));
  array_fold(
    @Array<Int>.0, 0,
    fn(@Int, @Int -> @Int) effects(pure) { @Int.1 * 10 + @Int.0 }
  )
}
"""
        assert _run(src) == 54321

    def test_array_mapi_empty_input(self) -> None:
        """array_mapi on an empty array returns an empty array.

        Exercises the len==0 path: the loop's initial bounds check
        (``idx >= arr_len`` with both 0) must break out immediately,
        no callback invocation, and the $alloc(0) must not trap.
        Folding over the empty result with a sum-counter yields 0.
        """
        src = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Array<Int> = array_mapi(
    array_range(0, 0),
    fn(@Int, @Nat -> @Int) effects(pure) {
      @Int.0 + nat_to_int(@Nat.0)
    }
  );
  array_fold(
    @Array<Int>.0, 0,
    fn(@Int, @Int -> @Int) effects(pure) { @Int.1 + @Int.0 }
  )
}
"""
        assert _run(src) == 0

    def test_array_reverse_empty_input(self) -> None:
        """array_reverse on an empty array returns an empty array."""
        src = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Array<Int> = array_reverse(array_range(0, 0));
  array_fold(
    @Array<Int>.0, 0,
    fn(@Int, @Int -> @Int) effects(pure) { @Int.1 * 10 + @Int.0 }
  )
}
"""
        # Empty result, digit-packing fold neutral == 0.
        assert _run(src) == 0

    def test_array_flatten_empty_input(self) -> None:
        """array_flatten on an empty outer array returns an empty array.

        Exercises the len==0 path for the two-pass flatten: the
        first pass (summing inner lengths) exits at idx==0, total
        stays at 0, $alloc(0) succeeds, the second pass is likewise
        empty.  No trap despite the zero-byte allocation.
        """
        src = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Array<Array<Int>> = [];
  let @Array<Int> = array_flatten(@Array<Array<Int>>.0);
  array_fold(
    @Array<Int>.0, 0,
    fn(@Int, @Int -> @Int) effects(pure) { @Int.1 + @Int.0 }
  )
}
"""
        assert _run(src) == 0

    def test_array_find_returns_first_match(self) -> None:
        """array_find([1..10], > 5) → Some(6) — first match, not last."""
        src = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Option<Int> = array_find(
    array_range(1, 10),
    fn(@Int -> @Bool) effects(pure) { @Int.0 > 5 }
  );
  match @Option<Int>.0 {
    Some(@Int) -> @Int.0,
    None -> -1
  }
}
"""
        assert _run(src) == 6

    def test_array_find_returns_none_when_no_match(self) -> None:
        """array_find returns None sentinel when every predicate is false."""
        src = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Option<Int> = array_find(
    array_range(1, 5),
    fn(@Int -> @Bool) effects(pure) { @Int.0 > 100 }
  );
  match @Option<Int>.0 {
    Some(@Int) -> @Int.0,
    None -> -42
  }
}
"""
        assert _run(src) == -42

    def test_array_find_short_circuits(self) -> None:
        """array_find short-circuit properties that are observable in pure code.

        ``array_find``'s signature requires ``effects(pure)`` on the
        predicate, so we cannot count calls from inside Vera — that
        check would require mutable state, which pure functions
        cannot reach.  What IS observable without effects:

          (a) The *first* match wins, not a later one.  A predicate
              that's true for many elements must return Some(first),
              never Some(later).  Covered by
              ``test_array_find_returns_first_match`` on [1..10].

          (b) An empty array returns None rather than trapping on
              an out-of-bounds access.  Included below.

          (c) A predicate that is expensive at later indices but
              cheap at the first match still runs cheaply overall.
              This is the architectural short-circuit; we exercise
              the compile-time structure by ensuring a match at
              index 0 of a very large array returns immediately
              (the test would time out if every element were
              actually visited).

        The WAT's inner-loop structure (``br_if $brk_find`` on
        match) is the real guarantee; these tests confirm the
        externally visible behaviour is consistent with that.
        """
        # (b) empty-array base case — None rather than a trap
        empty_src = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Array<Int> = [];
  let @Option<Int> = array_find(
    @Array<Int>.0,
    fn(@Int -> @Bool) effects(pure) { true }
  );
  match @Option<Int>.0 {
    Some(@Int) -> 1,
    None -> 0
  }
}
"""
        assert _run(empty_src) == 0

        # (c) big-array match-at-head: if the loop didn't break
        # early, `array_range(0, 10000)` would force the runtime to
        # walk all 10,000 elements before returning.  Matching on
        # the very first element exercises the short-circuit path.
        # Returned value (0) also confirms the first match wins.
        big_src = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Option<Int> = array_find(
    array_range(0, 10000),
    fn(@Int -> @Bool) effects(pure) { @Int.0 == 0 }
  );
  match @Option<Int>.0 {
    Some(@Int) -> @Int.0,
    None -> -1
  }
}
"""
        assert _run(big_src) == 0

    def test_array_any(self) -> None:
        """array_any: true when at least one passes; false otherwise."""
        src_true = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  if array_any(
    array_range(-3, 3),
    fn(@Int -> @Bool) effects(pure) { @Int.0 > 0 }
  ) then { 1 } else { 0 }
}
"""
        src_false = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  if array_any(
    array_range(-3, 0),
    fn(@Int -> @Bool) effects(pure) { @Int.0 > 0 }
  ) then { 1 } else { 0 }
}
"""
        assert _run(src_true) == 1
        assert _run(src_false) == 0

    def test_array_all(self) -> None:
        """array_all: true when every element passes; false otherwise."""
        src_true = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  if array_all(
    array_range(1, 6),
    fn(@Int -> @Bool) effects(pure) { @Int.0 > 0 }
  ) then { 1 } else { 0 }
}
"""
        src_false = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  if array_all(
    array_range(-3, 3),
    fn(@Int -> @Bool) effects(pure) { @Int.0 > 0 }
  ) then { 1 } else { 0 }
}
"""
        assert _run(src_true) == 1
        assert _run(src_false) == 0

    def test_array_any_short_circuits_observably(self) -> None:
        """Head-match: array_any with assert(false) on the trailing
        element confirms the predicate is *not* invoked past the
        first match.

        Input is ``[1, 99]``.  Predicate returns true for 1 and
        traps via ``assert(false)`` for any other value.  If
        array_any short-circuits on the first match (correct
        behaviour), the second element is never visited and the
        program returns 1 cleanly.  A non-short-circuiting
        implementation would invoke the predicate on 99, hit the
        assert, and trap — caught by ``_run_trap`` failing to find
        a trap.
        """
        src = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Array<Int> = [1, 99];
  let @Bool = array_any(
    @Array<Int>.0,
    fn(@Int -> @Bool) effects(pure) {
      if @Int.0 == 1 then { true } else { assert(false); false }
    }
  );
  if @Bool.0 then { 1 } else { 0 }
}
"""
        assert _run(src) == 1

    def test_array_all_short_circuits_observably(self) -> None:
        """Head-fail: array_all with assert(false) on the trailing
        element confirms the predicate is *not* invoked past the
        first failure.

        Input is ``[0, 99]``.  Predicate returns false for 0 and
        traps for any other value.  If array_all short-circuits on
        the first false (correct behaviour), 0 fails and 99 is
        never visited.  A non-short-circuiting implementation
        would visit 99, hit the assert, and trap.
        """
        src = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Array<Int> = [0, 99];
  let @Bool = array_all(
    @Array<Int>.0,
    fn(@Int -> @Bool) effects(pure) {
      if @Int.0 == 0 then { false } else { assert(false); true }
    }
  );
  if @Bool.0 then { 1 } else { 0 }
}
"""
        assert _run(src) == 0

    def test_array_any_all_empty(self) -> None:
        """Empty-array invariants: any → false, all → true (vacuous truth)."""
        src = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Array<Int> = [];
  let @Bool = array_any(@Array<Int>.0,
    fn(@Int -> @Bool) effects(pure) { true });
  let @Bool = array_all(@Array<Int>.0,
    fn(@Int -> @Bool) effects(pure) { false });
  if @Bool.1 then { 1 } else {
    if @Bool.0 then { 2 } else { 10 }
  }
}
"""
        # @Bool.1 (any) should be false (empty), @Bool.0 (all) should
        # be true (vacuous), so we hit the inner `if @Bool.0`'s then.
        assert _run(src) == 2

    def test_array_flatten(self) -> None:
        """Flatten [[1,2],[3,4],[5,6]] → [1,2,3,4,5,6]; pack as 123456."""
        src = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Array<Array<Int>> = array_map(
    array_range(0, 3),
    fn(@Int -> @Array<Int>) effects(pure) {
      array_range(@Int.0 * 2 + 1, @Int.0 * 2 + 3)
    }
  );
  let @Array<Int> = array_flatten(@Array<Array<Int>>.0);
  array_fold(
    @Array<Int>.0, 0,
    fn(@Int, @Int -> @Int) effects(pure) { @Int.1 * 10 + @Int.0 }
  )
}
"""
        # Inner: (1,2), (3,4), (5,6).  Flatten → 1,2,3,4,5,6.  Pack
        # → 123456.
        assert _run(src) == 123456

    def test_array_flatten_with_empty_inners(self) -> None:
        """Flatten where some inner arrays are empty.  [[1,2], [], [3]] → [1,2,3]."""
        src = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  -- Build [[1,2], [], [3]] via mapi: idx 0 → [1,2], idx 1 → [], idx 2 → [3]
  let @Array<Array<Int>> = array_mapi(
    array_range(0, 3),
    fn(@Int, @Nat -> @Array<Int>) effects(pure) {
      if nat_to_int(@Nat.0) == 0 then {
        array_range(1, 3)
      } else {
        if nat_to_int(@Nat.0) == 1 then {
          array_range(0, 0)
        } else {
          array_range(3, 4)
        }
      }
    }
  );
  let @Array<Int> = array_flatten(@Array<Array<Int>>.0);
  array_fold(
    @Array<Int>.0, 0,
    fn(@Int, @Int -> @Int) effects(pure) { @Int.1 * 10 + @Int.0 }
  )
}
"""
        # Inner arrays: [1,2], [], [3].  Flattened: [1,2,3].  Packed: 123.
        assert _run(src) == 123

    def test_array_sort_by_ascending_ints(self) -> None:
        """Sort [3, 1, 2] ascending → [1, 2, 3]; pack → 123."""
        src = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Array<Int> = array_concat(
    array_concat(array_range(3, 4), array_range(1, 2)),
    array_range(2, 3)
  );
  let @Array<Int> = array_sort_by(
    @Array<Int>.0,
    fn(@Int, @Int -> @Ordering) effects(pure) {
      if @Int.1 < @Int.0 then { Less } else {
        if @Int.1 > @Int.0 then { Greater } else { Equal }
      }
    }
  );
  array_fold(
    @Array<Int>.0, 0,
    fn(@Int, @Int -> @Int) effects(pure) { @Int.1 * 10 + @Int.0 }
  )
}
"""
        assert _run(src) == 123

    def test_array_sort_by_descending(self) -> None:
        """Sort [1, 3, 2] descending → [3, 2, 1]; pack → 321.

        Confirms the comparator's polarity is respected — flipping
        the < / > in the comparator inverts the sort order.
        """
        src = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Array<Int> = array_concat(
    array_concat(array_range(1, 2), array_range(3, 4)),
    array_range(2, 3)
  );
  let @Array<Int> = array_sort_by(
    @Array<Int>.0,
    fn(@Int, @Int -> @Ordering) effects(pure) {
      if @Int.1 > @Int.0 then { Less } else {
        if @Int.1 < @Int.0 then { Greater } else { Equal }
      }
    }
  );
  array_fold(
    @Array<Int>.0, 0,
    fn(@Int, @Int -> @Int) effects(pure) { @Int.1 * 10 + @Int.0 }
  )
}
"""
        assert _run(src) == 321

    def test_array_sort_by_already_sorted(self) -> None:
        """Sorting an already-sorted array is a no-op."""
        src = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Array<Int> = array_sort_by(
    array_range(1, 6),
    fn(@Int, @Int -> @Ordering) effects(pure) {
      if @Int.1 < @Int.0 then { Less } else {
        if @Int.1 > @Int.0 then { Greater } else { Equal }
      }
    }
  );
  array_fold(
    @Array<Int>.0, 0,
    fn(@Int, @Int -> @Int) effects(pure) { @Int.1 * 10 + @Int.0 }
  )
}
"""
        assert _run(src) == 12345

    def test_array_sort_by_empty(self) -> None:
        """Sorting an empty array returns an empty array (length 0)."""
        src = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Array<Int> = [];
  let @Array<Int> = array_sort_by(
    @Array<Int>.0,
    fn(@Int, @Int -> @Ordering) effects(pure) { Equal }
  );
  array_length(@Array<Int>.0)
}
"""
        assert _run(src) == 0

    def test_array_sort_by_singleton(self) -> None:
        """Sorting a single-element array returns that element unchanged."""
        src = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Array<Int> = array_range(42, 43);
  let @Array<Int> = array_sort_by(
    @Array<Int>.0,
    fn(@Int, @Int -> @Ordering) effects(pure) { Equal }
  );
  array_fold(
    @Array<Int>.0, 0,
    fn(@Int, @Int -> @Int) effects(pure) { @Int.1 + @Int.0 }
  )
}
"""
        assert _run(src) == 42

    def test_array_sort_by_strings(self) -> None:
        """sort_by on Array<String> exercises the pair-T GC rooting branch.

        ``String`` is a pair-typed element (i32 ptr + i32 len, 8 bytes),
        so the sort's ``tmp_a`` holds a heap pointer that must be
        rooted across the comparator's ``call_indirect``.  The
        comparator allocates an ``Ordering`` box per call, which can
        trigger GC; without the shadow-stack root added in round 2,
        the String pointed at by ``tmp_a`` could be collected and the
        sort would corrupt its output.

        Comparator orders by string length here (cheap and
        deterministic) rather than lexicographically — Vera does not
        yet have a built-in string ordering, and that's a separate
        ergonomic gap.  Sort the input by length, then concatenate
        the sorted result and return the byte-length of the
        concatenation as the verifiable scalar.
        """
        src = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Array<String> = ["aaa", "b", "cc"];
  let @Array<String> = array_sort_by(
    @Array<String>.0,
    fn(@String, @String -> @Ordering) effects(pure) {
      if string_length(@String.1) < string_length(@String.0) then {
        Less
      } else {
        if string_length(@String.1) > string_length(@String.0) then {
          Greater
        } else {
          Equal
        }
      }
    }
  );
  -- Fold a length-weighted fingerprint: sum of (len * 100^position).
  -- Stable ascending [b, cc, aaa] gives 1*1 + 2*100 + 3*10000 = 30201.
  -- Any other ordering produces a different fingerprint.
  let @Int = array_fold(
    @Array<String>.0, 0,
    fn(@Int, @String -> @Int) effects(pure) {
      @Int.0 * 100 + nat_to_int(string_length(@String.0))
    }
  );
  @Int.0
}
"""
        # Sorted lengths: [1, 2, 3].  Fold reads left-to-right with
        # `acc * 100 + len`:
        #   step 1: 0 * 100 + 1 = 1
        #   step 2: 1 * 100 + 2 = 102
        #   step 3: 102 * 100 + 3 = 10203
        assert _run(src) == 10203

    def test_array_sort_by_options(self) -> None:
        """sort_by on Array<Option<Int>> exercises the ADT-T GC rooting branch.

        ``Option<Int>`` is an i32 heap handle (16-byte boxed ADT,
        not a pair).  The ``tmp`` local in the sort holds this
        handle directly; without the round-2 ADT-rooting fix
        (``t_is_adt`` / ``t_needs_root``), the option box could be
        collected during the comparator's allocation, and the sort
        would dereference garbage memory.

        Sort by extracting the inner Int (with a sentinel for None)
        and comparing those.  Verify the result via match-arm fold.
        """
        src = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  -- Build [Some(3), Some(1), Some(2)] via array_map for an
  -- Array<Option<Int>>.  The map output element is Option<Int>,
  -- which is an i32 heap handle (the GC-managed shape we want
  -- to exercise).
  let @Array<Int> = [3, 1, 2];
  let @Array<Option<Int>> = array_map(
    @Array<Int>.0,
    fn(@Int -> @Option<Int>) effects(pure) { Some(@Int.0) }
  );
  let @Array<Option<Int>> = array_sort_by(
    @Array<Option<Int>>.0,
    fn(@Option<Int>, @Option<Int> -> @Ordering) effects(pure) {
      let @Int = match @Option<Int>.1 {
        Some(@Int) -> @Int.0,
        None -> 0
      };
      let @Int = match @Option<Int>.0 {
        Some(@Int) -> @Int.0,
        None -> 0
      };
      if @Int.1 < @Int.0 then { Less } else {
        if @Int.1 > @Int.0 then { Greater } else { Equal }
      }
    }
  );
  -- Fold: extract each Some payload, digit-pack.  Sorted
  -- ascending gives [Some(1), Some(2), Some(3)] → 1, 12, 123.
  array_fold(
    @Array<Option<Int>>.0, 0,
    fn(@Int, @Option<Int> -> @Int) effects(pure) {
      let @Int = match @Option<Int>.0 {
        Some(@Int) -> @Int.0,
        None -> 0
      };
      @Int.1 * 10 + @Int.0
    }
  )
}
"""
        assert _run(src) == 123

    def test_array_sort_by_stability(self) -> None:
        """Equal-keyed elements preserve their original relative order.

        Encode each element as ``key * 10 + payload`` where keys are
        duplicated (10, 10, 20, 20, 10) and payloads are the original
        indices (0, 1, 2, 3, 4).  Sort by key only — the comparator
        inspects just the key digit (x / 10).  A stable sort keeps
        equal-keyed elements in input order:

          input:     [100, 101, 202, 203, 104]  (key*10 + pos)
          sort-key:  [ 10,  10,  20,  20,  10]
          stable:    [100, 101, 104, 202, 203]  (payloads 0, 1, 4, 2, 3)
          unstable:  equal elements may shuffle (e.g. payloads 1, 0, 4)

        Digit-pack the result to nail the exact order — 100, 101,
        104 first (the 10-keyed group in original order), then 202,
        203 (the 20-keyed group in original order).
        """
        src = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  -- Input: [100, 101, 202, 203, 104]
  let @Array<Int> = array_concat(
    array_concat(
      array_concat(
        array_concat(array_range(100, 101), array_range(101, 102)),
        array_range(202, 203)
      ),
      array_range(203, 204)
    ),
    array_range(104, 105)
  );
  let @Array<Int> = array_sort_by(
    @Array<Int>.0,
    fn(@Int, @Int -> @Ordering) effects(pure) {
      -- Compare on key = elem / 10 only.  Payload = elem % 10 is
      -- deliberately ignored so equal-keyed elements carry no
      -- ordering signal through the comparator.
      if @Int.1 / 10 < @Int.0 / 10 then { Less } else {
        if @Int.1 / 10 > @Int.0 / 10 then { Greater } else { Equal }
      }
    }
  );
  -- Fold to a fingerprint: multiply by 1000 per step so the
  -- digits don't overlap.  Stable order [100,101,104,202,203]
  -- yields 100 then 100*1000+101=100101 then 100101*1000+104=...
  -- which gets unwieldy; use sum-of-squares instead — any
  -- transposition of adjacent equals would change at least one
  -- squared term, but sum-of-squares is order-invariant.  So
  -- use a position-weighted sum instead: fold with index.
  let @Int = array_fold(
    @Array<Int>.0, 0,
    fn(@Int, @Int -> @Int) effects(pure) { @Int.1 * 1000 + @Int.0 }
  );
  @Int.0
}
"""
        # Stable output:    [100, 101, 104, 202, 203]
        # Position-weighted: ((((0*1000+100)*1000+101)*1000+104)*1000+202)*1000+203
        #                    = (100*1e3 + 101) = 100101
        #                    * 1000 + 104       = 100101104
        #                    * 1000 + 202       = 100101104202
        #                    * 1000 + 203       = 100101104202203
        assert _run(src) == 100101104202203


_INLINE_BUILTIN_NAMES = (
    # #471 — character classifiers + first-byte case conversion
    "is_digit", "is_alpha", "is_alphanumeric", "is_whitespace",
    "is_upper", "is_lower", "char_to_upper", "char_to_lower",
    # #470 — string utilities
    "string_chars", "string_lines", "string_words",
    "string_reverse", "string_trim_start", "string_trim_end",
    "string_pad_start", "string_pad_end",
)


def _assert_no_host_imports_for_inline_builtins(wat: str) -> None:
    """Assert the compiled WAT has no host imports for the 16 inline
    built-ins added by #470 + #471.

    These functions are documented as being implemented entirely
    inline in WAT (no host imports — bit-identical Python/browser
    output by construction).  If a future refactor accidentally
    routes one through a host import, the import would appear as
    ``(import "vera" "<name>" ...)`` in the module's import section
    and this assertion would catch it.

    The check tolerates other unrelated imports (`IO.print`,
    `gc_collect` host helpers, etc.) — it scans only for our 16
    names.
    """
    for name in _INLINE_BUILTIN_NAMES:
        marker = f'(import "vera" "{name}"'
        assert marker not in wat, (
            f"Expected no host import for inline built-in {name!r}, "
            f"but found {marker!r} in the WAT.  This contradicts the "
            f"#470/#471 design contract."
        )


class TestCharClassification:
    """#471 — the six ASCII classifiers + two case converters.

    Each classifier loads the first byte and tests against one or
    more ASCII ranges (subtract + unsigned-less-than trick for
    ``is_digit``/`is_alpha`/`is_upper`/`is_lower`; direct equality
    OR for ``is_whitespace``; OR'd pair for ``is_alphanumeric``).
    Empty-string convention: always false.
    """

    def _run_bool(self, src: str) -> int:
        """Compile a classifier call and return the i32 result."""
        return _run(src)

    def test_no_host_imports_for_inline_builtins(self) -> None:
        """Compile a program that uses all 16 #470/#471 built-ins and
        assert none of them is routed through a host import.

        Catches regressions in either direction: a refactor that
        adds a host import for one of these (the documented
        contract is "inline WAT, no host calls"), or a sibling
        builtin renamed to collide with one of our 16 names.
        """
        src = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Bool = is_digit("5");
  let @Bool = is_alpha("A");
  let @Bool = is_alphanumeric("0");
  let @Bool = is_whitespace(" ");
  let @Bool = is_upper("A");
  let @Bool = is_lower("a");
  let @String = char_to_upper("a");
  let @String = char_to_lower("A");
  let @String = string_reverse("ab");
  let @String = string_trim_start("  x");
  let @String = string_trim_end("x  ");
  let @String = string_pad_start("x", 3, "0");
  let @String = string_pad_end("x", 3, "0");
  let @Array<String> = string_chars("ab");
  let @Array<String> = string_lines("a\\nb");
  let @Array<String> = string_words("a b");
  0
}
"""
        result = _compile_ok(src)
        _assert_no_host_imports_for_inline_builtins(result.wat)

    def test_is_digit(self) -> None:
        """is_digit: '5' true, 'x' false, '' false, '9' true, '0' true."""
        for s, expected in [("5", 1), ("x", 0), ("", 0), ("9", 1), ("0", 1)]:
            src = f"""\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{{ if is_digit({json.dumps(s)}) then {{ 1 }} else {{ 0 }} }}
"""
            assert _run(src) == expected, f"is_digit({json.dumps(s)}) != {expected}"

    def test_is_alpha(self) -> None:
        """is_alpha: ASCII A-Z and a-z only."""
        for s, expected in [("a", 1), ("Z", 1), ("0", 0), ("!", 0), ("", 0)]:
            src = f"""\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{{ if is_alpha({json.dumps(s)}) then {{ 1 }} else {{ 0 }} }}
"""
            assert _run(src) == expected, f"is_alpha({json.dumps(s)}) != {expected}"

    def test_is_alphanumeric(self) -> None:
        """is_alphanumeric: letter OR digit."""
        for s, expected in [("a", 1), ("5", 1), ("Z", 1), (" ", 0), ("", 0)]:
            src = f"""\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{{ if is_alphanumeric({json.dumps(s)}) then {{ 1 }} else {{ 0 }} }}
"""
            assert _run(src) == expected, f"is_alphanumeric({json.dumps(s)}) != {expected}"

    def test_is_whitespace(self) -> None:
        """is_whitespace: Python str.isspace() ASCII set — space(32),
        tab(9), LF(10), VT(11), FF(12), CR(13).  Non-whitespace and
        empty string return 0.

        Vera's lexer only recognizes \\n / \\t / \\r / \\0 as simple
        escapes (see `_SIMPLE_ESCAPES` in vera/transform.py); VT and
        FF are written as `\\u{0B}` / `\\u{0C}` unicode escapes.
        """
        cases = [
            (" ", 1),
            ("\t", 1),
            ("\n", 1),
            ("\u000b", 1),  # VT — spelled "\u{0B}" in Vera source
            ("\u000c", 1),  # FF — spelled "\u{0C}" in Vera source
            ("\r", 1),
            ("a", 0),
            ("0", 0),
            ("", 0),
        ]
        _VERA_ESCAPES = {"\u000b": '"\\u{0B}"', "\u000c": '"\\u{0C}"'}
        for s, expected in cases:
            literal = _VERA_ESCAPES.get(s, json.dumps(s))
            src = f"""\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{{ if is_whitespace({literal}) then {{ 1 }} else {{ 0 }} }}
"""
            assert _run(src) == expected, f"is_whitespace({literal}) != {expected}"

    def test_is_upper(self) -> None:
        """is_upper: 'A'..'Z' only."""
        for s, expected in [("A", 1), ("Z", 1), ("a", 0), ("5", 0), ("", 0)]:
            src = f"""\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{{ if is_upper({json.dumps(s)}) then {{ 1 }} else {{ 0 }} }}
"""
            assert _run(src) == expected, f"is_upper({json.dumps(s)}) != {expected}"

    def test_is_lower(self) -> None:
        """is_lower: 'a'..'z' only."""
        for s, expected in [("a", 1), ("z", 1), ("A", 0), ("5", 0), ("", 0)]:
            src = f"""\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{{ if is_lower({json.dumps(s)}) then {{ 1 }} else {{ 0 }} }}
"""
            assert _run(src) == expected, f"is_lower({json.dumps(s)}) != {expected}"

    def test_char_to_upper_first_only(self) -> None:
        """char_to_upper converts first char only; others untouched."""
        src = """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{ IO.print(char_to_upper("abc")) }
"""
        assert _run_io(src) == "Abc"

    def test_char_to_upper_non_letter_pass_through(self) -> None:
        """char_to_upper on non-letter first char: pass through."""
        src = """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{ IO.print(char_to_upper("5xy")) }
"""
        assert _run_io(src) == "5xy"

    def test_char_to_lower_first_only(self) -> None:
        """char_to_lower converts first char only; others untouched."""
        src = """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{ IO.print(char_to_lower("ABC")) }
"""
        assert _run_io(src) == "aBC"

    def test_char_to_upper_empty(self) -> None:
        """Empty string passes through."""
        src = """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{ IO.print(char_to_upper("")) }
"""
        assert _run_io(src) == ""

    def test_char_to_lower_empty(self) -> None:
        """Empty string passes through (mirror of char_to_upper)."""
        src = """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{ IO.print(char_to_lower("")) }
"""
        assert _run_io(src) == ""


class TestStringUtilities:
    """#470 — string_chars, lines, words, pad_start, pad_end, reverse,
    trim_start, trim_end.

    All inline WAT.  The Array<String>-returning ones (chars, lines,
    words) allocate each slice independently via ``$alloc`` rather
    than slicing into a shared backing buffer; the GC mark phase
    rejects interior pointers, so per-slice allocation is required
    for elements to stay reachable across collections triggered
    after the function returns.
    """

    def test_string_reverse(self) -> None:
        """Reverse bytes."""
        src = """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{ IO.print(string_reverse("hello")) }
"""
        assert _run_io(src) == "olleh"

    def test_string_reverse_empty(self) -> None:
        """Empty reverses to empty."""
        src = """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{ IO.print(string_reverse("")) }
"""
        assert _run_io(src) == ""

    def test_string_trim_start(self) -> None:
        """Strip leading whitespace only."""
        src = """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{ IO.print(string_trim_start("  hi  ")) }
"""
        assert _run_io(src) == "hi  "

    def test_string_trim_end(self) -> None:
        """Strip trailing whitespace only."""
        src = """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{ IO.print(string_trim_end("  hi  ")) }
"""
        assert _run_io(src) == "  hi"

    def test_string_trim_vt_ff_full_set(self) -> None:
        """Full Python isspace() ASCII set is recognised by both trim
        ends — exercises the same predicate _translate_trim shares
        with is_whitespace and string_strip.  VT (0x0B) and FF (0x0C)
        are spelled with unicode escapes since Vera's lexer doesn't
        recognise \\v / \\f as simple escapes.
        """
        # trim_start drops " \t\n\v\f\r" prefix; trim_end keeps only
        # the leading whitespace.
        src_start = """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{ IO.print(string_trim_start(" \\t\\n\\u{0B}\\u{0C}\\rhi ")) }
"""
        assert _run_io(src_start) == "hi "
        src_end = """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{ IO.print(string_trim_end(" hi \\t\\n\\u{0B}\\u{0C}\\r")) }
"""
        assert _run_io(src_end) == " hi"

    def test_string_trim_all_whitespace(self) -> None:
        """A string of only whitespace → empty (either variant).

        Check via length since an IO.print of an empty string leaves
        stdout empty too (indistinguishable from "print was never
        called" at the assertion layer).
        """
        src_start = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ nat_to_int(string_length(string_trim_start("   "))) }
"""
        src_end = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ nat_to_int(string_length(string_trim_end("   "))) }
"""
        assert _run(src_start) == 0
        assert _run(src_end) == 0

    def test_string_pad_start(self) -> None:
        """Left-pad with fill, cycling if needed."""
        # single-char fill
        src1 = """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{ IO.print(string_pad_start("x", 5, "0")) }
"""
        assert _run_io(src1) == "0000x"
        # multi-char fill cycles
        src2 = """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{ IO.print(string_pad_start("xx", 7, "ab")) }
"""
        # pad_len = 5, fill pattern a,b,a,b,a
        assert _run_io(src2) == "ababaxx"

    def test_string_pad_end(self) -> None:
        """Right-pad with fill, cycling."""
        src = """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{ IO.print(string_pad_end("xx", 7, "ab")) }
"""
        assert _run_io(src) == "xxababa"

    def test_string_pad_no_change_when_longer(self) -> None:
        """If input is already >= target, no pad."""
        src = """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{ IO.print(string_pad_start("hello", 3, "*")) }
"""
        assert _run_io(src) == "hello"

    def test_string_pad_end_no_change_when_longer(self) -> None:
        """Mirror: pad_end also returns input unchanged when too long."""
        src = """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{ IO.print(string_pad_end("hello", 3, "*")) }
"""
        assert _run_io(src) == "hello"

    def test_string_pad_empty_fill(self) -> None:
        """Empty fill string: no pad, input returned."""
        src = """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{ IO.print(string_pad_start("x", 5, "")) }
"""
        assert _run_io(src) == "x"

    def test_string_pad_end_empty_fill(self) -> None:
        """Mirror: pad_end with empty fill is a no-op too."""
        src = """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{ IO.print(string_pad_end("x", 5, "")) }
"""
        assert _run_io(src) == "x"

    def test_string_chars_length(self) -> None:
        """chars length == byte length."""
        src = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ nat_to_int(array_length(string_chars("abcde"))) }
"""
        assert _run(src) == 5

    def test_string_chars_empty(self) -> None:
        """chars of empty string is empty array."""
        src = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ nat_to_int(array_length(string_chars(""))) }
"""
        assert _run(src) == 0

    def test_string_chars_content(self) -> None:
        """Reassemble via join — chars + join should be identity."""
        src = """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{ IO.print(string_join(string_chars("abc"), "-")) }
"""
        assert _run_io(src) == "a-b-c"

    def test_string_lines_simple(self) -> None:
        """Basic \\n-separated lines."""
        src = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ nat_to_int(array_length(string_lines("a\\nb\\nc"))) }
"""
        assert _run(src) == 3

    def test_string_lines_crlf(self) -> None:
        """\\r\\n is one terminator (not two)."""
        src = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ nat_to_int(array_length(string_lines("a\\r\\nb\\r\\nc"))) }
"""
        assert _run(src) == 3

    def test_string_lines_cr_only(self) -> None:
        """Bare \\r is a terminator."""
        src = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ nat_to_int(array_length(string_lines("a\\rb\\rc"))) }
"""
        assert _run(src) == 3

    def test_string_lines_trailing_newline(self) -> None:
        """Trailing \\n does not add an empty final segment (splitlines)."""
        src = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ nat_to_int(array_length(string_lines("a\\nb\\n"))) }
"""
        assert _run(src) == 2

    def test_string_lines_empty(self) -> None:
        """Empty input → empty array (length 0)."""
        src = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ nat_to_int(array_length(string_lines(""))) }
"""
        assert _run(src) == 0

    def test_string_lines_content_via_join(self) -> None:
        """Lines + join with \\n should give back the source (modulo trailing \\n)."""
        src = """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{ IO.print(string_join(string_lines("foo\\nbar\\nbaz"), ",")) }
"""
        assert _run_io(src) == "foo,bar,baz"

    def test_string_lines_trailing_cr(self) -> None:
        """Trailing \\r: splitlines semantics — no empty trailing segment."""
        src = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ nat_to_int(array_length(string_lines("a\\r"))) }
"""
        # Just "a\r" → ["a"], length 1.
        assert _run(src) == 1

    def test_string_lines_trailing_crlf(self) -> None:
        """Trailing \\r\\n: splitlines semantics — no empty trailing segment.

        Distinct from ``test_string_lines_trailing_newline`` because
        CRLF is a two-byte terminator and the scanner advances past
        both in a single step.  Ensures that optimisation doesn't
        accidentally yield an extra empty segment.
        """
        src = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ nat_to_int(array_length(string_lines("a\\r\\nb\\r\\n"))) }
"""
        # ["a", "b"] — length 2, no empty trailing.
        assert _run(src) == 2

    def test_string_lines_interior_blank_lf(self) -> None:
        """Consecutive \\n preserves the empty interior line."""
        src = """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{ IO.print(string_join(string_lines("a\\n\\nb"), "|")) }
"""
        # "a\n\nb" → ["a", "", "b"] — join with "|" → "a||b".
        assert _run_io(src) == "a||b"

    def test_string_lines_interior_blank_cr(self) -> None:
        """Consecutive \\r also preserves an empty interior line."""
        src = """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{ IO.print(string_join(string_lines("a\\r\\rb"), "|")) }
"""
        # "a\r\rb" → ["a", "", "b"] — join with "|" → "a||b".
        assert _run_io(src) == "a||b"

    def test_string_words_simple(self) -> None:
        """Basic split on whitespace runs."""
        src = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ nat_to_int(array_length(string_words("foo bar baz"))) }
"""
        assert _run(src) == 3

    def test_string_words_runs(self) -> None:
        """Multiple whitespace chars count as one separator."""
        src = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ nat_to_int(array_length(string_words("  foo    bar  baz  "))) }
"""
        assert _run(src) == 3

    def test_string_words_empty(self) -> None:
        """Empty input → empty array."""
        src = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ nat_to_int(array_length(string_words(""))) }
"""
        assert _run(src) == 0

    def test_string_words_only_whitespace(self) -> None:
        """All-whitespace input → empty array (no words to emit)."""
        src = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ nat_to_int(array_length(string_words("   \\t\\n  "))) }
"""
        assert _run(src) == 0

    def test_string_words_vt_ff_separators(self) -> None:
        """VT (0x0B) and FF (0x0C) act as word separators too."""
        src = """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{ IO.print(string_join(string_words(" \\u{0B}foo\\u{0C}bar "), "|")) }
"""
        assert _run_io(src) == "foo|bar"

    def test_string_words_only_vt_ff(self) -> None:
        """All VT/FF input → empty array (matches Python str.split())."""
        src = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ nat_to_int(array_length(string_words(" \\u{0B}\\u{0C} "))) }
"""
        assert _run(src) == 0

    def test_string_words_content_via_join(self) -> None:
        """Words + join should give a canonicalised single-space-separated version."""
        src = """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{ IO.print(string_join(string_words("  foo\\tbar\\n\\nbaz  "), "|")) }
"""
        assert _run_io(src) == "foo|bar|baz"


class TestJsonTypedAccessors:
    """#366 — 11 new Json typed accessors shipped as pure-Vera prelude
    functions (no new WASM translators).  Six Layer-1 type-coercion
    accessors (Json → Option<T>) and five Layer-2 compound field
    accessors (Json, String → Option<T> = json_get + json_as_T
    composed).  ``json_as_int`` specifically guards every
    ``float_to_int`` (i.e. ``i64.trunc_f64_s``) trap path — NaN,
    +infinity, -infinity, and any finite float outside the
    closed-open i64 range ``[-2^63, 2^63)`` (that is,
    ``f >= 2^63`` or ``f < -2^63``; ``-2^63 = INT64_MIN`` is itself
    representable) — via ``float_is_nan`` / ``float_is_infinite``
    plus explicit bounds against ±9223372036854775808.0, returning
    ``None`` for every non-representable-as-Int input.
    """

    # ----- Layer 1: json_as_* -----

    def test_json_as_string_match(self) -> None:
        """JString("hi") → Some("hi")."""
        src = """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  match json_as_string(JString("hi")) {
    Some(@String) -> IO.print(@String.0),
    None -> IO.print("?")
  }
}
"""
        assert _run_io(src) == "hi"

    def test_json_as_string_mismatch(self) -> None:
        """JNumber(1.0) has no JString coercion → None."""
        src = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  match json_as_string(JNumber(1.0)) {
    Some(@String) -> 0,
    None -> 1
  }
}
"""
        assert _run(src) == 1

    def test_json_as_number_match(self) -> None:
        """JNumber(3.14) → Some(3.14)."""
        src = """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  match json_as_number(JNumber(3.14)) {
    Some(@Float64) -> IO.print(float_to_string(@Float64.0)),
    None -> IO.print("?")
  }
}
"""
        assert _run_io(src) == "3.14"

    def test_json_as_bool_match(self) -> None:
        """JBool(true) → Some(true); JBool(false) → Some(false)."""
        src_true = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  match json_as_bool(JBool(true)) {
    Some(@Bool) -> if @Bool.0 then { 1 } else { 0 },
    None -> -1
  }
}
"""
        assert _run(src_true) == 1
        src_false = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  match json_as_bool(JBool(false)) {
    Some(@Bool) -> if @Bool.0 then { 1 } else { 0 },
    None -> -1
  }
}
"""
        assert _run(src_false) == 0

    def test_json_as_int_truncates(self) -> None:
        """JNumber(42.7) → Some(42) via float_to_int truncation."""
        src = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  match json_as_int(JNumber(42.7)) {
    Some(@Int) -> @Int.0,
    None -> -1
  }
}
"""
        assert _run(src) == 42

    def test_json_as_int_negative(self) -> None:
        """JNumber(-3.9) → Some(-3) — i64.trunc_f64_s is toward-zero."""
        src = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  match json_as_int(JNumber(-3.9)) {
    Some(@Int) -> @Int.0,
    None -> 0
  }
}
"""
        assert _run(src) == -3

    def test_json_as_int_nan_returns_none(self) -> None:
        """JNumber(NaN) → None — guard prevents float_to_int trap.

        Without the `float_is_nan || float_is_infinite` guard in the
        prelude body, `float_to_int(NaN)` would trap.  This test
        pins that the accessor returns None cleanly instead.
        """
        src = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  match json_as_int(JNumber(0.0 / 0.0)) {
    Some(@Int) -> 0,
    None -> 1
  }
}
"""
        assert _run(src) == 1

    def test_json_as_int_infinity_returns_none(self) -> None:
        """JNumber(±inf) → None.  Both signs of infinity are trap
        inputs for ``i64.trunc_f64_s`` (distinct from the finite
        out-of-range case below) and the guard covers them via
        ``float_is_infinite``, which is sign-agnostic.
        """
        src_pos = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  match json_as_int(JNumber(infinity())) {
    Some(@Int) -> 0,
    None -> 1
  }
}
"""
        assert _run(src_pos) == 1
        src_neg = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  match json_as_int(JNumber(0.0 - infinity())) {
    Some(@Int) -> 0,
    None -> 1
  }
}
"""
        assert _run(src_neg) == 1

    def test_json_as_int_finite_overflow_returns_none(self) -> None:
        """JNumber with |f| >= 2^63 → None — the guard also covers
        finite-but-out-of-range values, not just NaN/infinity.

        ``i64.trunc_f64_s`` (emitted by ``float_to_int``) traps when
        the float exceeds the i64 range.  9223372036854775808.0 is
        exactly 2^63 in Float64 — representable but one above the
        maximum i64.  Without the range guard, this would trap.
        """
        src = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  match json_as_int(JNumber(9223372036854775808.0)) {
    Some(@Int) -> 0,
    None -> 1
  }
}
"""
        assert _run(src) == 1

    def test_json_as_int_finite_negative_overflow_returns_none(self) -> None:
        """JNumber with f < -2^63 → None (mirror of positive overflow)."""
        src = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  -- -2^64 is well outside i64 range.
  match json_as_int(JNumber(0.0 - 18446744073709551616.0)) {
    Some(@Int) -> 0,
    None -> 1
  }
}
"""
        assert _run(src) == 1

    def test_json_as_int_boundary_minus_2_63_is_representable(self) -> None:
        """JNumber(-2^63) → Some(INT64_MIN).

        The i64 range is closed on the low end (``[-2^63, 2^63)``):
        ``-2^63 = -9223372036854775808`` IS a valid Int.  This test
        pins both that ``Some`` is taken AND that the observed value
        is INT64_MIN (negative, and equal to itself under +1 overflow
        arithmetic).

        We probe the value indirectly because ``int_to_string(INT64_MIN)``
        hits a pre-existing bug (#475 bug 9: the negation step overflows
        i64, leaving an empty number body).  Two indirect probes pinpoint
        INT64_MIN without tripping that bug:
          (a) the value is negative: ``@Int.0 < 0`` holds,
          (b) ``@Int.0 + 1`` equals -9223372036854775807 (INT64_MIN + 1),
              which IS printable via ``int_to_string``.
        Off-by-one on the guard (``f <= -2^63`` instead of ``f < -2^63``)
        would reject this valid value; an accidental truncation to zero
        or positive value would fail probe (a).
        """
        src = """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  match json_as_int(JNumber(0.0 - 9223372036854775808.0)) {
    Some(@Int) -> {
      -- Probe (a): value is negative.
      IO.print(bool_to_string(@Int.0 < 0));
      IO.print(",");
      -- Probe (b): value + 1 = INT64_MIN + 1 = -9223372036854775807.
      IO.print(int_to_string(@Int.0 + 1))
    },
    None -> IO.print("none")
  }
}
"""
        assert _run_io(src) == "true,-9223372036854775807"

    def test_json_as_int_boundary_just_below_minus_2_63(self) -> None:
        """The Float64 value strictly below -2^63 must return None.

        Float64 precision at magnitude ~2^63 has ulp = 2^(63-52) =
        2048, so the next representable double below -2^63 is
        -2^63 - 2048 = -9223372036854777856.0.  A literal like
        -9223372036854776832.0 (= -2^63 - 1024) is *not*
        representable: it's exactly halfway between -2^63 and the
        next-lower double, and round-to-nearest-even rounds it back
        to -2^63.  Using the true next-lower value pins the guard's
        strict-less-than behaviour at the boundary.
        """
        src = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  match json_as_int(JNumber(0.0 - 9223372036854777856.0)) {
    Some(@Int) -> 0,
    None -> 1
  }
}
"""
        assert _run(src) == 1

    def test_json_as_array(self) -> None:
        """JArray([1,2,3]) → Some(array of length 3)."""
        src = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Json = JArray([JNumber(1.0), JNumber(2.0), JNumber(3.0)]);
  match json_as_array(@Json.0) {
    Some(@Array<Json>) -> nat_to_int(array_length(@Array<Json>.0)),
    None -> 0
  }
}
"""
        assert _run(src) == 3

    def test_json_as_object_from_parse(self) -> None:
        """JObject value via json_parse → Some(map); Map is opaque
        handle so we only assert round-trip, not contents."""
        src = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  match json_parse("{\\"k\\":1}") {
    Err(@String) -> 0,
    Ok(@Json) ->
      match json_as_object(@Json.0) {
        Some(@Map<String, Json>) -> 1,
        None -> 0
      }
  }
}
"""
        assert _run(src) == 1

    def test_json_as_coercions_are_disjoint(self) -> None:
        """Every Layer-1 accessor returns None for every constructor
        except its own.  This is the invariant callers rely on when
        chaining coercions.
        """
        src = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  -- JString has no bool coercion
  let @Int = match json_as_bool(JString("true")) {
    Some(@Bool) -> -1,
    None -> 0
  };
  -- JBool has no number coercion
  let @Int = match json_as_number(JBool(true)) {
    Some(@Float64) -> -1,
    None -> @Int.0
  };
  -- JNumber has no string coercion
  let @Int = match json_as_string(JNumber(1.0)) {
    Some(@String) -> -1,
    None -> @Int.0
  };
  -- JNull has no array coercion
  let @Int = match json_as_array(JNull) {
    Some(@Array<Json>) -> -1,
    None -> @Int.0
  };
  @Int.0
}
"""
        assert _run(src) == 0

    # ----- Layer 2: json_get_* -----

    def test_json_get_string_hit(self) -> None:
        """{"name":"Alice"}/name → Some("Alice")."""
        src = """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  match json_parse("{\\"name\\":\\"Alice\\"}") {
    Err(@String) -> IO.print("ERR"),
    Ok(@Json) ->
      match json_get_string(@Json.0, "name") {
        Some(@String) -> IO.print(@String.0),
        None -> IO.print("?")
      }
  }
}
"""
        assert _run_io(src) == "Alice"

    def test_json_get_int_hit(self) -> None:
        """{"age":30}/age → Some(30)."""
        src = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  match json_parse("{\\"age\\":30}") {
    Err(@String) -> -1,
    Ok(@Json) ->
      match json_get_int(@Json.0, "age") {
        Some(@Int) -> @Int.0,
        None -> -1
      }
  }
}
"""
        assert _run(src) == 30

    def test_json_get_number_hit(self) -> None:
        """{"score":3.14}/score → Some(3.14)."""
        src = """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  match json_parse("{\\"score\\":3.14}") {
    Err(@String) -> IO.print("ERR"),
    Ok(@Json) ->
      match json_get_number(@Json.0, "score") {
        Some(@Float64) -> IO.print(float_to_string(@Float64.0)),
        None -> IO.print("?")
      }
  }
}
"""
        assert _run_io(src) == "3.14"

    def test_json_get_bool_hit(self) -> None:
        """{"active":true}/active → Some(true)."""
        src = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  match json_parse("{\\"active\\":true}") {
    Err(@String) -> -1,
    Ok(@Json) ->
      match json_get_bool(@Json.0, "active") {
        Some(@Bool) -> if @Bool.0 then { 1 } else { 0 },
        None -> -1
      }
  }
}
"""
        assert _run(src) == 1

    def test_json_get_array_hit(self) -> None:
        """{"tags":[1,2,3]}/tags → Some(array of length 3)."""
        src = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  match json_parse("{\\"tags\\":[1,2,3]}") {
    Err(@String) -> -1,
    Ok(@Json) ->
      match json_get_array(@Json.0, "tags") {
        Some(@Array<Json>) -> nat_to_int(array_length(@Array<Json>.0)),
        None -> -1
      }
  }
}
"""
        assert _run(src) == 3

    def test_json_get_missing_field(self) -> None:
        """Missing field → None."""
        src = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  match json_parse("{\\"name\\":\\"Alice\\"}") {
    Err(@String) -> -1,
    Ok(@Json) ->
      match json_get_int(@Json.0, "nope") {
        Some(@Int) -> -1,
        None -> 1
      }
  }
}
"""
        assert _run(src) == 1

    def test_json_get_wrong_type(self) -> None:
        """Present field with wrong type → None (not trap)."""
        src = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  match json_parse("{\\"name\\":\\"Alice\\"}") {
    Err(@String) -> -1,
    Ok(@Json) ->
      match json_get_int(@Json.0, "name") {
        Some(@Int) -> -1,
        None -> 1
      }
  }
}
"""
        assert _run(src) == 1

    def test_json_get_on_non_object(self) -> None:
        """json_get_X on a non-JObject Json returns None (because the
        underlying json_get returns None for non-objects).
        """
        src = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  -- JArray is a valid Json but not an object, so json_get_int returns None.
  match json_get_int(JArray([JNumber(1.0)]), "any") {
    Some(@Int) -> -1,
    None -> 1
  }
}
"""
        assert _run(src) == 1

    # ----- Import gating: accessors are pure-Vera, not host imports -----

    def test_accessors_do_not_force_json_parse_import(self) -> None:
        """A program that uses only json_as_* / json_get_* accessors
        must NOT import vera.json_parse or vera.json_stringify.  These
        accessors are pure-Vera prelude functions; the host imports
        are only for the parse/serialise boundary.

        Regression test: a future refactor that accidentally routes an
        accessor through a host import would make the compiled module
        pull in unused imports.  Caught here by the import table.
        """
        src = """\
public fn test(@Json -> @Option<String>)
  requires(true) ensures(true) effects(pure)
{
  match json_get_string(@Json.0, "k") {
    Some(@String) -> Some(@String.0),
    None -> json_as_string(@Json.0)
  }
}
"""
        result = _compile_ok(src)
        assert '(import "vera" "json_parse"' not in result.wat, (
            "json_as_* / json_get_* must not force the json_parse host "
            "import — they are pure-Vera prelude functions."
        )
        assert '(import "vera" "json_stringify"' not in result.wat, (
            "json_as_* / json_get_* must not force the json_stringify "
            "host import."
        )

    def test_layer2_accessors_do_not_force_json_imports(self) -> None:
        """Mirror: json_get_int / json_get_array also pure.  Separate
        test because the accessors have slightly different return-type
        shapes (i64 payload vs i32_pair Array) and codegen might
        conceivably diverge between them.
        """
        src = """\
public fn test(@Json -> @Option<Int>)
  requires(true) ensures(true) effects(pure)
{
  match json_get_int(@Json.0, "age") {
    Some(@Int) -> Some(@Int.0),
    None ->
      match json_get_array(@Json.0, "tags") {
        Some(@Array<Json>) -> Some(nat_to_int(array_length(@Array<Json>.0))),
        None -> None
      }
  }
}
"""
        result = _compile_ok(src)
        assert '(import "vera" "json_parse"' not in result.wat
        assert '(import "vera" "json_stringify"' not in result.wat

    def test_json_parse_does_force_its_host_import(self) -> None:
        """Complementary test: json_parse IS a host import, so a
        program using it SHOULD emit the corresponding import.  Pins
        the direction of the invariant — if this test ever fails
        without the previous two also failing, the check is wrong,
        not the implementation.
        """
        src = """\
public fn test(@String -> @Result<Json, String>)
  requires(true) ensures(true) effects(pure)
{ json_parse(@String.0) }
"""
        result = _compile_ok(src)
        assert '(import "vera" "json_parse"' in result.wat, (
            "json_parse IS a host import and its import table entry "
            "must be present when the function is referenced."
        )


class TestGCShadowStackOverflow:
    """Regression tests for #464: deep recursive array accumulation
    overflowing the GC shadow stack into the worklist region.

    With a 4K shadow stack, build_acc (2 Array<Bool> params + 1 array_append
    dst = 12 bytes/frame) overflows at ~341 frames.  The overflow corrupted
    the GC worklist, causing incorrect mark/sweep and silent data corruption
    in the first few array elements.

    Fixed by increasing the shadow stack to 16K and adding an overflow guard.
    """

    def test_deep_array_accumulation_bool(self) -> None:
        """450-deep recursion with Array<Bool> accumulator."""
        src = """
private fn build_acc(@Array<Bool>, @Array<Bool>, @Int -> @Array<Bool>)
  requires(@Int.0 >= 0)
  ensures(true)
  decreases(@Int.0)
  effects(pure)
{
  if @Int.0 <= 0 then { @Array<Bool>.0 }
  else {
    build_acc(
      @Array<Bool>.1,
      array_append(@Array<Bool>.0, false),
      @Int.0 - 1
    )
  }
}

private fn first_bool(@Array<Bool> -> @Int)
  requires(array_length(@Array<Bool>.0) > 0)
  ensures(true)
  effects(pure)
{
  if @Array<Bool>.0[0] then { 1 } else { 0 }
}

public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  first_bool(build_acc([false], [false, false, false], 450))
}
"""
        assert _run(src) == 0  # first element must be false

    def test_shadow_stack_overflow_traps(self) -> None:
        """Overflow guard traps instead of silently corrupting memory.

        Uses a NON-tail-recursive shape so each iteration stacks a
        WASM frame and a fresh window of shadow-stack roots.

        #549 made tail-recursive allocating functions safe (per-
        iteration `$gc_sp` restore before each `return_call` keeps
        shadow-stack usage flat regardless of iteration count).
        Pre-#549 this test used a tail-recursive form that would
        leak shadow-stack slots; post-#549 such a form runs cleanly
        forever and no longer exercises the overflow guard.

        To still exercise the guard, this test wraps the recursive
        call in `array_append`, which moves it OUT of tail position.
        The non-tail call stacks WASM frames, each frame's shadow-
        stack roots survive across iterations, and at sufficient
        depth the overflow guard trips.

        Two-step assertion:
        1. Structural — the WAT for `overflow` contains the shadow-
           stack-overflow guard sequence (`global.get $gc_sp;
           global.get $gc_stack_limit; i32.ge_u; if; unreachable;
           end`).  Without this, a regression that silently drops
           the guard could still pass `_run_trap` via an unrelated
           trap class (e.g. heap exhaustion at a different scale).
        2. Behavioural — `_run_trap` confirms the program actually
           traps at the chosen 2000-iteration depth.

        Iteration count calibration: the 16K shadow stack holds
        ~4096 pointer slots (4 bytes each).  Each `overflow` frame
        pushes 2 `@Array<Bool>` params (8 bytes) + 1 array_append
        tmp root (4 bytes) = 12 bytes/frame, so the guard trips at
        ~1,365 frames.  2000 chosen with ~1.5× safety margin so
        the trap fires reliably even if per-frame size shrinks by
        a slot in a future optimisation.
        """
        src = """
private fn overflow(@Array<Bool>, @Array<Bool>, @Int -> @Array<Bool>)
  requires(@Int.0 >= 0)
  ensures(true)
  decreases(@Int.0)
  effects(pure)
{
  if @Int.0 <= 0 then { @Array<Bool>.0 }
  else {
    -- Wrapping the recursive call in array_append puts it out of
    -- tail position, so the call site emits plain `call` (not
    -- `return_call`) and each iteration genuinely stacks a frame.
    array_append(
      overflow(
        @Array<Bool>.1,
        array_append(@Array<Bool>.0, false),
        @Int.0 - 1
      ),
      true
    )
  }
}

public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  array_length(overflow([false], [false], 2000))
}
"""
        # Structural check: the WAT for `overflow` must contain
        # the shadow-stack overflow guard.  The distinctive token
        # is `global.get $gc_stack_limit`, which is only used by
        # this guard in the entire emission surface.
        #
        # Boundary-safe extraction (\b after `$overflow`) so a
        # future symbol like `$overflow_helper` couldn't false-
        # match the function-start search.
        compiled = _compile_ok(src)
        overflow_match = re.search(r"\(func \$overflow\b", compiled.wat)
        assert overflow_match is not None, (
            "`$overflow` function not found in emitted WAT"
        )
        overflow_start = overflow_match.start()
        next_fn = re.search(
            r"\(func \$", compiled.wat[overflow_start + 1:]
        )
        overflow_end = (
            overflow_start + 1 + next_fn.start()
            if next_fn is not None
            else len(compiled.wat)
        )
        overflow_body = compiled.wat[overflow_start:overflow_end]
        # The guard sequence emitted by `gc_shadow_push` in
        # `vera/wasm/helpers.py` is:
        #     global.get $gc_sp
        #     global.get $gc_stack_limit
        #     i32.ge_u
        #     if
        #       unreachable
        #     end
        # Check the distinctive parts as a substring; whitespace
        # between lines may vary depending on emission context.
        assert "global.get $gc_stack_limit" in overflow_body, (
            f"Shadow-stack overflow guard missing from `$overflow` "
            f"body — codegen must emit `global.get $gc_stack_limit` "
            f"as part of every shadow-stack push.  Without the "
            f"guard, _run_trap below could still pass via an "
            f"unrelated trap class.  Body:\n{overflow_body[:2000]}"
        )
        # Behavioural check: the program actually traps.
        _run_trap(src)

    def test_deep_array_accumulation_preserves_length(self) -> None:
        """Verify array length is correct after deep single-param accumulation."""
        src = """
private fn build_acc(@Array<Bool>, @Int -> @Array<Bool>)
  requires(@Int.0 >= 0)
  ensures(true)
  decreases(@Int.0)
  effects(pure)
{
  if @Int.0 <= 0 then { @Array<Bool>.0 }
  else {
    build_acc(array_append(@Array<Bool>.0, false), @Int.0 - 1)
  }
}

public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  array_length(build_acc([], 500))
}
"""
        assert _run(src) == 500


# =====================================================================
# Wrapper-handle bit-31 tagging (#578)
# =====================================================================

class TestWrapperHandleTagging578:
    """Regression tests for #578: wrapper-handle field bit-31 tagging.

    Surfaced by CodeRabbit on PR #577 (#573 phase 1-3).  After
    #573, every `Map<K, V>` / `Set<T>` / `Decimal` value is a
    pointer to an 8-byte wrapper ADT on the GC heap: tag (i32) at
    offset 0, handle (i32) at offset 4.  Phase 2b of `$gc_collect`
    does a conservative word-by-word scan of every reachable
    object's payload, checking whether each i32 word looks like a
    heap pointer (in heap range, 8-byte aligned).

    Pre-#578 the raw host handle (a small positive integer) was
    stored at offset 4.  For typical programs the handle stays
    below `gc_heap_start` (~144 KiB above the data section, so
    roughly 144 KiB plus the string-pool size) so the heap-range check
    rejects it.  But for very-long-running programs allocating
    >100K host handles per `execute()`, the handle counter could
    exceed `gc_heap_start` and (with the right alignment) be
    falsely classified as a heap pointer — silently retaining an
    unrelated heap object.  A *retention* issue, not a correctness
    one (no use-after-free, no corruption), but unbounded
    retention for long sessions.

    Post-#578 the handle is stored as `handle | 0x80000000` so
    the in-heap field is always >= 2 GiB, structurally outside
    any heap-range check (the `$alloc` heap-ceiling guard
    enforces `heap_ptr < 0x80000000`).  The unwrap site ANDs
    with 0x7FFFFFFF to recover the raw handle.

    #706: `Map` / `Set` are now bucket-as-truth — their wrappers
    carry no host handle (the +4 field is vestigial), so they no
    longer wrap/unwrap.  `Decimal` keeps the value-typed Python
    store and is the remaining type exercising the bit-31 tagging,
    so these codegen tests use a Decimal program.
    """

    def test_wrap_emits_tag_or(self) -> None:
        """Wrap site emits `i32.const 0x80000000; i32.or; i32.store offset=4`.

        Pin the FULL 3-instruction wrap-site sequence — not just
        the `const`/`or` pair.  The header-mark path also has an
        `i32.or` and the heap-ceiling guard also has the constant;
        only the wrap site emits all three with `i32.store
        offset=4` (the wrapper-body handle field).  Including the
        store in the regex pins the SEMANTIC intent (tagging
        immediately precedes the field store) rather than the
        accidental fact that the const-or pair happens to be
        unique today.  Symmetric with `test_unwrap_emits_mask_and`
        which already pins the full 3-instruction unwrap sequence.
        """
        source = """\
public fn main(@Unit -> @Decimal)
  requires(true) ensures(true) effects(pure)
{
  decimal_add(decimal_from_int(1), decimal_from_int(2))
}
"""
        result = _compile_ok(source)
        # `\s+` matches newlines + indentation between adjacent
        # WAT instructions.
        assert re.search(
            r"i32\.const 0x80000000\s+i32\.or\s+i32\.store offset=4",
            result.wat,
        ), (
            "Expected adjacent `i32.const 0x80000000; i32.or; "
            "i32.store offset=4` sequence (the wrap-site tag "
            "emission immediately followed by the wrapper-field "
            "store).  Without #578, the wrap site stores the raw "
            "handle and this sequence never appears."
        )

    def test_unwrap_emits_mask_and(self) -> None:
        """Unwrap site emits adjacent load-const-and sequence."""
        source = """\
public fn main(@Unit -> @Decimal)
  requires(true) ensures(true) effects(pure)
{
  decimal_add(decimal_from_int(1), decimal_from_int(2))
}
"""
        result = _compile_ok(source)
        # Pin the exact 3-instruction sequence the unwrap helper
        # emits: load offset=4, const 0x7FFFFFFF, and.  Loose
        # substring `0x7FFFFFFF in wat` would survive a future
        # unrelated use of the mask constant; this won't.
        assert re.search(
            r"i32\.load\s+offset=4"
            r"\s+i32\.const 0x7FFFFFFF"
            r"\s+i32\.and",
            result.wat,
        ), (
            "Expected adjacent unwrap sequence "
            "`i32.load offset=4; i32.const 0x7FFFFFFF; i32.and`. "
            "Without #578, the unwrap reads the tagged value "
            "raw and `map_store` lookups would fail."
        )

    def test_alloc_emits_heap_ceiling_guard(self) -> None:
        """$alloc traps if heap_ptr + total would exceed 0x80000000.

        The structural counterpart to the wrap-site tag: the
        guard ensures `heap_ptr < 0x80000000` always, so tagged
        handles (>= 2 GiB) and heap pointers (< 2 GiB) are
        guaranteed disjoint.  Without this guard a 3+ GiB heap
        could produce real pointers in the tagged-handle range,
        reintroducing the spurious-retention bug.

        The guard is overflow-safe: it rejects allocations with
        `total >= 2 GiB` first, then checks
        `heap_ptr >= 0x80000000 - total` via SUBTRACTION.  An
        `i32.add` form could wrap on overflow (`heap_ptr =
        0xFFFFFFFF, total = 10` wraps to `0x09`, below the
        ceiling, silent bypass).  Upstream `memory.grow` makes
        the wraparound unreachable in practice but the algebraic
        gap is real.

        Pin both ordered sequences — not just constant presence.
        """
        source = """\
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Map<Int, Int> = map_insert(map_new(), 1, 100);
  option_unwrap_or(map_get(@Map<Int, Int>.0, 1), 0)
}
"""
        result = _compile_ok(source)
        # Locate $alloc via boundary-safe regex (not `find()`,
        # which could false-match an `$alloc_xxx` symbol).
        alloc_match = re.search(r"\(func \$alloc\b", result.wat)
        assert alloc_match is not None, (
            "`$alloc` function not found in WAT"
        )
        alloc_start = alloc_match.start()
        next_fn = re.search(
            r"\(func \$", result.wat[alloc_start + 1:],
        )
        alloc_end = (
            alloc_start + 1 + next_fn.start()
            if next_fn is not None
            else len(result.wat)
        )
        alloc_body = result.wat[alloc_start:alloc_end]
        # Step 1: total < 2 GiB precheck (rejects pathologically
        # large single allocations and prevents underflow in
        # step 2's subtraction).
        step1 = re.search(
            r"local\.get \$total"
            r"\s+i32\.const 0x80000000"
            r"\s+i32\.ge_u"
            r"\s+if"
            r"\s+unreachable"
            r"\s+end",
            alloc_body,
            re.DOTALL,
        )
        assert step1 is not None, (
            f"Heap-ceiling step 1 (total < 2 GiB precheck) not "
            f"found in $alloc body.  Without it, step 2's "
            f"`i32.sub` could underflow on a pathological total. "
            f"$alloc body:\n{alloc_body[:2000]}"
        )
        # Step 2: heap_ptr >= 0x80000000 - total → trap.  Pinned
        # AFTER step 1 by anchoring the search from step 1's end.
        rest = alloc_body[step1.end():]
        step2 = re.search(
            r"global\.get \$heap_ptr"
            r"\s+i32\.const 0x80000000"
            r"\s+local\.get \$total"
            r"\s+i32\.sub"
            r"\s+i32\.ge_u"
            r"\s+if"
            r"\s+unreachable"
            r"\s+end",
            rest,
            re.DOTALL,
        )
        assert step2 is not None, (
            f"Heap-ceiling step 2 (overflow-safe subtraction "
            f"check) not found after step 1 in $alloc body.  An "
            f"`i32.add` form would be vulnerable to wraparound "
            f"(heap_ptr=0xFFFFFFFF, total=10 wraps to 0x09, below "
            f"the ceiling, silent bypass).  Step 2 must use "
            f"`i32.sub` for overflow safety.  $alloc body:\n"
            f"{alloc_body[:2000]}"
        )

    def test_wrap_unwrap_round_trip_preserves_handle(self) -> None:
        """Behavioural: wrap-then-unwrap recovers the original handle.

        End-to-end smoke test that the tag+mask combination
        round-trips correctly for a real Map operation.  A bug
        in either direction (wrong mask, wrong constant, wrong
        order of operations) would produce a corrupted handle
        and the `map_get` lookup would either trap or return
        a wrong value.
        """
        source = """\
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Map<Int, Int> = map_insert(map_new(), 42, 12345);
  let @Map<Int, Int> = map_insert(@Map<Int, Int>.0, 100, 67890);
  let @Int = option_unwrap_or(map_get(@Map<Int, Int>.0, 42), -1);
  let @Int = option_unwrap_or(map_get(@Map<Int, Int>.0, 100), -1);
  @Int.0 + @Int.1
}
"""
        # Expected: 42 -> 12345, 100 -> 67890. Sum = 80235.
        # If the wrap/unwrap round-trip is broken, this either
        # traps on host-side `map_store[bad_handle]` lookup or
        # returns -1 + -1 = -2.
        assert _run(source) == 80235

    def test_html_round_trip_uses_host_side_mask(self) -> None:
        """Host-side reader applies the 0x7FFFFFFF mask.

        `vera/wasm/html_serde.py::read_html` reads
        `wrapper_ptr + 4` directly (via wasmtime memory access)
        rather than going through the WAT `_emit_unwrap_handle`
        helper.  Post-#578 that read sees the TAGGED value and
        must AND with 0x7FFFFFFF before looking up the host-side
        `map_store`.  Without the mask the lookup would miss and
        `html_to_string` would emit an element with empty
        attributes.

        Pin the EXACT serialized output (not just length) so a
        hypothetical bug that produced wrong content with the
        right length (e.g. `<p title="WRONG"></p>` — also 21
        chars) would still fail.  `IO.print` + `_run_io` captures
        the rendered output for direct string comparison.
        """
        source = _IO_PRELUDE + """\
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Map<String, String> = map_insert(map_new(), "title", "hello");
  IO.print(html_to_string(HtmlElement("p", @Map<String, String>.0, [])))
}
"""
        # Exact rendered output.  Without the host-side mask the
        # attribute dict would be empty and the output would be
        # `<p></p>` instead.
        assert _run_io(source, fn="main") == '<p title="hello"></p>'

    def test_json_round_trip_uses_host_side_mask(self) -> None:
        """Host-side JSON reader applies the 0x7FFFFFFF mask.

        Sibling of `test_html_round_trip_uses_host_side_mask`.
        `vera/wasm/json_serde.py::read_json` reads
        `wrapper_ptr + 4` directly (via wasmtime memory access)
        rather than going through the WAT `_emit_unwrap_handle`
        helper.  Post-#578 that read sees the TAGGED value and
        must AND with 0x7FFFFFFF before looking up the host-side
        `map_store`.  Without the mask the lookup would miss,
        `read_json` would fall through to the "unknown JObject
        handle" warning + empty-dict path, and `json_stringify`
        would emit `{}` instead of the object.

        Pin the EXACT serialized output (not just length) so a
        hypothetical bug that produced wrong content with the
        right length (e.g. `{"name": "BB"}` — also 14 chars)
        would still fail.
        """
        source = _IO_PRELUDE + """\
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Json = JObject(map_insert(map_new(), "name", JString("hi")));
  IO.print(json_stringify(@Json.0))
}
"""
        # Exact rendered output.  Python's json.dumps default
        # separators include a space after the colon, so the
        # form is `{"name": "hi"}` (NOT the compact `{"name":"hi"}`).
        # Without the host-side mask json_stringify would emit
        # `{}` instead.
        assert _run_io(source, fn="main") == '{"name": "hi"}'

    # --- Unit tests for the _validate_wrap_handle helper ---
    #
    # The validator is module-scope in `vera/codegen/api.py` so it
    # can be tested directly without standing up a wasmtime
    # instance.  `_wrap_handle` (nested inside `execute()`) calls
    # this helper.  These tests pin all 5 failure modes the
    # validator rejects.

    def test_validate_wrap_handle_accepts_valid_range(self) -> None:
        """[0, 0x80000000) is the accepted range — no raise."""
        from vera.codegen.api import _validate_wrap_handle
        # Boundary lo, mid, boundary hi (last valid).
        for raw in (0, 1, 12345, 0x7FFFFFFE, 0x7FFFFFFF):
            _validate_wrap_handle(raw, kind=1, body_ptr=0x1000)

    def test_validate_wrap_handle_rejects_negative(self) -> None:
        """Negative ints have bit 31 set in two's complement."""
        from vera.codegen.api import _validate_wrap_handle
        with pytest.raises(RuntimeError, match="#578.*outside the valid"):
            _validate_wrap_handle(-1, kind=1, body_ptr=0x1000)
        with pytest.raises(RuntimeError, match="#578"):
            _validate_wrap_handle(-12345, kind=2, body_ptr=0x2000)

    def test_validate_wrap_handle_rejects_at_2gb_boundary(self) -> None:
        """0x80000000 is the FIRST invalid value (range is half-open)."""
        from vera.codegen.api import _validate_wrap_handle
        with pytest.raises(RuntimeError, match="0x80000000"):
            _validate_wrap_handle(0x80000000, kind=1, body_ptr=0x1000)

    def test_validate_wrap_handle_rejects_above_32bit(self) -> None:
        """Values >= 2^32 truncate on _write_i32 — must be caught here.

        The pre-tightening (round 1) bit-31-only check let these
        through: `0x100000001 & 0x80000000 == 0`, so the check
        passed, but `_write_i32` would truncate to `0x00000001`
        and the unwrap mask would return that — a silent wrong
        handle.
        """
        from vera.codegen.api import _validate_wrap_handle
        with pytest.raises(RuntimeError, match="#578"):
            _validate_wrap_handle(0x100000000, kind=1, body_ptr=0x1000)
        with pytest.raises(RuntimeError, match="#578"):
            _validate_wrap_handle(0x100000001, kind=1, body_ptr=0x1000)

    def test_validate_wrap_handle_rejects_non_int(self) -> None:
        """Non-int sentinels surface here, not deeper in the stack.

        Without the type check, `None` / `"5"` / etc. would
        raise `TypeError` from the bitwise `&` operation in the
        old check, producing a less actionable error.
        """
        from vera.codegen.api import _validate_wrap_handle
        for bad in (None, "5", 1.5, [1], {}):
            with pytest.raises(RuntimeError, match="#578"):
                _validate_wrap_handle(bad, kind=1, body_ptr=0x1000)

    def test_validate_wrap_handle_rejects_bool(self) -> None:
        """bool is rejected despite Python's bool-subclasses-int rule.

        `isinstance(True, int)` is `True` because `bool` is a
        subclass of `int` in Python.  An `isinstance`-only check
        would let `True` / `False` slip through and silently alias
        to handles 1 and 0 respectively — exactly the silent-
        corruption class #578 sought to eliminate.  The validator
        uses `type(raw_handle) is int` rather than `isinstance`,
        which rejects bool while still accepting plain int.
        """
        from vera.codegen.api import _validate_wrap_handle
        with pytest.raises(RuntimeError, match="#578"):
            _validate_wrap_handle(True, kind=1, body_ptr=0x1000)
        with pytest.raises(RuntimeError, match="#578"):
            _validate_wrap_handle(False, kind=1, body_ptr=0x1000)


# =====================================================================
# @Nat subtraction underflow runtime guard (#520)
# =====================================================================

class TestNatSubtractionRuntimeGuard520:
    """Codegen emits a runtime underflow guard for `@Nat - @Nat`.

    The verifier (vera/verifier.py, #520 commit b446cac) emits a
    Tier-1 proof obligation `lhs >= rhs` at every @Nat-Nat
    subtraction site.  The codegen mirrors that detection (same
    helpers — _is_static_nat_typed + _has_nat_origin_codegen) and
    emits a runtime guard that traps on underflow.

    The guard exists because `vera compile` doesn't run the verifier
    — programs that skip `vera verify` would otherwise produce
    silent negative @Nat values.  When verification has run and
    discharged the obligation statically, the runtime guard is
    redundant but cheap (one i64 compare + branch); a Tier-1
    skip-channel is a future optimization.
    """

    # Body uses `@Nat.1 - @Nat.0` (first param minus second param)
    # rather than `@Nat.0 - @Nat.1` so the call-site argument order
    # reads naturally — De Bruijn `@T.0` is the most recent (last)
    # binding, so `unsafe(a, b)` with body `@Nat.0 - @Nat.1` would be
    # `b - a` and easy to misread.  See CLAUDE.md / DE_BRUIJN.md.
    _GUARDED_SUB = """
private fn unsafe(@Nat, @Nat -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Nat.1 - @Nat.0
}

public fn main(@Unit -> @Nat)
  requires(true) ensures(true) effects(pure)
{
  unsafe(0, 1)
}
"""

    _SAFE_SUB = """
private fn safe(@Nat, @Nat -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Nat.1 - @Nat.0
}

public fn main(@Unit -> @Nat)
  requires(true) ensures(true) effects(pure)
{
  safe(5, 3)
}
"""

    def test_underflow_traps_at_runtime(self) -> None:
        """unsafe(0, 1) traps via the runtime guard.

        Without the guard, `i64.sub` would produce -1 silently and
        store it in a @Nat slot, violating the type invariant. With
        the guard, the function traps cleanly before the bad value
        propagates.
        """
        result = _compile_ok(self._GUARDED_SUB)
        with pytest.raises((wasmtime.WasmtimeError, wasmtime.Trap, RuntimeError)):
            execute(result, fn_name="main", args=[])

    def test_safe_subtraction_returns_correct_result(self) -> None:
        """safe(5, 3) returns 2 — guard passes through cleanly.

        The guard is `if (i64.lt_s lhs rhs) then unreachable end`, so
        when lhs >= rhs the branch is not taken and the subtraction
        proceeds normally.  Confirms the guard doesn't introduce a
        regression on the happy path.
        """
        assert _run(self._SAFE_SUB) == 2

    def test_guard_emitted_in_wat_for_nat_sub(self) -> None:
        """The guarded WAT contains `i64.lt_s` and `unreachable`.

        Structural assertion that the codegen actually inserted the
        guard sequence rather than emitting a bare `i64.sub`.  The
        unguarded WAT (e.g. for `@Int - @Int`) would contain
        `i64.sub` but no `i64.lt_s` paired with `unreachable`.
        """
        result = _compile_ok(self._GUARDED_SUB)
        wat = result.wat
        # Both the comparison and the trap must appear inside `unsafe`
        # (the function with the @Nat-Nat subtraction).
        unsafe_idx = wat.find("(func $unsafe")
        assert unsafe_idx >= 0, "unsafe function not found in WAT"
        # Slice out the `unsafe` body up to the next top-level paren.
        body_end = wat.find("\n  (func ", unsafe_idx + 1)
        if body_end < 0:
            body_end = len(wat)
        body = wat[unsafe_idx:body_end]
        assert "i64.lt_s" in body, (
            f"Expected `i64.lt_s` in unsafe body for underflow guard, "
            f"got: {body!r}"
        )
        assert "unreachable" in body, (
            f"Expected `unreachable` in unsafe body for underflow guard, "
            f"got: {body!r}"
        )

    def test_int_subtract_emits_no_guard(self) -> None:
        """`@Int - @Int` does not get the guard — Int can be negative.

        Sister to the structural test above: the guard fires only on
        sites where the result is statically @Nat AND at least one
        operand has @Nat origin.  Int-Int sites must emit a bare
        `i64.sub` with no `i64.lt_s`/`unreachable` pair adjacent.
        """
        src = """
private fn int_sub(@Int, @Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Int.0 - @Int.1
}

public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  int_sub(5, 10)
}
"""
        result = _compile_ok(src)
        wat = result.wat
        int_sub_idx = wat.find("(func $int_sub")
        assert int_sub_idx >= 0
        body_end = wat.find("\n  (func ", int_sub_idx + 1)
        if body_end < 0:
            body_end = len(wat)
        body = wat[int_sub_idx:body_end]
        # i64.sub must be present (it's the actual subtraction).
        assert "i64.sub" in body
        # But the guard pieces must NOT be — Int subtraction is unguarded.
        # Banning *both* `i64.lt_s` and `i64.lt_u` (regex
        # `\bi64\.lt_[su]\b`) defends against a future codegen flip
        # to unsigned-comparison or any other compare-then-trap
        # variant; the previous `not in body` substring check would
        # have silently passed if the guard mechanism changed.
        assert not re.search(r"\bi64\.lt_[su]\b", body), (
            f"Unexpected `i64.lt_[su]` in int_sub body — Int subtraction "
            f"should not have an underflow guard. Body:\n{body}"
        )
        assert "unreachable" not in body, (
            f"Unexpected `unreachable` in int_sub body — Int subtraction "
            f"should not emit a trap. Body:\n{body}"
        )

    def test_pure_literal_subtract_emits_no_guard(self) -> None:
        """`0 - 1` (pure-literal idiom) emits no guard — Path-A scope.

        The codegen guard fires only when at least one operand has
        @Nat *provenance* (slot ref or @Nat-returning function),
        matching the verifier's _has_nat_origin filter.  This keeps
        the corpus's `Err(_) -> 0 - 1` and `throw(0 - 1)` idioms
        unaffected — they consume the result at @Int positions where
        the upcast is well-defined.
        """
        # ensures(true) avoids confounding `i64.lt_s` from the
        # postcondition-check codegen (which compiles `< 0` to
        # `i64.lt_s; i32.eqz; if; ...; call $vera.contract_fail`).
        # We're isolating whether the underflow guard fires, not the
        # postcondition check.
        src = """
public fn neg_sentinel(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  0 - 1
}

public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  neg_sentinel()
}
"""
        result = _compile_ok(src)
        wat = result.wat
        sentinel_idx = wat.find("(func $neg_sentinel")
        assert sentinel_idx >= 0
        body_end = wat.find("\n  (func ", sentinel_idx + 1)
        if body_end < 0:
            body_end = len(wat)
        body = wat[sentinel_idx:body_end]
        # Bare i64.sub, no guard — even though both operands are
        # non-negative IntLits and thus statically @Nat per checker.
        # The provenance filter excludes pure-literal subtractions.
        # As with test_int_subtract_emits_no_guard, banning both
        # `i64.lt_s` / `i64.lt_u` and any `unreachable` defends
        # against future codegen variants that switch comparator or
        # trap mechanism.
        assert "i64.sub" in body
        assert not re.search(r"\bi64\.lt_[su]\b", body), (
            f"Pure-literal `0 - 1` should not get a guard at Path-A "
            f"scope. Body:\n{body}"
        )
        assert "unreachable" not in body, (
            f"Pure-literal `0 - 1` should not emit a trap guard at "
            f"Path-A scope. Body:\n{body}"
        )

    def test_recursion_with_path_guard_runs_clean(self) -> None:
        """`if @Nat.0 == 0 then 0 else f(@Nat.0 - 1)` runs at deep depth.

        The verifier discharges the underflow obligation from the
        path condition (the else-branch implies @Nat.0 != 0, hence
        @Nat.0 >= 1).  The codegen still emits the runtime guard
        (no Tier-1 skip-channel currently), but `lhs >= rhs` always
        holds at runtime so the branch is never taken — confirming
        the guard doesn't fire spuriously on path-discharged sites.
        """
        src = """
private fn countdown(@Nat -> @Nat)
  requires(true)
  ensures(true)
  decreases(@Nat.0)
  effects(pure)
{
  if @Nat.0 == 0 then {
    0
  } else {
    countdown(@Nat.0 - 1)
  }
}

public fn main(@Unit -> @Nat)
  requires(true) ensures(true) effects(pure)
{
  countdown(100)
}
"""
        # countdown(100) → 99 → ... → 0; guard never fires.
        assert _run(src) == 0

        # Structural assertion: the guard IS emitted on the
        # path-discharged @Nat.0 - 1 site.  Pure behavioural assertion
        # (countdown(100) == 0) would pass even if the guard were
        # accidentally elided, because the path condition keeps
        # @Nat.0 >= 1 in the recursive arm so underflow can never
        # fire — making the test silently coverage-blind.  Pinning
        # the WAT shape catches a future regression where the codegen
        # detector skips path-discharged sites (that's a Tier-1
        # skip-channel optimisation; until it lands, every @Nat-Nat
        # site with provenance gets the guard regardless of static
        # discharge status).
        result = _compile_ok(src)
        wat = result.wat
        countdown_idx = wat.find("(func $countdown")
        assert countdown_idx >= 0, "countdown not found in WAT"
        body_end = wat.find("\n  (func ", countdown_idx + 1)
        if body_end < 0:
            body_end = len(wat)
        body = wat[countdown_idx:body_end]
        assert "i64.lt_s" in body and "unreachable" in body, (
            f"Expected the @Nat.0 - 1 underflow guard "
            f"(i64.lt_s + unreachable) inside countdown body, got: "
            f"{body!r}"
        )

    def test_modulecall_provenance_emits_guard_and_traps(self) -> None:
        """ModuleCall with @Nat return type carries provenance.

        `vera.math::abs(...)` returns `@Nat` per spec/09 §9.x, so
        `vera.math::abs(a) - vera.math::abs(b)` is a `@Nat - @Nat`
        site where both operands have @Nat provenance via
        ast.ModuleCall (not ast.FnCall).  The CodeRabbit review on
        PR #554 (round 1) identified that the original codegen
        helpers `_is_static_nat_typed` and `_has_nat_origin_codegen`
        only handled ast.FnCall — module-qualified callees with
        @Nat return types would have slipped past the guard.

        This test exercises the fix by:
          (1) confirming the guard is emitted in the WAT for the
              ModuleCall case, and
          (2) confirming the guard actually fires at runtime when
              the subtraction would underflow (`abs(0) - abs(5)`
              produces -5 without the guard, traps with it).
        """
        unsafe_src = """
import vera.math(abs);

private fn unsafe_modcall(@Int, @Int -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  vera.math::abs(@Int.1) - vera.math::abs(@Int.0)
}

public fn main(@Unit -> @Nat)
  requires(true) ensures(true) effects(pure)
{
  -- @Int.1 is the first param (older / De Bruijn = 1), @Int.0 is the
  -- second / most-recent.  Body computes `abs(@Int.1) - abs(@Int.0)`,
  -- so `unsafe_modcall(0, 5)` evaluates as `abs(0) - abs(5) = 0 - 5`
  -- → underflow.
  unsafe_modcall(0, 5)
}
"""
        # Structural assertion: guard emitted in unsafe_modcall body.
        result = _compile_ok(unsafe_src)
        wat = result.wat
        fn_idx = wat.find("(func $unsafe_modcall")
        assert fn_idx >= 0, "unsafe_modcall not found in WAT"
        body_end = wat.find("\n  (func ", fn_idx + 1)
        if body_end < 0:
            body_end = len(wat)
        body = wat[fn_idx:body_end]
        assert "i64.lt_s" in body and "unreachable" in body, (
            f"Expected the underflow guard for ModuleCall-provenance "
            f"@Nat - @Nat inside unsafe_modcall body, got: {body!r}"
        )

        # Behavioural assertion: unsafe_modcall(0, 5) produces
        # abs(@Int.1) - abs(@Int.0) = abs(0) - abs(5) = 0 - 5 = underflow → trap.
        # @Int.1 is the first parameter (older / De Bruijn = 1) and @Int.0 the
        # second (most-recent), so call order is preserved in the body via
        # the swapped subscripts.
        with pytest.raises((wasmtime.WasmtimeError, wasmtime.Trap, RuntimeError)):
            execute(result, fn_name="main", args=[])

        # Safe case: passing args where lhs >= rhs runs cleanly.
        safe_src = """
import vera.math(abs);

private fn safe_modcall(@Int, @Int -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  vera.math::abs(@Int.1) - vera.math::abs(@Int.0)
}

public fn main(@Unit -> @Nat)
  requires(true) ensures(true) effects(pure)
{
  -- safe_modcall(5, 3): @Int.1=5, @Int.0=3 → abs(5) - abs(3) = 2.
  safe_modcall(5, 3)
}
"""
        # safe_modcall(5, 3): abs(@Int.1) - abs(@Int.0) = abs(5) - abs(3) = 2.
        assert _run(safe_src) == 2

    def test_rhs_only_provenance_emits_guard_and_traps(self) -> None:
        """`0 - @Nat.0` carries provenance via the RHS slot only.

        The codegen detector requires `_has_nat_origin_codegen(left)
        OR _has_nat_origin_codegen(right)` — symmetric in both
        operands.  Existing positive tests pin the left-has-provenance
        case (`@Nat.1 - @Nat.0`, `@Nat.0 - 1`) and the both-provenance
        ModuleCall case, but not the right-only-provenance case.
        Without that coverage a future refactor that accidentally
        ignored `expr.right` (or changed `or` to `and`) would still
        pass every existing test while silently re-opening the
        underflow hole on the right-only shape.

        Body: `0 - @Nat.0` (a non-negative IntLit on the left, a
        @Nat slot on the right).  Both operands are statically @Nat
        per the checker, but only the slot has @Nat provenance —
        the literal is exempt at Path-A scope.  The guard must
        still fire because the right operand provides provenance.
        """
        src = """
private fn lit_minus_slot(@Nat -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  0 - @Nat.0
}

public fn main(@Unit -> @Nat)
  requires(true) ensures(true) effects(pure)
{
  -- @Nat.0 = 1 → `0 - 1` underflows.
  lit_minus_slot(1)
}
"""
        # Structural assertion: guard emitted in lit_minus_slot body
        # despite the LHS being a literal.
        result = _compile_ok(src)
        wat = result.wat
        fn_idx = wat.find("(func $lit_minus_slot")
        assert fn_idx >= 0, "lit_minus_slot not found in WAT"
        body_end = wat.find("\n  (func ", fn_idx + 1)
        if body_end < 0:
            body_end = len(wat)
        body = wat[fn_idx:body_end]
        assert "i64.lt_s" in body and "unreachable" in body, (
            f"Expected the underflow guard for rhs-only-provenance "
            f"`0 - @Nat.0` inside lit_minus_slot body, got:\n{body}"
        )

        # Behavioural assertion: lit_minus_slot(1) → 0 - 1 → trap.
        with pytest.raises((wasmtime.WasmtimeError, wasmtime.Trap, RuntimeError)):
            execute(result, fn_name="main", args=[])

        # Safe case: lit_minus_slot(0) → 0 - 0 = 0 (no underflow).
        safe_src = """
private fn lit_minus_slot(@Nat -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  0 - @Nat.0
}

public fn main(@Unit -> @Nat)
  requires(true) ensures(true) effects(pure)
{
  lit_minus_slot(0)
}
"""
        assert _run(safe_src) == 0


# =====================================================================
# @Nat binding-site narrowing runtime guard (#552)
# =====================================================================

class TestNatBindingRuntimeGuard552:
    """Codegen emits a runtime `value >= 0` guard at `let @Nat = <Int>`
    narrowing sites (#552), the binding-site generalisation of the #520
    subtraction guard.

    The verifier emits a Tier-1 `value >= 0` obligation; codegen mirrors
    the detection (_narrows_into_nat, sharing _is_static_nat_typed +
    _has_nat_origin_codegen) and traps if a negative value would reach a
    @Nat slot.  Like the #520 guard, it protects programs compiled
    without `vera verify`.

    #552 guarded the canonical `let` site; #747 extends the runtime guard
    to the tuple-destructure, top-level match-bind, ADT sub-pattern,
    concrete constructor-field, and call-argument sites (see
    `TestNatBindingRuntimeGuard747`).  The effect-op-argument site and a
    dedicated trap kind remain a follow-up.
    """

    _GUARDED_LET = """
private fn narrow(@Int -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Nat = @Int.0;
  @Nat.0
}

public fn main(@Unit -> @Nat)
  requires(true) ensures(true) effects(pure)
{
  narrow(0 - 1)
}
"""

    _SAFE_LET = """
private fn narrow(@Int -> @Nat)
  requires(@Int.0 >= 0)
  ensures(true)
  effects(pure)
{
  let @Nat = @Int.0;
  @Nat.0
}

public fn main(@Unit -> @Nat)
  requires(true) ensures(true) effects(pure)
{
  narrow(7)
}
"""

    def test_negative_narrowing_traps_at_runtime(self) -> None:
        """narrow(0 - 1) feeds -1 into `let @Nat`, tripping the guard.

        Without the guard, `local.set` would store -1 silently in a
        @Nat slot.  With it, the function traps before the bad value
        propagates.
        """
        result = _compile_ok(self._GUARDED_LET)
        with pytest.raises(
            (wasmtime.WasmtimeError, wasmtime.Trap, RuntimeError)
        ):
            execute(result, fn_name="main", args=[])

    def test_nonnegative_narrowing_returns_value(self) -> None:
        """narrow(7) passes the guard and returns 7 — no spurious trap."""
        assert _run(self._SAFE_LET) == 7

    def test_guard_emitted_in_wat_for_let_narrowing(self) -> None:
        """The `narrow` body contains the `i64.lt_s` + `unreachable` guard."""
        result = _compile_ok(self._GUARDED_LET)
        wat = result.wat
        idx = wat.find("(func $narrow")
        assert idx >= 0, "narrow function not found in WAT"
        body_end = wat.find("\n  (func ", idx + 1)
        if body_end < 0:
            body_end = len(wat)
        body = wat[idx:body_end]
        assert "i64.lt_s" in body, (
            f"Expected `i64.lt_s` in narrow body for the @Nat guard. "
            f"Body:\n{body}"
        )
        assert "unreachable" in body, (
            f"Expected `unreachable` in narrow body for the @Nat guard. "
            f"Body:\n{body}"
        )

    def test_guard_emitted_for_untranslatable_let_narrowing(self) -> None:
        """The let-site guard fires even when the narrowed value is
        untranslatable to Z3 (a Tier-3 narrowing — the case the guard
        primarily exists for).  Codegen keys on static @Nat-typing, not
        Z3-translatability, so `let @Nat = array_length(...)` is guarded
        like any other @Int->@Nat let (#748 review)."""
        src = """
private fn narrow_len(@Array<Int> -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Nat = array_length(@Array<Int>.0);
  @Nat.0
}

public fn main(@Unit -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  narrow_len([1, 2, 3])
}
"""
        result = _compile_ok(src)
        wat = result.wat
        idx = wat.find("(func $narrow_len")
        assert idx >= 0, "narrow_len function not found in WAT"
        body_end = wat.find("\n  (func ", idx + 1)
        if body_end < 0:
            body_end = len(wat)
        body = wat[idx:body_end]
        assert "i64.lt_s" in body, (
            f"Expected `i64.lt_s` @Nat guard for an untranslatable let "
            f"narrowing. Body:\n{body}"
        )
        assert "unreachable" in body

    def test_already_nat_let_emits_no_guard(self) -> None:
        """`let @Nat = @Nat.0` is not a narrowing — no guard emitted.

        Sister to the structural test above: the guard fires only when
        the bound value is not already statically @Nat (or is a
        pure-literal subtraction), so a @Nat -> @Nat let must emit no
        `i64.lt_[su]`.
        """
        src = """
private fn passthru(@Nat -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Nat = @Nat.0;
  @Nat.0
}

public fn main(@Unit -> @Nat)
  requires(true) ensures(true) effects(pure)
{
  passthru(5)
}
"""
        result = _compile_ok(src)
        wat = result.wat
        idx = wat.find("(func $passthru")
        assert idx >= 0
        body_end = wat.find("\n  (func ", idx + 1)
        if body_end < 0:
            body_end = len(wat)
        body = wat[idx:body_end]
        assert not re.search(r"\bi64\.lt_[su]\b", body), (
            f"`let @Nat = @Nat.0` is not a narrowing and must not get a "
            f"guard. Body:\n{body}"
        )

    def test_wrapped_subtraction_traps_at_runtime(self) -> None:
        """`let @Nat = { 0 - 1 }` — a pure-literal underflow wrapped in a
        block — now gets the guard and traps, matching the verifier.  The
        top-level-only check missed this; the guard descends to the
        value-producing leaf (#552 review)."""
        src = """
public fn main(@Unit -> @Nat)
  requires(true) ensures(true) effects(pure)
{
  let @Nat = { 0 - 1 };
  @Nat.0
}
"""
        result = _compile_ok(src)
        with pytest.raises(
            (wasmtime.WasmtimeError, wasmtime.Trap, RuntimeError)
        ):
            execute(result, fn_name="main", args=[])


class TestNatBindingRuntimeGuard747:
    """#747: the runtime `value >= 0` guard now fires at the @Nat binding
    sites beyond `let` — tuple destructure, top-level match bind, ADT
    sub-pattern bind, concrete constructor field, and call argument.  Each
    emits the `i64.lt_s; if; unreachable` net so an unverified compile traps
    on a negative @Nat rather than silently storing it; a non-narrowing
    target (an @Int field/formal) emits none.
    """

    @staticmethod
    def _body(wat: str, fn: str) -> str:
        """Slice out function ``fn``'s WAT body.

        The guard-presence tests assert ``i64.lt_s`` appears in this slice;
        that uniquely identifies the @Nat guard *only because* their
        fixtures contain no other `i64.lt_s` emitter (comparison, string /
        array / math builtins all emit one).  Keep these fixtures to plain
        arithmetic / ctor / match bodies — the negative-traps tests below
        pin the guard's runtime *semantics* independently.
        """
        # Boundary-safe so `$gcall` does not match `$gcall_helper` — a plain
        # substring `find` would slice the wrong body (CR #756).
        m = re.search(rf"\(func \${re.escape(fn)}(?![A-Za-z0-9_$.])", wat)
        assert m is not None, f"{fn} not found in WAT"
        idx = m.start()
        end = wat.find("\n  (func ", idx + 1)
        return wat[idx:end if end >= 0 else len(wat)]

    def _assert_guarded(self, wat: str, fn: str) -> None:
        """Assert ``fn``'s body emits the full @Nat guard shape — both the
        `i64.lt_s` comparison and the `unreachable` trap edge — so a
        regression emitting the compare without the trap is caught (CR #756).
        The fixtures are plain arithmetic / ctor / match bodies, so neither
        token appears except in the guard."""
        body = self._body(wat, fn)
        assert "i64.lt_s" in body, f"{fn}: missing i64.lt_s guard compare"
        assert "unreachable" in body, f"{fn}: missing unreachable trap edge"

    def test_param_destructure_nat_components_guarded(self) -> None:
        """`let Tuple<@Nat, @Nat> = @Tuple<Int, Int>.0` guards each
        narrowed component."""
        result = _compile_ok("""
public fn gdestr(@Tuple<Int, Int> -> @Nat)
  requires(true) ensures(true) effects(pure)
{ let Tuple<@Nat, @Nat> = @Tuple<Int, Int>.0; @Nat.0 }
""")
        self._assert_guarded(result.wat, "gdestr")

    def test_subpattern_nat_bind_guarded(self) -> None:
        """`match opt { Some(@Nat) -> }` on `Option<Int>` guards the
        projected @Int payload bound as @Nat."""
        result = _compile_ok("""
public fn gsub(@Option<Int> -> @Int)
  requires(true) ensures(true) effects(pure)
{ match @Option<Int>.0 { Some(@Nat) -> @Nat.0, None -> 0 } }
""")
        self._assert_guarded(result.wat, "gsub")

    def test_toplevel_match_nat_bind_guarded(self) -> None:
        """`match <Int> { @Nat -> }` guards the scrutinee bound as @Nat."""
        result = _compile_ok("""
public fn gmatch(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ match @Int.0 { @Nat -> @Nat.0 } }
""")
        self._assert_guarded(result.wat, "gmatch")

    def test_concrete_nat_ctor_field_guarded(self) -> None:
        """A concrete @Nat constructor field guards its @Int argument."""
        result = _compile_ok("""
public data NatBox { WrapN(Nat) }
public fn gctor(@Int -> @NatBox)
  requires(true) ensures(true) effects(pure)
{ WrapN(@Int.0) }
""")
        self._assert_guarded(result.wat, "gctor")

    def test_concrete_nat_call_arg_guarded(self) -> None:
        """A concrete @Nat call formal guards its @Int argument."""
        result = _compile_ok("""
public fn takesNat(@Nat -> @Nat)
  requires(true) ensures(true) effects(pure)
{ @Nat.0 }
public fn gcall(@Int -> @Nat)
  requires(true) ensures(true) effects(pure)
{ takesNat(@Int.0) }
""")
        self._assert_guarded(result.wat, "gcall")

    def test_nat_alias_let_bind_guarded(self) -> None:
        """A `type Age = Nat` alias target is guarded at the let-bind site —
        `_resolve_base_type_name` resolves the alias so the runtime guard is
        not skipped by the bare `type_name == "Nat"` check (CR #756)."""
        result = _compile_ok("""
type Age = Nat;
public fn galias(@Int -> @Age)
  requires(true) ensures(true) effects(pure)
{ let @Age = @Int.0; @Age.0 }
""")
        self._assert_guarded(result.wat, "galias")

    def test_generic_nat_alias_ctor_field_guarded(self) -> None:
        """A generic alias instantiated to @Nat (`type Id<T> = T` used as
        `Id<Nat>`) resolves to Nat via type-argument substitution, so the
        constructor-field narrowing is still guarded (CR #756)."""
        result = _compile_ok("""
type Id<T> = T;
public data GBox { GWrap(Id<Nat>) }
public fn ggen(@Int -> @GBox)
  requires(true) ensures(true) effects(pure)
{ GWrap(@Int.0) }
""")
        self._assert_guarded(result.wat, "ggen")

    def test_generic_instantiated_call_arg_guarded(self) -> None:
        """A generic function formal fixed to @Nat at the call site is guarded
        on the *monomorphised* callee.  The guard keys on the resolved call
        target (`pick$Nat`, concrete @Nat flags), not the generic `pick`
        (erased flags) — so `pick<Nat>(@Nat.0, @Int.0)` traps a negative
        narrowing just like a concrete @Nat call (CR #756)."""
        result = _compile_ok("""
private forall<T>
fn pick(@T, @T -> @T)
  requires(true) ensures(true) effects(pure)
{ @T.0 }
public fn gcall(@Nat, @Int -> @Nat)
  requires(@Int.0 >= 0) ensures(true) effects(pure)
{ pick(@Nat.0, @Int.0) }
""")
        self._assert_guarded(result.wat, "gcall")

    def test_builtin_mdheading_nat_field_guarded(self) -> None:
        """The built-in `MdHeading` constructor's concrete @Nat level field is
        guarded.  Manual built-in layouts bypass `_compute_constructor_layout`
        (the only other `nat_fields` populator), so the flag must be set on the
        layout explicitly; MdHeading is the sole built-in ctor with a @Nat
        field (CR #756)."""
        result = _compile_ok("""
public fn mkheading(@Int -> @MdBlock)
  requires(true) ensures(true) effects(pure)
{ MdHeading(@Int.0, [MdText("x")]) }
""")
        self._assert_guarded(result.wat, "mkheading")

    def test_int_ctor_field_emits_no_guard(self) -> None:
        """A concrete @Int constructor field is not a narrowing target —
        no guard, mirroring the @Int-field/@Int-formal exemption."""
        result = _compile_ok("""
public data IntBox { WrapI(Int) }
public fn gint(@Int -> @IntBox)
  requires(true) ensures(true) effects(pure)
{ WrapI(@Int.0) }
""")
        assert not re.search(
            r"\bi64\.lt_[su]\b", self._body(result.wat, "gint"))

    def test_call_arg_negative_traps_at_runtime(self) -> None:
        """An unverified compile passing -5 into a @Nat formal traps at
        runtime — the guard's safety-net role beyond the `let` site."""
        result = _compile_ok("""
public fn takesNat(@Nat -> @Nat)
  requires(true) ensures(true) effects(pure)
{ @Nat.0 }
public fn main(@Unit -> @Nat)
  requires(true) ensures(true) effects(pure)
{ takesNat(0 - 5) }
""")
        with pytest.raises(
            (wasmtime.WasmtimeError, wasmtime.Trap, RuntimeError)
        ):
            execute(result, fn_name="main", args=[])

    def test_destructure_negative_traps_at_runtime(self) -> None:
        """A tuple-destructure binding a negative component into a @Nat slot
        traps at runtime — proves the destructure guard's *semantics*, not
        just its emission (the offset/accessor load logic is the most
        regression-prone of the five sites)."""
        result = _compile_ok("""
public fn main(@Unit -> @Nat)
  requires(true) ensures(true) effects(pure)
{ let Tuple<@Nat, @Nat> = Tuple(0 - 5, 1); @Nat.0 }
""")
        with pytest.raises(
            (wasmtime.WasmtimeError, wasmtime.Trap, RuntimeError)
        ):
            execute(result, fn_name="main", args=[])

    def test_subpattern_negative_traps_at_runtime(self) -> None:
        """An ADT sub-pattern binding a negative payload as @Nat traps at
        runtime — the sub-pattern guard's semantics."""
        result = _compile_ok("""
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ match Some(0 - 5) { Some(@Nat) -> @Nat.0, None -> 0 } }
""")
        with pytest.raises(
            (wasmtime.WasmtimeError, wasmtime.Trap, RuntimeError)
        ):
            execute(result, fn_name="main", args=[])

    def test_toplevel_match_negative_traps_at_runtime(self) -> None:
        """A top-level `match <Int> { @Nat -> }` binding a negative scrutinee
        as @Nat traps at runtime — pins the match-bind guard's semantics, not
        only its WAT emission (CR #756)."""
        result = _compile_ok("""
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ match 0 - 5 { @Nat -> @Nat.0 } }
""")
        with pytest.raises(
            (wasmtime.WasmtimeError, wasmtime.Trap, RuntimeError)
        ):
            execute(result, fn_name="main", args=[])

    @staticmethod
    def _boxes_module() -> object:
        """A resolved `boxes` module declaring `data NatBox { WrapN(Nat) }`
        for the cross-module imported-constructor guard tests (#747 site 4)."""
        from pathlib import Path

        from vera.parser import parse_to_ast
        from vera.resolver import ResolvedModule

        src = "public data NatBox {\n  WrapN(Nat)\n}\n"
        return ResolvedModule(
            path=("boxes",), file_path=Path("/fake/boxes.vera"),
            program=parse_to_ast(src), source=src)

    def test_imported_concrete_nat_ctor_field_guarded(self) -> None:
        """An imported concrete-@Nat constructor field emits the runtime
        guard (#747 site 4) — the cross-module codegen path the local-ctor
        tests don't exercise."""
        from vera.parser import parse_to_ast

        src = """import boxes(WrapN, NatBox);
public fn gimp(@Int -> @NatBox)
  requires(true) ensures(true) effects(pure)
{ WrapN(@Int.0) }
"""
        result = compile(
            parse_to_ast(src), source=src,
            resolved_modules=[self._boxes_module()])
        assert not [d for d in result.diagnostics if d.severity == "error"]
        self._assert_guarded(result.wat, "gimp")

    def test_imported_ctor_negative_traps_at_runtime(self) -> None:
        """The imported concrete-@Nat ctor guard traps on a negative arg —
        the cross-module runtime safety net."""
        from vera.parser import parse_to_ast

        src = """import boxes(WrapN, NatBox);
public fn main(@Unit -> @NatBox)
  requires(true) ensures(true) effects(pure)
{ WrapN(0 - 5) }
"""
        result = compile(
            parse_to_ast(src), source=src,
            resolved_modules=[self._boxes_module()])
        assert not [d for d in result.diagnostics if d.severity == "error"]
        with pytest.raises(
            (wasmtime.WasmtimeError, wasmtime.Trap, RuntimeError)
        ):
            execute(result, fn_name="main", args=[])

    @staticmethod
    def _nat_fn_module() -> object:
        """A resolved `natfns` module with a function taking a concrete @Nat
        formal, for the cross-module imported-function guard test (CR #756 —
        `_register_modules` must harvest the module's `_fn_nat_params`)."""
        from pathlib import Path

        from vera.parser import parse_to_ast
        from vera.resolver import ResolvedModule

        src = ("public fn boxNat(@Nat -> @Nat)\n"
               "  requires(true) ensures(true) effects(pure)\n"
               "{ @Nat.0 }\n")
        return ResolvedModule(
            path=("natfns",), file_path=Path("/fake/natfns.vera"),
            program=parse_to_ast(src), source=src)

    def test_imported_fn_nat_param_guarded(self) -> None:
        """A cross-module call into an imported function's concrete @Nat formal
        emits the runtime guard.  `_register_modules` must harvest the imported
        module's `_fn_nat_params`, or the guard metadata is lost and the
        narrowing stored unchecked (CR #756)."""
        from vera.parser import parse_to_ast

        src = """import natfns(boxNat);
public fn gimpfn(@Int -> @Nat)
  requires(true) ensures(true) effects(pure)
{ boxNat(@Int.0) }
"""
        result = compile(
            parse_to_ast(src), source=src,
            resolved_modules=[self._nat_fn_module()])
        assert not [d for d in result.diagnostics if d.severity == "error"]
        self._assert_guarded(result.wat, "gimpfn")

    def test_imported_fn_negative_traps_at_runtime(self) -> None:
        """The imported-function @Nat guard traps on a negative argument at
        run time, not only in the WAT — proves the harvested `_fn_nat_params`
        is enforced end-to-end across the module boundary (CR #756)."""
        from vera.parser import parse_to_ast

        src = """import natfns(boxNat);
public fn gimpfn(@Int -> @Nat)
  requires(true) ensures(true) effects(pure)
{ boxNat(@Int.0) }
"""
        result = compile(
            parse_to_ast(src), source=src,
            resolved_modules=[self._nat_fn_module()])
        assert not [d for d in result.diagnostics if d.severity == "error"]
        with pytest.raises(
            (wasmtime.WasmtimeError, wasmtime.Trap, RuntimeError)
        ):
            execute(result, fn_name="gimpfn", args=[-1])

    @pytest.mark.parametrize("body", [
        'string_repeat("ab", 0 - 5)',
        'string_from_char_code(0 - 5)',
        'string_pad_start("ab", 0 - 5, "x")',
        'string_pad_end("ab", 0 - 5, "x")',
    ])
    def test_builtin_nat_param_negative_traps_at_runtime(self, body) -> None:
        """A negative @Int narrowed into a builtin's @Nat parameter traps at
        runtime (#757 fold-in).  Builtin translators bypass `_fn_nat_params`,
        so each guards its @Nat arg directly; an unverified compile of a
        negative argument traps rather than overallocating or passing a
        negative to a host import (CR #756)."""
        result = _compile_ok(f"""
public fn main(@Unit -> @String)
  requires(true) ensures(true) effects(pure)
{{ {body} }}
""")
        with pytest.raises(
            (wasmtime.WasmtimeError, wasmtime.Trap, RuntimeError)
        ):
            execute(result, fn_name="main", args=[])

    def test_builtin_nat_param_valid_does_not_trap(self) -> None:
        """A non-negative builtin @Nat argument runs without trapping — the
        guard fires only on a genuine narrowing of a negative value (#757)."""
        result = _compile_ok("""
public fn main(@Unit -> @String)
  requires(true) ensures(true) effects(pure)
{ string_repeat("ab", 3) }
""")
        execute(result, fn_name="main", args=[])

    def test_builtin_md_has_heading_negative_level_traps_at_runtime(self) -> None:
        """`md_has_heading` is the markup builtin in the guarded set — its @Nat
        `level` parameter is covered by the same `_narrows_into_nat` guard as the
        string builtins, but its `@MdBlock`/`@Bool` signature keeps it out of the
        `@String`-returning parametrized trap test above.  A negative @Int
        narrowed into `level` traps rather than passing a negative to the host
        import (review of #756; round-14 #757 fold-in)."""
        result = _compile_ok("""
effect IO { op print(String -> Unit); }
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Result<MdBlock, String> = md_parse("# Title");
  match @Result<MdBlock, String>.0 {
    Ok(@MdBlock) -> {
      let @Bool = md_has_heading(@MdBlock.0, 0 - 5);
      if @Bool.0 then { IO.print("yes") } else { IO.print("no") }
    },
    Err(_) -> IO.print("err")
  }
}
""")
        with pytest.raises(
            (wasmtime.WasmtimeError, wasmtime.Trap, RuntimeError)
        ):
            execute(result, fn_name="main", args=[])

    def test_generic_ctor_field_negative_does_not_trap_today(self) -> None:
        """The generic-instantiated constructor field is the one #747 narrowing
        site with NO runtime guard: constructor layouts carry no per-field @Nat
        mono metadata, so a generic field instantiated to @Nat erases to i64
        (#757).  `Some(0 - 5)` building an `Option<Nat>` therefore compiles and
        runs *without* trapping today — it stores -5 silently.  This pins the
        deferral so it can't regress to a *silent* loss of the obligation: when
        #757 lands and emits the guard, this test flips to a trap and becomes the
        regression anchor, symmetric with the #754 effect-op pin
        (`test_non_let_tier3_narrowing_warns_unguarded`).  The verifier still
        obligates the narrowing statically (E503), so a verified program is
        unaffected — this is purely the codegen runtime backstop (review of
        #756, #760)."""
        result = _compile_ok("""
public fn f(@Unit -> @Option<Nat>)
  requires(true) ensures(true) effects(pure)
{ Some(0 - 5) }
""")
        # No pytest.raises: the deferred-guard state means this MUST NOT trap.
        # If #757 adds the guard, replace this with a pytest.raises(...) block.
        execute(result, fn_name="f", args=[])


# =====================================================================
# WASM call translator critical bug fixes (#475 PR 1)
# =====================================================================

class TestExpressionBodiedExnHandler475:
    """`#475` finding 1: handle[Exn<E>] with expression-bodied catch arms.

    Pre-fix, `_translate_handle_exn` only inferred `result_wt` when
    the catch-clause body was an `ast.Block`; expression-bodied
    handlers (e.g. `throw(@String) -> None`) left `result_wt = None`
    and the emitted WAT omitted the `(result T)` annotation —
    producing invalid WAT that would fail validation when the body
    type was anything other than Unit.

    Post-fix, `_infer_expr_wasm_type` is used for both the catch
    clause and the body, handling all expression types uniformly.
    """

    def test_expression_bodied_handler_returns_option(self) -> None:
        """`throw(@String) -> None` (expression-bodied, returns Option)."""
        src = """
private fn try_div(@Int, @Int -> @Option<Int>)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[Exn<String>] {
    throw(@String) -> None
  } in {
    Some(safe_div(@Int.0, @Int.1))
  }
}

private fn safe_div(@Int, @Int -> @Int)
  requires(true)
  ensures(true)
  effects(<Exn<String>>)
{
  if @Int.1 == 0 then {
    throw("divide by zero")
  } else {
    @Int.0 / @Int.1
  }
}

public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  match try_div(10, 2) {
    Some(@Int) -> @Int.0,
    None -> -1
  }
}
"""
        # Should compile cleanly and run; pre-#475 the missing
        # `(result ...)` annotation made the WAT invalid.
        assert _run(src) == 5

    def test_expression_bodied_handler_traps_on_zero(self) -> None:
        """Same shape as above but exercises the throw path returning None."""
        src = """
private fn try_div(@Int, @Int -> @Option<Int>)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[Exn<String>] {
    throw(@String) -> None
  } in {
    Some(safe_div(@Int.0, @Int.1))
  }
}

private fn safe_div(@Int, @Int -> @Int)
  requires(true)
  ensures(true)
  effects(<Exn<String>>)
{
  if @Int.1 == 0 then {
    throw("divide by zero")
  } else {
    @Int.0 / @Int.1
  }
}

public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  match try_div(10, 0) {
    Some(@Int) -> @Int.0,
    None -> -1
  }
}
"""
        # try_div(10, 0) → throws → handler returns None → match → -1.
        assert _run(src) == -1

    def test_expression_bodied_handler_int_result(self) -> None:
        """Catch arm returns @Int (not Option) — verifies non-pair WAT result."""
        src = """
private fn safe_div(@Int, @Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[Exn<String>] {
    throw(@String) -> 0 - 1
  } in {
    inner_div(@Int.0, @Int.1)
  }
}

private fn inner_div(@Int, @Int -> @Int)
  requires(true)
  ensures(true)
  effects(<Exn<String>>)
{
  if @Int.1 == 0 then {
    throw("divide by zero")
  } else {
    @Int.0 / @Int.1
  }
}

public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  safe_div(10, 0)
}
"""
        assert _run(src) == -1


class TestStringSliceClampBefore475:
    """`#475` finding 2: `string_slice` clamps in i64 before wrapping to i32.

    Pre-fix, `string_slice` had no clamping at all (the placeholder
    `_ = len_s  # reserved for future bounds checking` documented
    the gap).  Indices were narrowed via `i32.wrap_i64` first; large
    positive i64 values silently turned into negative i32 values,
    which then drove the byte-copy loop into out-of-range memory
    or produced garbled output.

    Post-fix, the clamp happens in i64 space (via the new
    `_clamp_i64_to_range_then_wrap` helper) before narrowing — so a
    huge positive index clamps to `len_s` cleanly and a negative
    index clamps to 0, producing a well-defined empty or short
    slice.
    """

    def test_normal_slice(self) -> None:
        """Baseline: `string_slice("hello world", 0, 5)` → 'hello'."""
        src = """
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print(string_slice("hello world", 0, 5))
}
"""
        assert _run_io(src).strip() == "hello"

    def test_negative_start_clamps_to_zero(self) -> None:
        """Negative start clamps to 0 (in i64) — produces 'hel'.

        Pre-fix this either crashed the byte-copy loop on a wrapped
        negative i32 offset, or silently produced garbled output.
        """
        src = """
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print(string_slice("hello", -1, 3))
}
"""
        assert _run_io(src).strip() == "hel"

    def test_end_beyond_length_clamps_to_length(self) -> None:
        """End past length clamps to length — full remaining suffix."""
        src = """
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print(string_slice("hello", 2, 100))
}
"""
        assert _run_io(src).strip() == "llo"

    def test_swapped_indices_produce_empty(self) -> None:
        """end < start → empty slice (end clamped up to start)."""
        src = """
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print(string_slice("hello", 3, 1))
}
"""
        # start=3, end=1 → end clamped up to start=3 → empty.
        assert _run_io(src).strip() == ""

    def test_huge_positive_start_clamps_in_i64(self) -> None:
        """Pre-fix bug: i64 value > i32.MAX wraps to negative i32 then misbehaves.

        Post-fix: clamps in i64 space to `len_s` (i64) before
        narrowing.  Index 4294967301 (= 2^32 + 5) would wrap to
        i32 = 5 pre-fix, falsely succeeding with an unintended
        offset.  Post-fix it clamps to len_s (5) and produces the
        empty slice correctly.
        """
        src = """
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print(string_slice("hello", 4294967301, 4294967310))
}
"""
        # Both indices clamp to len_s (5); end clamped up to start;
        # new_len = 0; empty string.
        assert _run_io(src).strip() == ""


class TestCharCodeBoundsCheck475:
    """`#475` finding 3: `string_char_code` traps on out-of-range index.

    Pre-fix, `_translate_char_code` had no bounds check at all —
    the index was wrapped from i64 to i32 and used as a byte offset
    to `i32.load8_u` directly.  Out-of-range indices read arbitrary
    WASM linear memory, a real memory-safety hole.

    Post-fix, the bounds check operates in i64 space (`idx < 0 ||
    idx >= len_s_i64`) and traps with `unreachable` before
    narrowing — so huge positive i64 values cannot wrap to small
    in-range-looking i32 values and bypass the check.
    """

    def test_in_range_returns_byte(self) -> None:
        """Baseline: `string_char_code("hello", 1)` → 'e' = 101."""
        src = """
public fn main(@Unit -> @Nat)
  requires(true) ensures(true) effects(pure)
{
  string_char_code("hello", 1)
}
"""
        assert _run(src) == 101

    def test_negative_index_traps(self) -> None:
        """Negative index → trap (was: read at ptr - 1 silently)."""
        src = """
public fn main(@Unit -> @Nat)
  requires(true) ensures(true) effects(pure)
{
  string_char_code("hello", -1)
}
"""
        with pytest.raises((wasmtime.WasmtimeError, wasmtime.Trap, RuntimeError)):
            execute(_compile_ok(src), fn_name="main", args=[])

    def test_index_at_length_traps(self) -> None:
        """Index == length → trap (out-of-range; valid range is [0, len))."""
        src = """
public fn main(@Unit -> @Nat)
  requires(true) ensures(true) effects(pure)
{
  string_char_code("hello", 5)
}
"""
        with pytest.raises((wasmtime.WasmtimeError, wasmtime.Trap, RuntimeError)):
            execute(_compile_ok(src), fn_name="main", args=[])

    def test_huge_positive_index_traps(self) -> None:
        """Huge i64 index → trap (was: wraps to small i32 and reads OOB).

        4294967301 (= 2^32 + 5) wraps to i32 = 5 pre-fix.  For
        "hello" (len 5) that would have read at offset 5 — past
        the string, into adjacent memory.  Post-fix: bounds check
        operates in i64 *before* narrowing, so 4294967301 >>
        len_s_i64 (5) traps cleanly.
        """
        src = """
public fn main(@Unit -> @Nat)
  requires(true) ensures(true) effects(pure)
{
  string_char_code("hello", 4294967301)
}
"""
        with pytest.raises((wasmtime.WasmtimeError, wasmtime.Trap, RuntimeError)):
            execute(_compile_ok(src), fn_name="main", args=[])

    def test_last_valid_index(self) -> None:
        """Boundary: index == length - 1 returns the last byte cleanly."""
        src = """
public fn main(@Unit -> @Nat)
  requires(true) ensures(true) effects(pure)
{
  string_char_code("hello", 4)
}
"""
        # 'o' = 111
        assert _run(src) == 111


# =====================================================================
# WASM call translator major bug fixes (#475 PR 2)
# =====================================================================


class TestArraySliceClamp475:
    """`#475` finding 4: `array_slice` clamps in i64 before wrapping.

    Pre-fix, `array_slice` narrowed start/end indices via
    `i32.wrap_i64` first, then compared with `arr_len` as i32.  A
    huge positive i64 value (e.g. 2^32 + 5) wraps to a small i32
    that looks in-range and the byte-copy reads past the array.

    Post-fix, the translator widens `arr_len` to i64 and uses the
    cross-mixin `_clamp_i64_to_range_then_wrap` helper (shared with
    `string_slice`) to clamp before narrowing.
    """

    def test_normal_slice(self) -> None:
        """Baseline: `array_slice([1,2,3,4,5], 1, 4)` length 3."""
        src = """
public fn main(@Unit -> @Nat)
  requires(true) ensures(true) effects(pure)
{
  array_length(array_slice([1, 2, 3, 4, 5], 1, 4))
}
"""
        assert _run(src) == 3

    def test_negative_start_clamps_to_zero(self) -> None:
        """Negative start clamps to 0 (in i64) — slice has length 3."""
        src = """
public fn main(@Unit -> @Nat)
  requires(true) ensures(true) effects(pure)
{
  array_length(array_slice([1, 2, 3, 4, 5], -1, 3))
}
"""
        assert _run(src) == 3

    def test_end_beyond_length_clamps(self) -> None:
        """End past length clamps to length — full remaining suffix."""
        src = """
public fn main(@Unit -> @Nat)
  requires(true) ensures(true) effects(pure)
{
  array_length(array_slice([1, 2, 3, 4, 5], 2, 100))
}
"""
        assert _run(src) == 3

    def test_huge_positive_start_clamps_in_i64(self) -> None:
        """Pre-fix bug: i64 > i32.MAX wraps to small i32 and reads OOB.

        Post-fix: clamps in i64 space to `arr_len_i64` before
        narrowing.  4294967301 (2^32 + 5) wraps to i32 = 5 pre-fix
        and would have copied past the array; post-fix it clamps
        to arr_len cleanly.
        """
        src = """
public fn main(@Unit -> @Nat)
  requires(true) ensures(true) effects(pure)
{
  array_length(array_slice([1, 2, 3, 4, 5], 4294967301, 4294967310))
}
"""
        assert _run(src) == 0


class TestMapArrayValueRejected475:
    """`#475` finding 5: `Map<K, Array<T>>` is rejected at codegen.

    Pre-fix, `_map_wasm_tag` returned a placeholder string for any
    unknown type, so `Map<K, Array<T>>` would compile but silently
    treat the array values as opaque pointers — operations like
    `Map<K, Array<T>>.get` returned the raw pointer i32, not a
    properly-tagged Array, leading to type-system holes downstream.

    Post-fix, `_map_wasm_tag` returns `None` for unsupported value
    types (including `Array`); 11 call sites guard against this and
    return None to surface the unsupported feature as a codegen
    error rather than a silent miscompilation.
    """

    def test_compile_skips_function_for_map_of_array(self) -> None:
        """`Map<Nat, Array<Nat>>` insert: function body skipped at codegen.

        Pre-fix the value type fell through to `_map_wasm_tag` ⇒ ``"b"``
        (single i32) and the host import was emitted with one slot
        where two were needed; the resulting binary mis-tagged Array
        values silently.

        Post-fix `_translate_map_insert` returns `None` (because
        `_map_wasm_tag("Array<Nat>")` is `None`); the WASM backend's
        per-function "unsupported expressions" guard catches the None
        and emits an E602 warning, skipping `main` from the export
        table.  The well-formed program (parses, type-checks) gets a
        controlled rejection rather than a silently mis-tagged binary.
        """
        src = """
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Map<Nat, Array<Nat>> = map_insert(map_new(), 1, [1, 2, 3]);
  IO.print("ok")
}
"""
        # Type-check + compile both succeed (no error diagnostics);
        # but `main` is skipped from exports and an E602 "unsupported
        # expressions" warning is emitted.
        result = _compile_ok(src)
        assert "main" not in result.exports, (
            f"main should be skipped (Map<Nat, Array<Nat>> unsupported); "
            f"exports were: {result.exports}"
        )
        warnings = [d for d in result.diagnostics if d.severity == "warning"]
        assert any("unsupported" in d.description.lower() for d in warnings), (
            f"Expected an 'unsupported' warning; warnings: {warnings}"
        )


class TestGenericMonoSuffixFromSlotRef604:
    """`#604` / `#655` — generic prelude combinator mono clones now
    produce the correct type-arg suffix when the closure argument is
    a ``SlotRef`` typed as an FnType alias (e.g. ``@Doubler.0``).

    Pre-fix `_unify_param_arg` in `vera/codegen/monomorphize.py` had
    an AnonFn-specific alias-resolution path; `SlotRef` args typed as
    FnType aliases skipped that path and left the closure's return
    type variable unbound.  The unbound type var fell to the
    ``"Bool"`` phantom-var fallback at result-building time, producing
    mono suffixes like ``option_map$Int_Bool`` instead of
    ``option_map$Int_Int`` and trapping at runtime with ``indirect
    call type mismatch``.

    Post-fix (this commit): both AnonFn literals AND SlotRef-typed-as-
    FnType-alias args flow through the shared ``_resolve_arg_fn_shape``
    helper, binding the closure's return type uniformly.

    Two tests below pin the contract:

    1. ``option_map(opt, fn_alias_slot)`` produces ``option_map$Int_Int``
       and runs correctly (not a runtime trap).
    2. The template-only ``[E602]``/``[E604]`` warnings on the prelude
       generics are suppressed in programs that successfully call them
       — audit recommendation 2 from #604.
    """

    _SLOT_FN_SRC = """
type Doubler = fn(Int -> Int) effects(pure);

private fn use_map(@Option<Int>, @Doubler -> @Option<Int>)
  requires(true) ensures(true) effects(pure)
{
  option_map(@Option<Int>.0, @Doubler.0)
}

public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  option_unwrap_or(use_map(Some(10), fn(@Int -> @Int) effects(pure) { @Int.0 * 2 }), 0)
}
"""

    def test_mono_suffix_correct_for_slotref_fn_alias_arg(self) -> None:
        """`option_map(opt, @Doubler.0)` where ``Doubler = fn(Int -> Int)``
        produces a mono clone with suffix ``$Int_Int`` (not ``$Int_Bool``)
        and runs without trapping.

        Pre-fix this produced ``option_map$Int_Bool`` and trapped at
        runtime with ``wasm trap: indirect call type mismatch`` because
        the closure's i64 return mismatched the i32 (Bool) the wrongly-
        suffixed mono clone expected.

        CR-2 on PR #659 — the WAT-only assertions pinned suffix
        correctness but didn't catch the actual user-visible failure
        mode (the runtime trap).  Add a runtime execution assertion
        so a regression in indirect-call signature wiring fails the
        test rather than silently slipping through with the right
        suffix in WAT but wrong execution.
        """
        result = _compile_ok(self._SLOT_FN_SRC)
        # The compiled module should contain the correctly-suffixed
        # mono clone, not the wrongly-suffixed one.  Use
        # boundary-safe regex (CR-10 on PR #659) so longer variants
        # like `$option_map$Int_Int_X` don't slip past as substrings
        # of the expected token.
        wat = result.wat or ""
        assert re.search(r"\$option_map\$Int_Int(?![A-Za-z0-9_])", wat), (
            f"Expected correctly-suffixed mono clone "
            f"`$option_map$Int_Int` in WAT; got WAT containing "
            f"option_map suffixes: "
            f"{[line for line in wat.splitlines() if 'option_map$' in line]}"
        )
        assert not re.search(r"\$option_map\$Int_Bool(?![A-Za-z0-9_])", wat), (
            "Wrong-suffix mono clone `$option_map$Int_Bool` "
            "should not appear post-#604 fix; found in WAT"
        )
        # F8 on PR #659 review — independently pin the WASM-side
        # call-site rewriter (`vera/wasm/calls.py::_resolve_arg_fn_shape_wasm`
        # + `_infer_fn_alias_type_args_wasm`).  The function
        # definition `(func $option_map$Int_Int ...)` is emitted by
        # the monomorphizer at Pass 1.5; the `call` instruction is
        # emitted later by the WASM call-site rewriter, which has
        # an independent SlotRef-FnType-alias resolution path.  A
        # regression where Pass 1.5 produces the right clone but
        # the rewriter mangles the call to a different name would
        # pass the function-definition assertion above but fail at
        # WASM validation with `unknown function $option_map$<wrong>`.
        # Assert both names match by counting `call $option_map$Int_Int`
        # (or `return_call $option_map$Int_Int`) occurrences.
        call_pattern = (
            r"(?:^|\s)(?:return_)?call\s+\$option_map\$Int_Int"
            r"(?![A-Za-z0-9_])"
        )
        assert re.search(call_pattern, wat, re.MULTILINE), (
            f"Expected a `call $option_map$Int_Int` (or "
            f"`return_call`) instruction in WAT — without it the "
            f"call-site rewriter's mangled name doesn't match the "
            f"mono clone's definition.  Got option_map references: "
            f"{[line.strip() for line in wat.splitlines() if 'option_map' in line]}"
        )
        # Runtime pin: execute and confirm no trap.  `Some(10) * 2 = 20`.
        # Pre-fix this would have trapped with
        # `wasm trap: indirect call type mismatch`.
        exec_result = execute(result, fn_name="main")
        assert exec_result.value == 20, (
            f"Expected main() to return 20 (Some(10) * 2 unwrapped); "
            f"got {exec_result.value!r}.  A non-20 result OR a trap "
            f"signals indirect-call signature regression."
        )

    def test_parameterised_alias_substitutes_type_args(self) -> None:
        """`option_map(opt, @Mapper<Int>.0)` where
        ``type Mapper<T> = fn(T -> T)`` substitutes ``T → Int`` in
        the alias body before unifying against the generic call's
        ``OptionMapFn<A, B>`` param.

        CR-4 / CR-5 on PR #659: without substitution, the
        ``_resolve_arg_fn_shape`` helper returned the raw alias body
        ``fn(T -> T)`` and the downstream
        ``_infer_fn_alias_type_args`` matcher bound alias-local names
        (``A → T``, ``B → T``) instead of concrete ones.  The mono
        suffix would have been ``option_map$T_T`` rather than
        ``option_map$Int_Int`` — wrong shape, wouldn't match the
        clone Pass 1.5 registered, runtime trap.
        """
        src = """
type Mapper<T> = fn(T -> T) effects(pure);

private fn use_map(@Option<Int>, @Mapper<Int> -> @Option<Int>)
  requires(true) ensures(true) effects(pure)
{
  option_map(@Option<Int>.0, @Mapper<Int>.0)
}

public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  option_unwrap_or(use_map(Some(7), fn(@Int -> @Int) effects(pure) { @Int.0 * 3 }), 0)
}
"""
        result = _compile_ok(src)
        wat = result.wat or ""
        # Boundary-safe regex (CR-10 on PR #659) — see sibling test.
        assert re.search(r"\$option_map\$Int_Int(?![A-Za-z0-9_])", wat), (
            f"Expected `$option_map$Int_Int` from parameterised "
            f"alias `Mapper<Int>`; got option_map suffixes: "
            f"{[line for line in wat.splitlines() if 'option_map$' in line]}"
        )
        # Negative pin (CR-9 on PR #659): the unsubstituted alias-
        # local-name clone must not be emitted alongside the correct
        # one.  A bug that produced both (e.g. partial substitution
        # leaking the raw alias body into a second registration) would
        # otherwise slip past the positive assertion.
        assert not re.search(r"\$option_map\$T_T(?![A-Za-z0-9_])", wat), (
            "Unsubstituted parameterised-alias clone "
            "`$option_map$T_T` should not appear after the "
            "`T → Int` substitution fix; found in WAT"
        )
        # Runtime pin — `Some(7) * 3 = 21`.
        exec_result = execute(result, fn_name="main")
        assert exec_result.value == 21

    def test_template_warning_suppressed_when_mono_clone_compiles(
        self,
    ) -> None:
        """Audit recommendation 2 from #604: template-only `[E602]` /
        `[E604]` warnings on a generic decl are suppressed when at
        least one mono clone of that decl successfully compiles.

        Pre-fix every program that imported the prelude saw 5 spurious
        warnings about ``option_unwrap_or`` / ``option_map`` / etc.
        even when those functions worked end-to-end via mono.  The
        warnings were misleading (they suggested a problem when there
        was none) and drowned out genuine `[E602]` skips in the
        Layer 1 e602 gate (#656).

        Post-fix the post-compile suppression pass in
        ``vera/codegen/core.py::compile_program`` drops the spurious
        warnings.  Programs that never call a given generic still see
        the warning (preserving the "this generic can't compile and
        you're never using a mono clone" signal).
        """
        result = _compile_ok(self._SLOT_FN_SRC)
        warnings = [d for d in result.diagnostics if d.severity == "warning"]
        # The two generics actually called in `main` — `option_map`
        # and `option_unwrap_or` — must not appear in template-only
        # warning diagnostics.
        for fn_name in ("option_map", "option_unwrap_or"):
            offending = [
                d for d in warnings
                if d.error_code in {"E602", "E604", "E605"}
                and d.description.startswith(f"Function '{fn_name}' ")
            ]
            assert not offending, (
                f"Template-only warning for '{fn_name}' should be "
                f"suppressed (mono clones compiled); got: "
                f"{[d.description for d in offending]}"
            )

    def test_template_warning_NOT_suppressed_when_generic_never_called(
        self,
    ) -> None:
        """Negative control for the suppression pass.

        A user-defined generic ``forall<T>`` decl with a bare ``@T``
        parameter that is **never called** still emits its template
        warning.  Pre-fix this would have emitted `[E604]` ("function
        has unsupported parameter type") for every prelude generic on
        every compile; post-fix the suppression pass only fires when
        at least one mono clone of the generic actually compiled
        (`compiled_mono_bases` in
        `vera/codegen/core.py::compile_program`).  An over-broad
        suppressor that dropped *all* template warnings would pass
        the sibling test above but fail this one.

        CR-7 on PR #659.
        """
        src = """
private forall<T> fn unused_generic(@T -> @T)
  requires(true) ensures(true) effects(pure)
{
  @T.0
}

public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  42
}
"""
        result = _compile_ok(src)
        warnings = [d for d in result.diagnostics if d.severity == "warning"]
        offending = [
            d for d in warnings
            if d.error_code in {"E602", "E604", "E605"}
            and d.description.startswith("Function 'unused_generic' ")
        ]
        assert offending, (
            f"Expected `unused_generic` template warning to fire (no "
            f"mono clone exists since the generic is never called); "
            f"got warnings: "
            f"{[d.description for d in warnings]}"
        )


class TestHeadOverRefinement655ShapeB:
    """`#655` Shape B — array indexing through a refinement-of-Array
    alias now compiles and runs cleanly.

    Pre-fix: `type NonEmptyArray = { @Array<Int> | predicate }` plus
    a function `head(@NonEmptyArray -> @Int) { @NonEmptyArray.0[0] }`
    parsed and type-checked OK, but codegen's
    `_infer_index_element_type` returned None — the
    `_alias_array_element` helper in `vera/wasm/inference.py` only
    followed `isinstance(target, ast.NamedType)` chains, so
    `RefinementType.base_type` was never unwrapped.  The `head`
    function got dropped via [E602] ("body contains unsupported
    expressions"), and any call site referenced a non-existent
    `$head` → `unknown func: $head` at WASM validation.

    Post-fix (v0.0.146): the alias-target lookup peels any
    `RefinementType` layers before checking whether the base is a
    `NamedType` pointing at `Array<T>`.  Refinement-of-Array
    aliases now resolve their element type the same as a bare
    `Array<T>`.

    This test pins both the compile contract (no [E602] for `head`,
    function gets exported) and the runtime contract
    (`head([1, 2, 3])` returns 1).
    """

    _HEAD_SRC = """
type NonEmptyArray = { @Array<Int> | array_length(@Array<Int>.0) > 0 };

private fn head(@NonEmptyArray -> @Int)
  requires(true) ensures(true) effects(pure)
{
  @NonEmptyArray.0[0]
}

public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  head([1, 2, 3])
}
"""

    def test_head_over_refinement_compiles_and_runs(self) -> None:
        """`head([1, 2, 3])` returns 1 — the function compiles and the
        call resolves to a real `$head` clone in WASM."""
        result = _compile_ok(self._HEAD_SRC)
        # `$head` must appear as a defined function in the WAT (not
        # dropped via [E602]).
        wat = result.wat or ""
        assert re.search(r"\(func \$head\b", wat), (
            f"Expected `(func $head ...)` definition in WAT after "
            f"#655 Shape B fix.  Pre-fix `head` was dropped via "
            f"[E602] and the call site referenced an absent "
            f"`$head`.  WAT excerpt: "
            f"{[line.strip() for line in wat.splitlines() if 'head' in line.lower()][:5]}"
        )
        # Runtime pin — `head([1, 2, 3]) == 1`.
        exec_result = execute(result, fn_name="main")
        assert exec_result.value == 1, (
            f"Expected head([1, 2, 3]) == 1; got {exec_result.value!r}"
        )

    def test_head_emits_no_e602_for_refinement_alias(self) -> None:
        """Compiling the head/NonEmptyArray fixture emits no
        `[E602]` warning for `head` — the function isn't dropped.

        Pre-fix the diagnostic stream contained
        `Function 'head' body contains unsupported expressions —
        skipped.` for every compile of this shape.  Post-fix that
        warning is absent.
        """
        result = _compile_ok(self._HEAD_SRC)
        warnings = [d for d in result.diagnostics if d.severity == "warning"]
        head_e602 = [
            d for d in warnings
            if d.error_code == "E602"
            and d.description.startswith("Function 'head' ")
        ]
        assert not head_e602, (
            f"Expected no [E602] for `head`; got: "
            f"{[d.description for d in head_e602]}"
        )


class TestE602NodeLevelReasons626Layer3:
    """`#626` Layer 3 (PR #658) — `[E602]` diagnostics now carry a
    node-level span and a specific reason string, rather than the
    pre-Layer-3 generic enclosing-function-level message.

    Pre-Layer-3 the diagnostic looked like::

        [E602] Function 'main' body contains unsupported expressions
        — skipped.   ← span: declaration of `main` (line N)

    Post-Layer-3::

        [E602] Function 'main' body contains unsupported FnCall:
        Map/Set with Array-typed key, value, or element is not
        supported — function skipped.   ← span: the offending
        map_insert(...) call (line N+M)

    These two tests pin the user-visible contract:

    1. the diagnostic's ``description`` includes the specific reason
       text that the ``raise CodegenSkip(node, reason)`` site passed
       — preventing a future refactor from dropping back to a generic
       message.
    2. the diagnostic's ``location.line`` matches the offending node
       (the FnCall), not the enclosing function declaration — preventing
       a future refactor from dropping the per-node span.

    See `vera/codegen/functions.py::_compile_fn` for the catch handler
    that turns ``CodegenSkip(node, reason)`` into the user-visible
    ``[E602]`` shape.
    """

    _MAP_OF_ARRAY_SRC = """
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Map<Nat, Array<Nat>> = map_insert(map_new(), 1, [1, 2, 3]);
  IO.print("ok")
}
"""

    def test_e602_description_contains_node_specific_reason(self) -> None:
        """The `[E602]` description for `Map<Nat, Array<Nat>>` carries
        the specific reason text from the `_translate_map_insert`
        raise site, not just the generic ``"unsupported expressions"``.

        Locks in the user-visible improvement from PR #658:
        ``CodegenSkip(call, "Map/Set with Array-typed key, value, or
        element is not supported")`` flows through the catch handler
        as ``f"Function '{decl.name}' body contains unsupported
        {type(skip.node).__name__}: {skip.reason}"``.
        """
        result = _compile(self._MAP_OF_ARRAY_SRC)
        e602 = [
            d for d in result.diagnostics
            if d.error_code == "E602" and "main" in d.description
        ]
        assert e602, (
            f"Expected an [E602] for `main`; diagnostics: "
            f"{result.diagnostics}"
        )
        # The reason string from `vera/wasm/calls_containers.py`'s
        # CodegenSkip raise should appear verbatim in the diagnostic.
        assert "Array-typed" in e602[0].description, (
            f"Expected node-specific reason in [E602] description; "
            f"got: {e602[0].description!r}"
        )
        # And the AST-node-type label too — confirms the catch handler
        # is composing from `type(skip.node).__name__`.
        assert "FnCall" in e602[0].description, (
            f"Expected FnCall node-type label in [E602] description; "
            f"got: {e602[0].description!r}"
        )

    def test_e602_location_points_at_offending_call_not_fn_header(
        self,
    ) -> None:
        """The `[E602]` source location points at the offending
        `map_insert(...)` call (line 5 of the test source), not the
        `public fn main(...)` declaration (line 2).

        Pre-Layer-3 the legacy `_warning(decl, ...)` call attached
        the function-declaration span; Post-Layer-3 the catch handler
        passes `skip.node` (the FnCall), giving a per-node span.
        """
        result = _compile(self._MAP_OF_ARRAY_SRC)
        e602 = [
            d for d in result.diagnostics
            if d.error_code == "E602" and "main" in d.description
        ]
        assert e602, (
            f"Expected an [E602] for `main`; got: {result.diagnostics}"
        )
        # `public fn main(@Unit -> @Unit)` is line 2 in _MAP_OF_ARRAY_SRC;
        # the offending `map_insert(...)` is line 5, column 31.  The
        # diagnostic must point exactly at the call, not the declaration
        # (line 2) or any later statement.  Pin the line precisely so
        # any future refactor that drops back to enclosing-function
        # span (line 2) OR drifts to the `IO.print` on line 6 fails
        # the test.
        loc_line = e602[0].location.line
        assert loc_line == 5, (
            f"Expected [E602] location at line 5 (the "
            f"`map_insert(...)` call); got line {loc_line}.  "
            f"Pre-#658 this would have been line 2 (legacy "
            f"enclosing-fn span).  Any other line means the catch "
            f"handler drifted off the offending FnCall node."
        )


class TestUrlParseJoinRoundTrip475:
    """`#475` finding 6: `url_parse` / `url_join` round-trip preserves shape.

    Pre-fix, `url_parse` discarded the `has_auth`, `has_query`, and
    `has_frag` delimiter bits; `url_join` then reconstructed using
    `len > 0` heuristics, which:

    - Conflated `http:path` (no authority) with `http://path` (empty
      authority) — both joined as `http:///path`.
    - Lost trailing `?` and `#` when the body was empty.

    Post-fix, `url_parse` packs the three flag bits into a previously
    unused i32 word at struct offset 44; `url_join` reads them back
    and emits the delimiters faithfully.
    """

    def test_scheme_only_no_authority(self) -> None:
        """`http:path` round-trips without gaining `//`."""
        src = """
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  match url_parse("http:path") {
    Ok(@UrlParts) -> IO.print(url_join(@UrlParts.0)),
    Err(@String) -> IO.print("ERR")
  }
}
"""
        assert _run_io(src).strip() == "http:path"

    def test_full_url_with_authority(self) -> None:
        """`http://example.com/p` round-trips faithfully."""
        src = """
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  match url_parse("http://example.com/p") {
    Ok(@UrlParts) -> IO.print(url_join(@UrlParts.0)),
    Err(@String) -> IO.print("ERR")
  }
}
"""
        assert _run_io(src).strip() == "http://example.com/p"

    def test_url_with_query(self) -> None:
        """Query body with `=` round-trips."""
        src = """
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  match url_parse("https://x/p?q=1") {
    Ok(@UrlParts) -> IO.print(url_join(@UrlParts.0)),
    Err(@String) -> IO.print("ERR")
  }
}
"""
        assert _run_io(src).strip() == "https://x/p?q=1"

    def test_empty_query_delimiter_preserved(self) -> None:
        """`http://x?` (trailing `?` with empty body) round-trips.

        Pre-fix the trailing `?` was dropped because url_join
        gated query emit on `q_len > 0`.
        """
        src = """
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  match url_parse("http://x?") {
    Ok(@UrlParts) -> IO.print(url_join(@UrlParts.0)),
    Err(@String) -> IO.print("ERR")
  }
}
"""
        assert _run_io(src).strip() == "http://x?"

    def test_empty_fragment_delimiter_preserved(self) -> None:
        """`http://x#` (trailing `#` with empty body) round-trips."""
        src = """
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  match url_parse("http://x#") {
    Ok(@UrlParts) -> IO.print(url_join(@UrlParts.0)),
    Err(@String) -> IO.print("ERR")
  }
}
"""
        assert _run_io(src).strip() == "http://x#"


class TestBase64DecodePadding475:
    """`#475` finding 7: `base64_decode` rejects `=` outside padding region.

    RFC 4648 only allows `=` in the final 1–2 positions of the
    encoded string (and only when total length % 4 ∈ {2, 3}).  Pre-fix
    the decoder accepted `=` anywhere — `AB=C` decoded as if it were
    `AB==` followed by `C`, silently producing a corrupted output.

    Post-fix, the decoder verifies that any `=` byte sits at index
    >= `slen - pad` and rejects otherwise, surfacing a controlled
    error rather than miscompiling input.
    """

    def test_valid_padding_decodes(self) -> None:
        """Baseline: `Zm9v` (no padding) decodes to `foo`."""
        src = """
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  match base64_decode("Zm9v") {
    Ok(@String) -> IO.print(@String.0),
    Err(@String) -> IO.print("ERR")
  }
}
"""
        assert _run_io(src).strip() == "foo"

    def test_valid_one_pad_decodes(self) -> None:
        """`Zm8=` decodes to `fo` — one `=` at the end."""
        src = """
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  match base64_decode("Zm8=") {
    Ok(@String) -> IO.print(@String.0),
    Err(@String) -> IO.print("ERR")
  }
}
"""
        assert _run_io(src).strip() == "fo"

    def test_misplaced_equals_rejected(self) -> None:
        """`AB=C` (= in middle) → Err.

        Pre-fix this decoded silently with the embedded `=`
        treated as zero bits.  Post-fix it returns Err.
        """
        src = """
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  match base64_decode("AB=C") {
    Ok(@String) -> IO.print("OK"),
    Err(@String) -> IO.print("ERR")
  }
}
"""
        assert _run_io(src).strip() == "ERR"


class TestParseEmbeddedSpaces475:
    """`#475` finding 8: `parse_nat` / `parse_int` reject embedded spaces.

    Pre-fix the digit loop in both parsers silently skipped ASCII
    space characters mid-number.  `"1 2"` parsed as 12; `"-1 0"`
    parsed as -10.  Documentation only mentions trimming leading/
    trailing whitespace.

    Post-fix, leading whitespace is still trimmed but embedded
    spaces fall through to the `< '0'` digit-check and produce
    `Err`.
    """

    def test_parse_nat_normal(self) -> None:
        """Baseline: `parse_nat("123")` → Ok(123)."""
        src = """
public fn main(@Unit -> @Nat)
  requires(true) ensures(true) effects(pure)
{
  match parse_nat("123") {
    Ok(@Nat) -> @Nat.0,
    Err(@String) -> 999
  }
}
"""
        assert _run(src) == 123

    def test_parse_nat_leading_space_ok(self) -> None:
        """Leading whitespace still trimmed: `parse_nat("  42")` → Ok(42)."""
        src = """
public fn main(@Unit -> @Nat)
  requires(true) ensures(true) effects(pure)
{
  match parse_nat("  42") {
    Ok(@Nat) -> @Nat.0,
    Err(@String) -> 999
  }
}
"""
        assert _run(src) == 42

    def test_parse_nat_embedded_space_rejected(self) -> None:
        """`parse_nat("1 2")` → Err (was: Ok(12) pre-fix)."""
        src = """
public fn main(@Unit -> @Nat)
  requires(true) ensures(true) effects(pure)
{
  match parse_nat("1 2") {
    Ok(@Nat) -> @Nat.0,
    Err(@String) -> 999
  }
}
"""
        assert _run(src) == 999

    def test_parse_int_embedded_space_rejected(self) -> None:
        """`parse_int("-1 0")` → Err (was: Ok(-10) pre-fix)."""
        src = """
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  match parse_int("-1 0") {
    Ok(@Int) -> @Int.0,
    Err(@String) -> -999
  }
}
"""
        assert _run(src) == -999


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


# =====================================================================
# Pair-type closure capture (#535 — residual of #514)
# =====================================================================


class TestPairCapture535:
    """`#535`: closures capturing `String` / `Array<T>` outer bindings.

    Pre-fix, `vera/wasm/closures.py::_walk_free_vars` resolved the
    capture's wasm type via `_type_name_to_wasm`, which collapses every
    composite type to a single `"i32"`.  `_translate_anon_fn` then
    serialised only the ptr half of the pair into the closure struct;
    `_compile_lifted_closure` read back only the ptr and the body got
    the len from adjacent struct memory (typically zero).  So
    `array_length` / `string_length` of a captured `Array<T>` /
    `String` always returned 0.

    Post-fix all three sites carry an `"i32_pair"` tag for these
    captures: 8 bytes per field (two consecutive i32 stores at
    offset / offset+4); the lifted body allocates two consecutive
    i32 locals (ptr, len) and pushes only the ptr into the slot env,
    matching the let-binding and parameter conventions.
    """

    def test_array_capture_length_in_closure(self) -> None:
        """Reproducer from #535: captured `Array<Int>` length is correct.

        Three iterations × captured length 7 = 21.  Pre-fix the inner
        closure read the captured `@Array<Int>.0` length as 0, so
        `array_fold(...)` summed three zeroes = 0.
        """
        src = """
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Array<Int> = array_range(0, 7);
  let @Array<Int> = array_map(
    array_range(0, 3),
    fn(@Int -> @Int) effects(pure) {
      nat_to_int(array_length(@Array<Int>.0))
    }
  );
  array_fold(@Array<Int>.0, 0, fn(@Int, @Int -> @Int) effects(pure) { @Int.0 + @Int.1 })
}
"""
        assert _run(src) == 21

    def test_string_capture_length_in_closure(self) -> None:
        """Captured `@String.0` length is correct (5 × 3 iterations = 15)."""
        src = """
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @String = "hello";
  let @Array<Int> = array_map(
    array_range(0, 3),
    fn(@Int -> @Int) effects(pure) {
      nat_to_int(string_length(@String.0))
    }
  );
  array_fold(@Array<Int>.0, 0, fn(@Int, @Int -> @Int) effects(pure) { @Int.0 + @Int.1 })
}
"""
        assert _run(src) == 15

    def test_adt_capture_still_works(self) -> None:
        """ADT capture (single i32 ptr) still works — proof the pair fix
        is scoped and doesn't disturb the i32 path."""
        src = """
private data Box<T> { Box(T) }

public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Box<Int> = Box(42);
  let @Array<Int> = array_map(
    array_range(0, 3),
    fn(@Int -> @Int) effects(pure) {
      match @Box<Int>.0 { Box(@Int) -> @Int.0 }
    }
  );
  array_fold(@Array<Int>.0, 0, fn(@Int, @Int -> @Int) effects(pure) { @Int.0 + @Int.1 })
}
"""
        # 42 × 3 = 126
        assert _run(src) == 126

    def test_primitive_capture_still_works(self) -> None:
        """Primitive (Int) capture still works — same scope-pin as ADT."""
        src = """
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Int = 7;
  let @Array<Int> = array_map(
    array_range(0, 3),
    fn(@Int -> @Int) effects(pure) {
      @Int.1
    }
  );
  array_fold(@Array<Int>.0, 0, fn(@Int, @Int -> @Int) effects(pure) { @Int.0 + @Int.1 })
}
"""
        # 7 × 3 = 21
        assert _run(src) == 21

    def test_mixed_pair_and_primitive_capture(self) -> None:
        """Closure captures both an Int (primitive) and an Array (pair).

        Layout exercise: `_translate_anon_fn` must pack the i64 (Int)
        capture at one offset and the i32_pair at another, in the
        order they appear in the free-var walk.
        `_compile_lifted_closure` must mirror that layout on read.
        """
        src = """
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Int = 100;
  let @Array<Int> = array_range(0, 4);
  let @Array<Int> = array_map(
    array_range(0, 3),
    fn(@Int -> @Int) effects(pure) {
      @Int.1 + nat_to_int(array_length(@Array<Int>.0))
    }
  );
  array_fold(@Array<Int>.0, 0, fn(@Int, @Int -> @Int) effects(pure) { @Int.0 + @Int.1 })
}
"""
        # (100 + 4) × 3 = 312
        assert _run(src) == 312

    def test_empty_string_capture_in_closure(self) -> None:
        """Captured empty `String` reads as length 0 (not garbage).

        Edge case for the pair-capture fix: an empty string has
        len = 0, the same value the pre-fix bug *also* produced
        (because it always returned 0).  The post-fix property we
        pin here is that the len is *correctly* preserved as 0
        (rather than reading garbage from an unallocated len slot
        in the closure struct).
        """
        src = """
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @String = "";
  let @Array<Int> = array_map(
    array_range(0, 3),
    fn(@Int -> @Int) effects(pure) {
      nat_to_int(string_length(@String.0))
    }
  );
  array_fold(@Array<Int>.0, 0, fn(@Int, @Int -> @Int) effects(pure) { @Int.0 + @Int.1 })
}
"""
        # 0 × 3 = 0 (empty string captured)
        assert _run(src) == 0

    def test_empty_array_capture_in_closure(self) -> None:
        """Captured empty `Array<Int>` reads as length 0 (not garbage).

        Same edge-case shape as the empty-string test: pins that the
        post-fix path correctly preserves a zero-length pair capture
        (vs. happening to print 0 because the bug always read len as 0).
        """
        src = """
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Array<Int> = array_range(0, 0);
  let @Array<Int> = array_map(
    array_range(0, 3),
    fn(@Int -> @Int) effects(pure) {
      nat_to_int(array_length(@Array<Int>.0))
    }
  );
  array_fold(@Array<Int>.0, 0, fn(@Int, @Int -> @Int) effects(pure) { @Int.0 + @Int.1 })
}
"""
        # 0 × 3 = 0 (empty array captured)
        assert _run(src) == 0

    def test_gc_pressure_pair_capture(self) -> None:
        """Pair capture survives heavy in-closure allocation (GC pressure).

        Exercises the round-1 GC-ordering fix (`gc_capture_pushes`
        runs after `load_instrs`): the closure body allocates several
        large temporary arrays *before* reading the captured array's
        length.  If the capture root were pushed in the prologue
        (pre-fix, before loads), the shadow stack would carry zero —
        and a `$gc_collect` triggered by these in-body allocations
        could mark the captured array unreachable and sweep it,
        leaving the subsequent `array_length(@Array<Int>.0)` reading
        from freed memory.

        Post-fix: the capture root sits on the shadow stack with the
        loaded ptr value (after the env-loads emit), so the captured
        array stays marked through every allocation.

        Three iterations of the outer `array_map`, each allocating
        ~12 KB of temporary arrays inside the body, then reading the
        captured array's length (7) — folded sum is 21.
        """
        src = """
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Array<Int> = array_range(0, 7);
  let @Array<Int> = array_map(
    array_range(0, 3),
    fn(@Int -> @Int) effects(pure) {
      let @Array<Int> = array_range(0, 500);
      let @Array<Int> = array_range(0, 500);
      let @Array<Int> = array_range(0, 500);
      nat_to_int(array_length(@Array<Int>.3))
    }
  );
  array_fold(@Array<Int>.0, 0, fn(@Int, @Int -> @Int) effects(pure) { @Int.0 + @Int.1 })
}
"""
        # @Array<Int>.3 is the outer captured array (skip the three inner
        # let-bindings at indices 0, 1, 2); length 7, three iterations,
        # folded sum 21.
        assert _run(src) == 21

    def test_gc_pressure_string_capture(self) -> None:
        """Same shape as test_gc_pressure_pair_capture but for `String`.

        Captured String must survive heavy in-closure allocation.
        Three iterations × `string_length("hello")` = 5 × 3 = 15.
        """
        src = """
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @String = "hello";
  let @Array<Int> = array_map(
    array_range(0, 3),
    fn(@Int -> @Int) effects(pure) {
      let @Array<Int> = array_range(0, 500);
      let @Array<Int> = array_range(0, 500);
      let @Array<Int> = array_range(0, 500);
      nat_to_int(string_length(@String.0))
    }
  );
  array_fold(@Array<Int>.0, 0, fn(@Int, @Int -> @Int) effects(pure) { @Int.0 + @Int.1 })
}
"""
        # Captured "hello" is length 5; three iterations × 5 = 15
        assert _run(src) == 15


# =====================================================================
# GC infrastructure: $alloc multi-page grow (#487) + worklist (#348)
# =====================================================================


class TestLargeAllocGrow487:
    """`#487`: `$alloc` grows by enough pages, not just 1.

    Pre-fix, when `heap_ptr + total > memory.size * 65536`, `$alloc`
    unconditionally called `memory.grow 1` regardless of how many
    pages were actually needed.  A single allocation request more
    than ~64 KB past the current memory boundary fell through to
    the bump-allocate and trapped on out-of-bounds memory access.

    Post-fix, `$alloc` computes
    `pages_needed = ceil(shortage / 65536)` and grows by that many
    pages in a single call, so allocations of any practical size
    succeed (subject to `memory.grow` returning a valid value).
    """

    def test_50k_int_array_alloc_succeeds(self) -> None:
        """`array_range(0, 50_000)` allocates ~400 KB; pre-fix trapped.

        Two arrays of 50 K i64s (~800 KB total).  The default initial
        memory is 1 page (64 KB); the second `array_range` would
        need to grow by ~7 pages but pre-fix only grew by 1 page
        and then bump-allocated past memory.size, causing a WASM
        OOB-memory-access trap.  Post-fix: the multi-page grow
        provides enough memory and the access at index 49999 reads
        cleanly.
        """
        src = """
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Array<Int> = array_range(0, 50000);
  let @Array<Int> = array_map(@Array<Int>.0, fn(@Int -> @Int) effects(pure) { @Int.0 + 1 });
  @Array<Int>.0[49999]
}
"""
        # array_range(0, 50000) = [0..49999]; mapped to [+1] = [1..50000];
        # index 49999 = 50000.
        assert _run(src) == 50000

    def test_single_large_alloc_smaller_than_old_limit(self) -> None:
        """Smaller allocations (well within 1 page) must keep working.

        Regression pin: the multi-page grow math for the small case
        (shortage ≤ 65535 → pages_needed = 1) reduces to the same
        behaviour as the pre-fix single-page grow.
        """
        src = """
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Array<Int> = array_range(0, 1000);
  @Array<Int>.0[999]
}
"""
        assert _run(src) == 999

    def test_page_boundary_alloc_rounding(self) -> None:
        """Allocations that span the 64 KiB page boundary work cleanly.

        Pins the `pages_needed = (shortage + 65535) >> 16` ceiling
        math against off-by-one regressions at the 64 KiB boundary:

          - shortage = 65535 → 1 page  (just under)
          - shortage = 65536 → 1 page  (exactly fits)
          - shortage = 65537 → 2 pages (1 byte over → must round up)

        Each `array_range(0, N)` allocates `8 * N` payload bytes
        plus a small header.  The exact shortage at runtime depends
        on prior heap state, but the array sizes below straddle the
        single-page allocation boundary (8192 i64s = 65536 bytes ≈
        1 page).  If the rounding math regresses, one of these
        sizes will trap on out-of-bounds memory access at the index
        read.  Each test allocates fresh; we read the last element
        to force the access to actually land in the new memory.
        """
        # 8192 elements = 65536 bytes payload — exactly 1 page
        src_8192 = """
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Array<Int> = array_range(0, 8192);
  @Array<Int>.0[8191]
}
"""
        assert _run(src_8192) == 8191

        # 8193 elements = 65544 bytes payload — 1 page + 8 bytes
        # (shortage just over 64 KiB, must round up to 2 pages)
        src_8193 = """
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Array<Int> = array_range(0, 8193);
  @Array<Int>.0[8192]
}
"""
        assert _run(src_8193) == 8192

        # 16384 elements = 131072 bytes payload — exactly 2 pages
        src_16384 = """
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Array<Int> = array_range(0, 16384);
  @Array<Int>.0[16383]
}
"""
        assert _run(src_16384) == 16383


class TestWorklistOverflow348:
    """`#348`: GC worklist overflow trap (was: silent use-after-free).

    The mark-phase worklist sits between the shadow stack and the
    heap.  Pre-fix: 16 KiB capacity (4 096 entries); when full, the
    push branches in Phase 2 (seed) and Phase 2b (mark scan) silently
    skipped — leaving reachable objects unmarked, which the sweep
    phase then freed as garbage (a real use-after-free hole for
    programs with object graphs holding more than ~4 K pointers
    reachable from a single root).

    Post-fix:
      - Worklist quadrupled to 64 KiB (16 384 entries).  Reasonable
        program shapes don't reach the cap.
      - Both push branches now `unreachable` on overflow rather than
        silently dropping.  Any residual overflow is a clean WASM
        trap, not silent corruption.

    Note: the obvious "wide-graph" runtime test (e.g. an
    `array_map`-built `Array<Box>` of 5 000+ elements) is blocked by
    a separate pre-existing shadow-stack-overflow issue inside
    `array_map`'s per-element allocation pattern, which trips at
    around 4 000 elements regardless of GC worklist size.  The
    wide-graph runtime regression is therefore covered by a
    moderate-size case (which exercises the mark loop without
    tripping the shadow-stack issue) plus structural pins on the
    WAT.
    """

    def test_moderate_graph_with_gc_pressure(self) -> None:
        """ADT graph + heap pressure exercises the post-fix mark loop.

        Builds a 1 000-element `Array<Box>` (well within the
        shadow-stack budget) and forces several `$gc_collect`
        cycles via additional allocations before reading.  The
        Box pointers in the array's payload are pushed onto the
        worklist during the mark phase — exercising the same code
        path that overflowed pre-fix on larger graphs.
        """
        src = """
private data Box { MkBox(Int) }

public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Array<Box> = array_map(
    array_range(0, 1000),
    fn(@Int -> @Box) effects(pure) { MkBox(@Int.0) }
  );
  array_fold(
    @Array<Box>.0,
    0,
    fn(@Int, @Box -> @Int) effects(pure) {
      @Int.0 + match @Box.0 { MkBox(@Int) -> @Int.0 }
    }
  )
}
"""
        # 0+1+...+999 = 499_500
        assert _run(src) == 499_500

    def test_worklist_size_quadrupled_in_wat(self) -> None:
        """Structural pin: the GC region reflects the 64 KiB worklist.

        Pre-fix, `gc_heap_start = stack_base + 16 KiB stack + 16 KiB
        worklist = 32 768`.  Post-fix the worklist is 64 KiB so
        `gc_heap_start = 16 384 + 65 536 = 81 920`.  Pinning the
        constant against the WAT catches accidental size regressions.
        """
        source = """\
private data Box { MkBox(Int) }

public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ match MkBox(42) { MkBox(@Int) -> @Int.0 } }
"""
        result = _compile_ok(source)
        # gc_stack_limit = 16384 (16 KiB shadow stack)
        # gc_heap_start  = 81920 (16 KiB stack + 64 KiB worklist)
        # #692: $gc_stack_limit is now exported so host walkers
        # can check shadow-stack overflow before pushing.
        assert (
            '(global $gc_stack_limit (export "gc_stack_limit") '
            'i32 (i32.const 16384))'
        ) in result.wat
        assert "(global $gc_heap_start i32 (i32.const 81920))" in result.wat

    def test_worklist_overflow_traps_in_wat(self) -> None:
        """Structural pin: both worklist push branches trap on overflow.

        Pre-fix, the seed (Phase 2) and mark-scan (Phase 2b) push
        branches both used `i32.lt_u` followed by a guarded push,
        silently dropping pushes when the worklist was full.
        Post-fix, both use `i32.ge_u` followed by `unreachable` —
        any overflow is a clean trap rather than silent corruption.
        """
        source = """\
private data Box { MkBox(Int) }

public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ match MkBox(42) { MkBox(@Int) -> @Int.0 } }
"""
        result = _compile_ok(source)
        wat = result.wat
        # Extract the $gc_collect function body for inspection.
        gc_start = wat.index("(func $gc_collect")
        gc_end = wat.index("\n  (func ", gc_start + 1) if "\n  (func " in wat[gc_start + 1 :] else len(wat)
        gc_collect = wat[gc_start:gc_end]
        # Match the exact overflow-guard opcode sequence:
        #   local.get $wl_ptr
        #   local.get $wl_end
        #   i32.ge_u
        #   if
        #     unreachable
        # (with arbitrary indentation between lines).  Pre-fix the
        # corresponding sequence used `i32.lt_u` followed by a push,
        # so this regex would match zero times against a regressed
        # file even if `i32.ge_u` continued to appear elsewhere.
        # The two matches correspond to:
        #   - Phase 2 seed: scan_ptr loop, push of root pointers
        #   - Phase 2b mark-scan: per-payload-word push of children
        pattern = re.compile(
            r"local\.get \$wl_ptr\s*"
            r"local\.get \$wl_end\s*"
            r"i32\.ge_u\s*"
            r"if\s*"
            r"unreachable",
            re.MULTILINE,
        )
        matches = pattern.findall(gc_collect)
        assert len(matches) >= 2, (
            f"Expected ≥2 worklist-overflow guard sequences in $gc_collect "
            f"(Phase 2 seed + Phase 2b scan), found {len(matches)}.  "
            f"Pre-fix shape used `i32.lt_u` + push; post-fix uses "
            f"`i32.ge_u` + `unreachable` — a regression here would "
            f"mean one or both push branches reverted to silent-drop."
        )


# =====================================================================
# Opaque-handle GC-rooting hygiene (#347 + #490)
# =====================================================================


class TestOpaqueHandleParamRooting347:
    """`#347`: opaque host handles (Map / Set / Decimal) MUST NOT be
    pushed to the GC shadow stack as roots when they appear as
    function parameters.

    Pre-fix, the gc_pointer_params loop in
    `vera/codegen/functions.py` excluded only `Bool` and `Byte`,
    so a `Map<K, V>` / `Set<T>` / `Decimal` parameter (i32 handle
    index) was treated as a heap pointer and pushed onto the
    shadow stack.  Wasted shadow-stack space and a handle value
    that happened to land in the heap-pointer range with valid
    alignment would have caused the conservative mark phase to
    spuriously mark an unrelated heap object as live (memory
    retention, not corruption).

    Post-fix, the new `_is_host_handle_type` classifier in
    `vera/wasm/helpers.py` is consulted at the rooting decision
    site to exclude these opaque handle types.  We pin the fix
    structurally via WAT inspection: a function taking a
    `Map<K, V>` parameter and needing GC alloc should NOT contain
    the `local.get $p0; i32.store` shadow-push idiom.
    """

    @staticmethod
    def _assert_param0_not_shadow_pushed(
        src: str, fn_name: str, type_label: str,
    ) -> None:
        """Shared helper for the per-handle-type assertion.

        Compiles `src`, finds `$fn_name`, and verifies:

          1. The function's GC prologue WAS emitted (otherwise the
             test is vacuous — a function with no allocator activity
             trivially has no shadow-pushes regardless of whether
             the exclusion fires).
          2. The canonical param-0 shadow-push idiom is NOT present.

        The push regex accepts both numeric (`local.get 0`) and
        named (`local.get $p0`, `local.get $name`) forms — codegen
        currently emits numeric, but future renames shouldn't make
        this test silently pass.

        `type_label` surfaces in failure messages so each call site
        reports which handle type regressed.
        """
        result = _compile_ok(src)
        fn_marker = f"(func ${fn_name}"
        fn_start = result.wat.index(fn_marker)
        if "\n  (func " in result.wat[fn_start + 1:]:
            fn_end = result.wat.index("\n  (func ", fn_start + 1)
        else:
            fn_end = len(result.wat)
        fn_body = result.wat[fn_start:fn_end]

        # Non-vacuity check: confirm the GC prologue WAS emitted for
        # this function.  The prologue's signature is
        # `global.get $gc_sp` followed by a `local.set` (saving the
        # restore point).  Without this, the absence of param-0
        # pushes below is meaningless — there's no shadow-stack
        # activity in the function at all.
        prologue_pattern = re.compile(
            r"global\.get \$gc_sp\s+local\.set\b",
        )
        assert prologue_pattern.search(fn_body), (
            f"${fn_name} has no GC prologue — the test is vacuous "
            f"because no shadow-push activity was emitted.  Adjust "
            f"the test source so the function body forces an "
            f"allocation (e.g. via `option_unwrap_or` or an ADT "
            f"constructor) before the assertion below can pin the "
            f"opaque-handle exclusion."
        )

        # The push idiom we're guarding against — both numeric and
        # named forms of `local.get`.  Numeric is what codegen emits
        # today; named (`$p0`, `$name`) is matched defensively in
        # case codegen is later updated to use param names.
        push_pattern = re.compile(
            r"global\.get \$gc_sp\s+"
            r"local\.get (?:0\b|\$\S+)\s+"
            r"i32\.store",
            re.MULTILINE,
        )
        # Filter to pushes that target param 0 specifically.  Named
        # form `$p0` is the canonical first-param name; numeric `0`
        # also targets the first local.  Other locals (`local.get 1`,
        # `local.get $l2`, etc.) aren't relevant to the param-0
        # exclusion check.
        for match in push_pattern.finditer(fn_body):
            text = match.group(0)
            if "local.get 0" in text or "local.get $p0" in text:
                raise AssertionError(
                    f"Found a shadow_push of param 0 (the "
                    f"{type_label} handle) in ${fn_name} — the "
                    f"opaque-handle exclusion (#347) isn't being "
                    f"applied.  Map / Set / Decimal handles are "
                    f"i32 indices into Python-side stores, not "
                    f"Vera-heap pointers; rooting them wastes "
                    f"shadow-stack space and could cause spurious "
                    f"heap-object retention via the conservative "
                    f"GC's heap-range check.\n\nMatched WAT "
                    f"sequence: {text!r}"
                )

    def test_map_param_shadow_pushed_after_573(self) -> None:
        """A `Map<Nat, Nat>` parameter MUST appear in a
        gc_shadow_push sequence after #573.

        Pre-#573 (v0.0.132): Map values lowered to raw i32 host
        handles, so the #347 classifier excluded them from
        rooting.  Post-#573 (v0.0.134): Map values are pointers
        to GC-managed wrapper ADTs — real Vera-heap pointers
        that the conservative GC must trace, so the exclusion
        is dropped and the canonical shadow-push idiom
        ``global.get $gc_sp; local.get 0; i32.store`` reappears.
        Without rooting, a Map captured across an allocating
        call (e.g. ``map_get`` returning ``Option<V>``) would
        get freed mid-call and the host store entry would be
        decref'd before the surrounding code finishes using it.
        """
        from vera.parser import parse_file
        from vera.transform import transform
        src = """
public fn lookup_or_zero(@Map<Nat, Nat>, @Nat -> @Nat)
  requires(true) ensures(true) effects(pure)
{
  option_unwrap_or(map_get(@Map<Nat, Nat>.0, @Nat.0), 0)
}
"""
        import tempfile
        with tempfile.NamedTemporaryFile(
            mode="w", suffix=".vera", delete=False,
        ) as f:
            f.write(src)
            f.flush()
            path = f.name
        tree = parse_file(path)
        ast_module = transform(tree)
        result = compile(ast_module, source=src, file=path)
        wat = result.wat
        # Find $lookup_or_zero's body.
        fn_match = re.search(
            r"\(func \$lookup_or_zero\b.*?(?=\n  \(func |\n\s*\)\s*$)",
            wat, re.DOTALL,
        )
        assert fn_match is not None, (
            f"Could not find $lookup_or_zero in WAT: {wat[:500]}"
        )
        fn_body = fn_match.group(0)
        # The full ``gc_shadow_push`` idiom is push + advance:
        #   global.get $gc_sp; local.get N; i32.store      (push)
        #   global.get $gc_sp; i32.const 4; i32.add;
        #   global.set $gc_sp                              (advance)
        # Match BOTH halves in order — without the advance, every
        # subsequent push overwrites the same shadow-stack slot,
        # so the test must fail if the advance is missing.
        push_pattern = re.compile(
            r"global\.get \$gc_sp\s+"
            r"local\.get (?:0\b|\$p?0\b)\s+"
            r"i32\.store\s+"
            r"global\.get \$gc_sp\s+"
            r"i32\.const 4\s+"
            r"i32\.add\s+"
            r"global\.set \$gc_sp",
            re.MULTILINE,
        )
        assert push_pattern.search(fn_body) is not None, (
            "#573 regression: Map<Nat, Nat> param 0 was NOT "
            "shadow-pushed (with sp advance) in $lookup_or_zero. "
            "Post-#573, Map values are GC-managed wrapper-ADT "
            "pointers and MUST be rooted across allocating calls; "
            "without the full push+advance idiom the wrapper can "
            "be freed mid-call OR the next push overwrites it.\n\n"
            f"Function body excerpt:\n{fn_body[:800]}"
        )

    def test_set_param_shadow_pushed_after_573(self) -> None:
        """A `Set<Nat>` parameter MUST appear in a
        gc_shadow_push sequence after #573 phase 2.

        Same flip as Map (`test_map_param_shadow_pushed_after_573`):
        post-#573 the Set value lowers to a wrapper-ADT pointer
        (real Vera-heap pointer), so the conservative GC must
        trace it.  Without rooting, a Set captured across an
        allocating call (e.g. `set_contains` returning Bool but
        the surrounding ``option_unwrap_or(Some(...), ...)`` does
        an Option allocation) could be freed mid-call and the
        host-store entry decref'd before subsequent code finishes
        using it.
        """
        from vera.parser import parse_file
        from vera.transform import transform
        src = """
public fn contains_or_false(@Set<Nat>, @Nat -> @Bool)
  requires(true) ensures(true) effects(pure)
{
  if set_contains(@Set<Nat>.0, @Nat.0) then {
    option_unwrap_or(Some(true), false)
  } else {
    option_unwrap_or(Some(false), false)
  }
}
"""
        import tempfile
        with tempfile.NamedTemporaryFile(
            mode="w", suffix=".vera", delete=False,
        ) as f:
            f.write(src)
            f.flush()
            path = f.name
        tree = parse_file(path)
        ast_module = transform(tree)
        result = compile(ast_module, source=src, file=path)
        wat = result.wat
        fn_match = re.search(
            r"\(func \$contains_or_false\b.*?(?=\n  \(func |\n\s*\)\s*$)",
            wat, re.DOTALL,
        )
        assert fn_match is not None
        fn_body = fn_match.group(0)
        # Full push+advance idiom — see Map test for rationale.
        push_pattern = re.compile(
            r"global\.get \$gc_sp\s+"
            r"local\.get (?:0\b|\$p?0\b)\s+"
            r"i32\.store\s+"
            r"global\.get \$gc_sp\s+"
            r"i32\.const 4\s+"
            r"i32\.add\s+"
            r"global\.set \$gc_sp",
            re.MULTILINE,
        )
        assert push_pattern.search(fn_body) is not None, (
            "#573 phase 2 regression: Set<Nat> param 0 was NOT "
            "shadow-pushed (with sp advance) in $contains_or_false. "
            "Post-#573 phase 2, Set values are GC-managed "
            "wrapper-ADT pointers and MUST be rooted with the full "
            "push+advance idiom across allocating calls.\n\n"
            f"Function body excerpt:\n{fn_body[:800]}"
        )

    def test_decimal_param_shadow_pushed_after_573(self) -> None:
        """A `Decimal` parameter MUST appear in a gc_shadow_push
        sequence after #573 phase 3.

        Same flip as Map and Set: Decimal values are now wrapper-
        ADT pointers and need rooting.
        """
        from vera.parser import parse_file
        from vera.transform import transform
        src = """
public fn is_positive_or_false(@Decimal -> @Bool)
  requires(true) ensures(true) effects(pure)
{
  if decimal_eq(@Decimal.0, decimal_from_int(0)) then {
    option_unwrap_or(Some(false), false)
  } else {
    option_unwrap_or(Some(true), false)
  }
}
"""
        import tempfile
        with tempfile.NamedTemporaryFile(
            mode="w", suffix=".vera", delete=False,
        ) as f:
            f.write(src)
            f.flush()
            path = f.name
        tree = parse_file(path)
        ast_module = transform(tree)
        result = compile(ast_module, source=src, file=path)
        wat = result.wat
        fn_match = re.search(
            r"\(func \$is_positive_or_false\b.*?(?=\n  \(func |\n\s*\)\s*$)",
            wat, re.DOTALL,
        )
        assert fn_match is not None
        fn_body = fn_match.group(0)
        # Full push+advance idiom — see Map test for rationale.
        push_pattern = re.compile(
            r"global\.get \$gc_sp\s+"
            r"local\.get (?:0\b|\$p?0\b)\s+"
            r"i32\.store\s+"
            r"global\.get \$gc_sp\s+"
            r"i32\.const 4\s+"
            r"i32\.add\s+"
            r"global\.set \$gc_sp",
            re.MULTILINE,
        )
        assert push_pattern.search(fn_body) is not None, (
            "#573 phase 3 regression: Decimal param 0 was NOT "
            "shadow-pushed (with sp advance) in "
            "$is_positive_or_false.  Post-#573 phase 3, Decimal "
            "values are GC-managed wrapper-ADT pointers and MUST "
            "be rooted with the full push+advance idiom across "
            "allocating calls.\n\n"
            f"Function body excerpt:\n{fn_body[:800]}"
        )


class TestArrayFoldHandleRooting490:
    """`#490` (pre-#573) and `#573 phase 3` (post-): array_fold /
    array_map handle-rooting policy for ``Decimal`` accumulators
    and elements.

    Pre-#490 (v0.0.131): ADT-rooting heuristic over-rooted
    Decimal accumulators / elements as if they were heap pointers,
    even though Decimal lowered to a raw i32 host handle.

    Post-#490 (v0.0.132): the ``_is_host_handle_type`` classifier
    excluded Decimal so the rooting was suppressed (no waste, no
    spurious retention).

    Post-#573 phase 3 (v0.0.134): Decimal MIGRATED to heap-wrap-
    as-ADT.  Decimal values are now wrapper-ADT pointers — real
    Vera-heap pointers — so they MUST be rooted again.  This
    test class flips its assertion to enforce the new policy:
    Decimal accumulators / elements emit MORE shadow-pushes than
    the Int reference (the wrapper allocation rooting + the
    accumulator slot push).  Without rooting, a wrapper could be
    reclaimed mid-fold and the host_decref_handle path would
    evict the live Decimal entry from the host store.
    """

    @staticmethod
    def _count_main_pushes(wat: str) -> int:
        """Count `global.set $gc_sp` idioms inside `$main`'s body.

        Each `gc_shadow_push` emits exactly one `global.set $gc_sp`
        (the sp-advance step at the end of the idiom).  Higher
        count for Decimal vs. Int reference indicates Decimal IS
        being rooted — which post-#573 phase 3 is the correct
        behaviour.
        """
        fn_start = wat.index("(func $main")
        if "\n  (func " in wat[fn_start + 1:]:
            fn_end = wat.index("\n  (func ", fn_start + 1)
        else:
            fn_end = len(wat)
        return wat[fn_start:fn_end].count("global.set $gc_sp")

    def _assert_handle_extra_rooted_after_573(
        self,
        int_src: str,
        decimal_src: str,
        builder_name: str,
        accumulator_label: str,
    ) -> None:
        """Compile `int_src` (Int reference) and `decimal_src`
        (Decimal handle wrapper), then assert the Decimal version
        emits MORE shadow-pushes than the Int version.

        Pre-#573 this asserted the opposite (Decimal must equal
        Int).  Post-#573 phase 3 Decimal is wrapper-rooted, so
        the count rises by at least one (the accumulator's
        wrapper-pointer push) plus any per-iteration alloc roots
        from the wrap operation itself.
        """
        int_wat = _compile_ok(int_src).wat
        decimal_wat = _compile_ok(decimal_src).wat
        int_count = self._count_main_pushes(int_wat)
        decimal_count = self._count_main_pushes(decimal_wat)

        # Non-vacuity: int_count > 0 ensures we're measuring real
        # shadow-stack activity, not a degenerate empty slice.
        assert int_count > 0, (
            f"Int reference for {builder_name} emitted 0 "
            f"`global.set $gc_sp` idioms in $main — the helper "
            f"isn't measuring real shadow-stack activity, so the "
            f"comparison below would pass trivially."
        )

        # Strictly-greater: Decimal MUST add roots.  Pre-#573 this
        # was equality; post-#573 phase 3 the wrapper migration
        # adds wrapper-allocation rooting + accumulator-slot push.
        assert decimal_count > int_count, (
            f"`{builder_name}` with a Decimal {accumulator_label} "
            f"emits {decimal_count} `global.set $gc_sp` idioms in "
            f"$main vs. {int_count} for an Int reference.  Post-"
            f"#573 phase 3 the Decimal version must emit MORE — "
            f"Decimal is now a GC-managed wrapper-ADT pointer, "
            f"not a raw handle, so the wrapper allocation and "
            f"accumulator slot both need rooting.  An equal or "
            f"smaller count means `_is_host_handle_type` is "
            f"still excluding Decimal."
        )

    def test_decimal_accumulator_rooted_after_573(self) -> None:
        """`array_fold` over a `Decimal` accumulator MUST root the
        wrapper pointer (post-#573 phase 3).

        Pre-#573 phase 3 this asserted the opposite — the
        ``u_is_adt`` heuristic excluded Decimal because raw i32
        handles aren't heap pointers.  Post-#573 Decimal IS a
        heap pointer (wrapper ADT) and must be rooted to survive
        per-iteration GC pressure (every iteration's
        ``decimal_add`` allocates a new wrapper).
        """
        int_src = """
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  array_fold(
    array_range(0, 5),
    0,
    fn(@Int, @Int -> @Int) effects(pure) { @Int.0 + @Int.1 }
  )
}
"""
        decimal_src = """
public fn main(@Unit -> @Decimal)
  requires(true) ensures(true) effects(pure)
{
  array_fold(
    array_range(0, 5),
    decimal_from_int(0),
    fn(@Decimal, @Int -> @Decimal) effects(pure) {
      decimal_add(@Decimal.0, decimal_from_int(@Int.0))
    }
  )
}
"""
        self._assert_handle_extra_rooted_after_573(
            int_src, decimal_src, "array_fold", "accumulator",
        )

    def test_decimal_mapper_rooted_after_573(self) -> None:
        """`array_map` producing `Decimal` elements MUST root the
        wrapper pointer (post-#573 phase 3).

        Mirror of ``test_decimal_accumulator_rooted_after_573``
        for ``array_map``'s element-rooting heuristic
        (``t_is_adt``).
        """
        int_src = """
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  array_length(array_map(
    array_range(0, 5),
    fn(@Int -> @Int) effects(pure) { @Int.0 + 1 }
  ))
}
"""
        decimal_src = """
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  array_length(array_map(
    array_range(0, 5),
    fn(@Int -> @Decimal) effects(pure) { decimal_from_int(@Int.0) }
  ))
}
"""
        self._assert_handle_extra_rooted_after_573(
            int_src, decimal_src, "array_map", "element",
        )

    def test_array_fold_with_decimal_runs_correctly(self) -> None:
        """Functional pin: the fold over Decimal still produces the
        right result.  Pre- and post-fix this works (the
        conservative GC's heap-range check rejects small handle
        values either way), so this test passes in both states —
        but it pins that the structural optimisation didn't break
        anything.

        Sum 0+1+2+3+4 = 10; comparing to `decimal_from_int(10)`
        via `decimal_eq` returns 1.
        """
        src = """
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Decimal = array_fold(
    array_range(0, 5),
    decimal_from_int(0),
    fn(@Decimal, @Int -> @Decimal) effects(pure) {
      decimal_add(@Decimal.0, decimal_from_int(@Int.0))
    }
  );
  if decimal_eq(@Decimal.0, decimal_from_int(10)) then { 1 } else { 0 }
}
"""
        assert _run(src) == 1

    def test_array_map_with_decimal_runs_correctly(self) -> None:
        """Functional pin for the array_map case: produce an array
        of Decimal handles and verify the round-trip through
        `array_fold(decimal_add)` returns the right total.

        Pre- and post-fix this works (same conservative-GC
        argument as the fold case), but pinning prevents a
        future array_map regression from silently breaking the
        `Decimal` element path.

        `array_map([0..5), fn(i) { decimal_from_int(i*2) })`
        produces `[0, 2, 4, 6, 8]` as Decimal handles; folding
        with `decimal_add` gives 20.
        """
        src = """
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Array<Decimal> = array_map(
    array_range(0, 5),
    fn(@Int -> @Decimal) effects(pure) {
      decimal_from_int(@Int.0 * 2)
    }
  );
  let @Decimal = array_fold(
    @Array<Decimal>.0,
    decimal_from_int(0),
    fn(@Decimal, @Decimal -> @Decimal) effects(pure) {
      decimal_add(@Decimal.0, @Decimal.1)
    }
  );
  if decimal_eq(@Decimal.0, decimal_from_int(20)) then { 1 } else { 0 }
}
"""
        # 0 + 2 + 4 + 6 + 8 = 20
        assert _run(src) == 1

# =====================================================================
# Reclamation of transient Map / Set / Decimal values
# =====================================================================
# Historically (#573) every map_new / map_insert / map_remove
# allocated an entry in `_map_store` (in `vera/codegen/api.py`) that a
# Phase-2c `$gc_collect` walk evicted via `host_decref_handle` once the
# owning wrapper was unmarked.
#
# Post-#706 (bucket-as-truth): Map and Set hold no Python store at all
# — each op builds a fresh wrapper whose `bucket_ptr` (+8) owns the
# data, and transient wrappers + buckets are reclaimed by ordinary
# mark-sweep.  `ExecuteResult.peak_heap_bytes` (the exported `$heap_ptr`
# high-water mark) is the leak signal: a working reclaimer keeps it
# ~O(N) across an insert chain; a leak grows it ~O(N^2).  Decimal alone
# still uses a Python store, so `ExecuteResult.host_store_sizes` keeps
# reporting its post-execution population.
# =====================================================================


def _assert_chain_reclaims(
    chain,  # (int) -> str: builds the chain source for a given size
    small_n: int,
    large_n: int,
    small_val: int,
    large_val: int,
    ratio: int = 30,
) -> None:
    """#706: run an insert/add chain at two sizes and assert the heap
    high-water mark grows ~O(N), proving transient wrappers + buckets
    are reclaimed by mark-sweep.

    With power-of-two bucket sizing a working reclaimer reuses freed
    same-size buckets, so 10x the inserts gives only ~6x the peak heap.
    A leak (transients never freed) grows ~O(N^2) → ~100x.  The bound
    sits well between the two.
    """
    small = execute(_compile_ok(chain(small_n)))
    large = execute(_compile_ok(chain(large_n)))
    assert small.value == small_val, (
        f"chain(n={small_n}) returned {small.value}, expected {small_val}"
    )
    assert large.value == large_val, (
        f"chain(n={large_n}) returned {large.value}, expected {large_val}"
    )
    assert large.peak_heap_bytes < small.peak_heap_bytes * ratio, (
        f"#706 reclamation regression: peak heap for n={large_n} "
        f"({large.peak_heap_bytes:,} bytes) exceeds {ratio}x the n="
        f"{small_n} peak ({small.peak_heap_bytes:,} bytes).  Transient "
        f"Map/Set wrappers + buckets are not being reclaimed — O(N^2) "
        f"high-water growth indicates a leak, vs the ~O(N) expected from "
        f"mark-sweep plus power-of-two bucket sizing."
    )


class TestBucketOccupancy706:
    """#706: the 20-byte bucket slot carries an explicit occupancy flag,
    so an empty-string key (``(ptr, len) == (0, 0)``) and an Int ``0``
    key are distinguished from a genuinely empty slot — closing the
    sentinel collision the old write-only mirror left latent (#707
    review).
    """

    def test_empty_string_key_round_trips(self) -> None:
        """A "" key is found, not mistaken for an empty slot."""
        src = """
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Map<String, Int> = map_insert(map_new(), "", 42);
  match map_get(@Map<String, Int>.0, "") {
    Some(@Int) -> @Int.0,
    None -> -1
  }
}
"""
        assert _run(src) == 42

    def test_empty_string_key_miss_returns_none(self) -> None:
        """A different key still misses when only "" is present."""
        src = """
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Map<String, Int> = map_insert(map_new(), "", 42);
  match map_get(@Map<String, Int>.0, "x") {
    Some(@Int) -> @Int.0,
    None -> -1
  }
}
"""
        assert _run(src) == -1

    def test_int_zero_key_round_trips(self) -> None:
        """An Int 0 key is found, not mistaken for an empty slot."""
        src = """
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Map<Int, Int> = map_insert(map_new(), 0, 99);
  match map_get(@Map<Int, Int>.0, 0) {
    Some(@Int) -> @Int.0,
    None -> -1
  }
}
"""
        assert _run(src) == 99

    def test_empty_string_element_in_set(self) -> None:
        """A "" element round-trips through Set (occupancy flag)."""
        src = """
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Set<String> = set_add(set_new(), "");
  if set_contains(@Set<String>.0, "") then { 1 } else { 0 }
}
"""
        assert _run(src) == 1

    def test_empty_string_key_contains(self) -> None:
        """map_contains finds the "" key via the occupancy flag."""
        src = """
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Map<String, Int> = map_insert(map_new(), "", 42);
  if map_contains(@Map<String, Int>.0, "") then { 1 } else { 0 }
}
"""
        assert _run(src) == 1

    def test_empty_string_key_counts_in_size(self) -> None:
        """A "" key occupies a slot, so map_size counts it (not skipped
        as an empty slot)."""
        src = """
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Map<String, Int> = map_insert(map_new(), "", 42);
  nat_to_int(map_size(@Map<String, Int>.0))
}
"""
        assert _run(src) == 1

    def test_empty_string_key_removed(self) -> None:
        """map_remove("") clears the slot; a later lookup then misses,
        confirming the structural rebuild honours the sentinel key."""
        src = """
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Map<String, Int> = map_insert(map_new(), "", 42);
  let @Map<String, Int> = map_remove(@Map<String, Int>.0, "");
  match map_get(@Map<String, Int>.0, "") {
    Some(@Int) -> @Int.0,
    None -> -1
  }
}
"""
        assert _run(src) == -1


class TestAdtBuilderRooting743:
    """PR #743 (folded into #706): host-side ADT result builders root a
    freshly-allocated string / backing-array block across the enclosing
    struct/array alloc.

    The CLI ``_alloc_option_some_string`` / ``_alloc_result_*_string`` /
    ``_alloc_array_of_strings`` and the browser ``mapAllocOption`` /
    ``mapAllocArrayOfStrings`` / ``allocResult*String`` allocate a string,
    then allocate the wrapping struct/array — a GC fired by the second
    alloc would sweep the still-host-local string pointer and store a
    dangling reference.  Pre-existing (the #692/#695 work hardened the
    JSON/HTML walkers but not these simpler builders); surfaced by the
    CodeRabbit review of #706.  Reproduces only under ``VERA_EAGER_GC=1``
    / heap pressure.
    """

    def test_map_get_string_value_survives_eager_gc(
        self, monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        """500 ``map_get`` calls on a ``Map<Int, String>`` under eager GC
        each return the live string.  Pre-fix returned 0: the string block
        was swept during the ``Option<String>`` struct alloc and
        ``string_contains`` read reclaimed memory."""
        src = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Map<Int, String> = map_insert(map_new(), 1, "alphabet_soup_xyz");
  array_fold(
    array_range(0, 500),
    0,
    fn(@Int, @Int -> @Int) effects(pure) {
      match map_get(@Map<Int, String>.0, 1) {
        Some(@String) ->
          if string_contains(@String.0, "soup") then { @Int.1 + 1 }
          else { @Int.1 },
        None -> @Int.1
      }
    }
  )
}
"""
        monkeypatch.setenv("VERA_EAGER_GC", "1")
        assert _run(src) == 500

    def test_map_keys_string_backing_survives_eager_gc(
        self, monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        """``map_keys`` on a ``Map<String, Int>`` builds an
        ``Array<String>`` backing under eager GC, and this folds over that
        array reading each key's bytes via ``string_contains`` — so a
        backing (or key string) swept mid-fill reads garbage and misses
        the substring (or traps).  ``_alloc_array_of_strings`` roots the
        backing across the per-element string allocs; the outer fold
        rebuilds the keys array 200x to force free-block reuse.  ``array_fold``
        is the element accessor (``array_length`` reads the host-pushed
        count and would NOT dereference a swept backing)."""
        src = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Map<String, Int> = map_insert(map_insert(map_new(), "alpha_k", 1), "beta_k", 2);
  array_fold(
    array_range(0, 200),
    0,
    fn(@Int, @Int -> @Int) effects(pure) {
      let @Array<String> = map_keys(@Map<String, Int>.0);
      @Int.1 + array_fold(
        @Array<String>.0,
        0,
        fn(@Int, @String -> @Int) effects(pure) {
          if string_contains(@String.0, "_k") then { @Int.0 + 1 }
          else { @Int.0 }
        }
      )
    }
  )
}
"""
        monkeypatch.setenv("VERA_EAGER_GC", "1")
        # 200 outer x 2 keys (both contain "_k") = 400; a swept/corrupted
        # backing reads garbage bytes (miss) or traps.
        assert _run(src) == 400

    def test_regex_find_result_payload_survives_eager_gc(
        self, monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        """``regex_find`` wraps a freshly-built ``Option<String>`` in
        ``Result.Ok``; ``_alloc_result_ok_i32`` roots the payload across
        the struct alloc.  300x under eager GC the matched substring reads
        back intact — pre-fix the Option block was swept during the
        ``Result.Ok`` alloc.  (Same builder roots the Json / HtmlNode
        payloads of ``json_parse`` / ``html_parse``.)"""
        src = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  array_fold(
    array_range(0, 300),
    0,
    fn(@Int, @Int -> @Int) effects(pure) {
      match regex_find("alphabet_soup_xyz", "soup") {
        Ok(@Option<String>) ->
          match @Option<String>.0 {
            Some(@String) ->
              if string_contains(@String.0, "soup") then { @Int.1 + 1 }
              else { @Int.1 },
            None -> @Int.1
          },
        Err(@String) -> @Int.1
      }
    }
  )
}
"""
        monkeypatch.setenv("VERA_EAGER_GC", "1")
        assert _run(src) == 300

    def test_decimal_from_string_wrapper_survives_eager_gc(
        self, monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        """``decimal_from_string`` builds a Decimal wrapper, then wraps it
        in ``Option.Some`` via ``_alloc_option_some_i32``; the helper roots
        the wrapper across the struct alloc.  300x under eager GC the
        Decimal reads back as "3.14" — pre-fix the wrapper could be swept /
        Phase-2c-decref'd before the ``Some`` payload stored it."""
        src = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  array_fold(
    array_range(0, 300),
    0,
    fn(@Int, @Int -> @Int) effects(pure) {
      match decimal_from_string("3.14") {
        Some(@Decimal) ->
          if string_contains(decimal_to_string(@Decimal.0), "3.14")
          then { @Int.1 + 1 } else { @Int.1 },
        None -> @Int.1
      }
    }
  )
}
"""
        monkeypatch.setenv("VERA_EAGER_GC", "1")
        assert _run(src) == 300

    def test_regex_find_err_payload_survives_eager_gc(
        self, monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        """``regex_find`` with an invalid pattern returns ``Result.Err``
        via ``_alloc_result_err_string``; 300x under eager GC the error
        string reads back intact (the Err-path string builder roots its
        payload across the struct alloc)."""
        src = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  array_fold(
    array_range(0, 300),
    0,
    fn(@Int, @Int -> @Int) effects(pure) {
      match regex_find("x", "[") {
        Ok(@Option<String>) -> @Int.1,
        Err(@String) ->
          if string_contains(@String.0, "regex") then { @Int.1 + 1 }
          else { @Int.1 }
      }
    }
  )
}
"""
        monkeypatch.setenv("VERA_EAGER_GC", "1")
        assert _run(src) == 300


class TestSameValueZeroKeys743:
    """PR #743 (folded into #706): Float64 Map keys / Set elements compare
    under SameValueZero, so a NaN key/element round-trips (NaN equals NaN).

    Pre-existing: the CLI Python dict / the browser ``decodeColumn`` list
    use ``==`` / ``===``, which treat NaN as unequal to itself, so a NaN
    key could never be found, removed, or deduped.  ``0.0 / 0.0`` verifies
    and runs to NaN, so this is reachable.  Surfaced by the CodeRabbit
    review of #706.
    """

    def test_nan_map_key_found(self) -> None:
        """A NaN ``Float64`` map key is found by ``map_contains`` /
        ``map_get`` (pre-fix: not found → -1)."""
        src = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Float64 = 0.0 / 0.0;
  let @Map<Float64, Int> = map_insert(map_new(), @Float64.0, 42);
  if map_contains(@Map<Float64, Int>.0, @Float64.0) then {
    match map_get(@Map<Float64, Int>.0, @Float64.0) {
      Some(@Int) -> @Int.0,
      None -> -2
    }
  } else { -1 }
}
"""
        assert _run(src) == 42

    def test_nan_map_key_dedups_and_removes(self) -> None:
        """Inserting a NaN key twice dedups to one entry; ``map_remove``
        then clears it (pre-fix: dedup and removal both failed)."""
        src = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Float64 = 0.0 / 0.0;
  let @Map<Float64, Int> = map_insert(map_insert(map_new(), @Float64.0, 1), @Float64.0, 99);
  let @Int = nat_to_int(map_size(@Map<Float64, Int>.0));
  let @Map<Float64, Int> = map_remove(@Map<Float64, Int>.0, @Float64.0);
  let @Int = nat_to_int(map_size(@Map<Float64, Int>.0));
  @Int.1 * 100 + @Int.0
}
"""
        # size 1 after dedup, size 0 after remove → 100.
        assert _run(src) == 100

    def test_nan_set_element_round_trips(self) -> None:
        """A NaN ``Float64`` Set element dedups and is found by
        ``set_contains`` (pre-fix: duplicated and not found)."""
        src = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Float64 = 0.0 / 0.0;
  let @Set<Float64> = set_add(set_add(set_new(), @Float64.0), @Float64.0);
  if set_contains(@Set<Float64>.0, @Float64.0) then {
    nat_to_int(set_size(@Set<Float64>.0))
  } else { -1 }
}
"""
        # deduped to size 1; contains finds NaN → 1.
        assert _run(src) == 1

    def test_nan_set_element_removed(self) -> None:
        """``set_remove`` finds and drops a NaN element (SameValueZero in
        the structural rebuild); the later size is 0."""
        src = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Float64 = 0.0 / 0.0;
  let @Set<Float64> = set_add(set_new(), @Float64.0);
  let @Set<Float64> = set_remove(@Set<Float64>.0, @Float64.0);
  nat_to_int(set_size(@Set<Float64>.0))
}
"""
        assert _run(src) == 0


class TestHostHandleReclamation573:
    """Reclamation regressions originally for the heap-wrap-as-ADT
    migration of Map (#573), Set (#575), and Decimal (#576), updated
    for the #706 bucket-as-truth move.

    After #706 Map and Set hold no Python store: each op builds a fresh
    wrapper + bucket and the transients are reclaimed by ordinary
    mark-sweep (no Phase 2c destructor).  Decimal alone still uses a
    Python store, reclaimed via ``host_decref_handle``.

    Covers:

    * **chain reclaims transients** — a 1K/10K-iter ``array_fold``
      chain keeps only the final Map / Set reachable; ``peak_heap_bytes``
      grows ~O(N) (a leak would grow ~O(N^2)).  The Decimal chain still
      asserts a bounded host-store residual.
    * **value correct after pressure** — repeated lookups against the
      live final value across heavy GC cadence prove reclamation never
      evicts live entries.
    * **JObject bucket path at scale** — the JSON parser's internal
      ``Map<String, Json>`` allocations round-trip through the bucket
      codec thousands of times without corruption.
    * **wrap-table machinery present** — Map / Set / JSON / HTML /
      Decimal modules emit the ``host_decref_handle`` import,
      ``$register_wrapper`` (with its #579 compaction slow path), and
      export.  Post-#706 only Decimal actually registers; the infra is
      still gated on the broad ops predicate, so it is emitted (but
      unused) for non-Decimal modules too — conservative and
      correctness-neutral.
    """

    def test_map_chain_reclaims_transients(self) -> None:
        """#706: a long ``array_fold`` over ``map_insert`` keeps only the
        final Map reachable; every transient wrapper + bucket is
        reclaimed by ordinary mark-sweep (no Python store to evict).

        Measured via ``peak_heap_bytes`` (the bump high-water mark): with
        reclamation the heap grows ~O(N) across the chain (≈6x for 10x
        the inserts); a leak would grow ~O(N^2) (≈100x).
        """
        def chain(n: int) -> str:
            return f"""
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{{
  let @Map<Int, Int> = map_new();
  let @Map<Int, Int> = array_fold(
    array_range(1, {n + 1}),
    @Map<Int, Int>.0,
    fn(@Map<Int, Int>, @Int -> @Map<Int, Int>) effects(pure) {{
      map_insert(@Map<Int, Int>.0, @Int.0, @Int.0)
    }}
  );
  match map_get(@Map<Int, Int>.0, {n // 2}) {{
    Some(@Int) -> @Int.0,
    None -> -1
  }}
}}
"""
        _assert_chain_reclaims(chain, 1000, 10000, 500, 5000)

    def test_json_object_map_bucket_path_at_scale(self) -> None:
        """#706: JSON's internal ``Map<String, Json>`` for each JObject is
        a bucket-as-truth wrapper (``_alloc_map_wrapper``).  Parse 5 000
        transient JObjects in an iterative ``array_fold`` and read a field
        back out of each, round-tripping every one through the bucket
        *encode* (``_alloc_map_wrapper``) and *decode* (``_decode_map``
        via ``map_get``, reached through ``json_get_int``) paths at scale
        without corruption.

        This is a functional round-trip check, not a leak check.  Each
        JObject is a constant-size single-key map, so even total
        reclamation failure grows the heap only ~O(N) — the same order as
        the live ``array_range(0, N)`` input array — and a
        ``peak_heap_bytes`` ratio cannot separate the two (that signal
        needs healthy O(N) vs leaked O(N^2), which holds for the Map/Set
        chains above but never for constant-size transients).  Reclamation
        of these JObject wrappers is covered there — the chains leak
        O(N^2) through the same ``_alloc_map_wrapper`` encode path — and
        their value reachability by ``TestMapHostStoreGCReachability695``
        under ``VERA_EAGER_GC=1``.
        """
        src = """
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Int = 0;
  array_fold(
    array_range(0, 5000),
    @Int.0,
    fn(@Int, @Int -> @Int) effects(pure) {
      match json_parse("{\\"k\\": 7}") {
        Ok(@Json) ->
          match json_get_int(@Json.0, "k") {
            Some(@Int) -> @Int.2 + @Int.0,
            None -> @Int.1
          },
        Err(@String) -> @Int.1
      }
    }
  )
}
"""
        # 5 000 round-trips, each reading "k" = 7 back out → 5000 * 7.
        assert _run(src) == 35000

    def test_map_value_lookup_after_gc_pressure(self) -> None:
        """Functional integrity after heavy reclamation pressure.

        Pre-#573 the wrap-table walk wasn't running, so this would
        return the right answer trivially.  Post-#573 the destructor
        hook is firing on every transient — if it had a bug
        (off-by-one in compaction, wrong handle stored, etc.) the
        live Map's host store entry could be evicted by mistake
        and ``map_get`` would return None or trap.
        """
        src = """
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Map<Int, Int> = map_new();
  let @Map<Int, Int> = array_fold(
    array_range(0, 1000),
    @Map<Int, Int>.0,
    fn(@Map<Int, Int>, @Int -> @Map<Int, Int>) effects(pure) {
      map_insert(@Map<Int, Int>.0, @Int.0, @Int.0 * 7)
    }
  );
  --Look up several keys to force the live Map's entry to be
  --consulted multiple times across GC events.
  match map_get(@Map<Int, Int>.0, 0) {
    Some(@Int) -> match map_get(@Map<Int, Int>.0, 500) {
      Some(@Int) -> match map_get(@Map<Int, Int>.0, 999) {
        Some(@Int) -> @Int.0,
        None -> -1
      },
      None -> -2
    },
    None -> -3
  }
}
"""
        # 999 * 7 = 6993
        assert _run(src) == 6993

    def test_set_chain_reclaims_transients(self) -> None:
        """#706: a long ``array_fold`` over ``set_add`` keeps only the
        final Set reachable; transients are reclaimed by mark-sweep.

        Same ``peak_heap_bytes`` ~O(N) signal as the Map chain.
        """
        def chain(n: int) -> str:
            return f"""
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{{
  let @Set<Int> = set_new();
  let @Set<Int> = array_fold(
    array_range(1, {n + 1}),
    @Set<Int>.0,
    fn(@Set<Int>, @Int -> @Set<Int>) effects(pure) {{
      set_add(@Set<Int>.0, @Int.0)
    }}
  );
  if set_contains(@Set<Int>.0, {n // 2}) then {{ 1 }} else {{ 0 }}
}}
"""
        _assert_chain_reclaims(chain, 1000, 10000, 1, 1)

    def test_set_value_correct_after_gc_pressure(self) -> None:
        """Functional integrity for Set under GC pressure.

        Symmetric to the Map / Decimal lookup-after-pressure tests:
        if the Set destructor mechanism had a bug evicting live
        wrappers, ``set_contains`` would return false for elements
        that ARE in the live Set, or trap on a missing host-store
        entry.  Exercises 1 000 set_adds + multiple ``set_contains``
        and ``set_size`` calls on the live Set.
        """
        src = """
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Set<Int> = set_new();
  let @Set<Int> = array_fold(
    array_range(0, 1000),
    @Set<Int>.0,
    fn(@Set<Int>, @Int -> @Set<Int>) effects(pure) {
      set_add(@Set<Int>.0, @Int.0)
    }
  );
  --Three lookups + size, all on the same live Set across GC events.
  if set_contains(@Set<Int>.0, 0) then {
    if set_contains(@Set<Int>.0, 500) then {
      if set_contains(@Set<Int>.0, 999) then {
        nat_to_int(set_size(@Set<Int>.0))
      } else { -1 }
    } else { -2 }
  } else { -3 }
}
"""
        # 1000 distinct elements in [0, 1000) → size 1000.
        assert _run(src) == 1000

    def test_decimal_chain_reclaims_transients(self) -> None:
        """A 5 000-iteration ``array_fold`` over ``decimal_add``
        reclaims transients (#573 phase 3).

        Each iteration constructs a new Decimal handle via
        ``decimal_add`` (host_decimal_add allocates a fresh
        PyDecimal in ``_decimal_store``); the closure return is
        consumed by the next iteration.  Pre-fix store size was
        ~5 000+ (each intermediate plus per-iteration
        ``decimal_from_int(@Int.0)`` for the second arg).  Post-
        fix Phase 2c walks the wrap table and fires
        ``host_decref_handle(DECIMAL, handle)`` for every
        unmarked wrapper.

        Smaller iteration count than the Map test because
        ``decimal_add`` is more expensive per iteration (Python
        ``Decimal`` arithmetic vs. dict insertion).
        """
        src = """
public fn main(@Unit -> @Bool)
  requires(true) ensures(true) effects(pure)
{
  let @Decimal = array_fold(
    array_range(0, 5000),
    decimal_from_int(0),
    fn(@Decimal, @Int -> @Decimal) effects(pure) {
      decimal_add(@Decimal.0, decimal_from_int(@Int.0))
    }
  );
  --Sum 0 + 1 + ... + 4999 = 12 497 500.
  decimal_eq(@Decimal.0, decimal_from_int(12497500))
}
"""
        result = _compile_ok(src)
        exec_result = execute(result)
        assert exec_result.value == 1, (
            f"Decimal sum should equal 12 497 500; "
            f"got {exec_result.value}"
        )
        store_size = exec_result.host_store_sizes.get("decimal", 0)
        # Decimal accumulates ~2 entries per iteration pre-GC
        # (the old accumulator + the from_int(idx)) plus the
        # final decimal_eq pair.  Bound is more generous than
        # Map because the arithmetic path is denser.
        assert store_size < 1500, (
            f"#573 phase 3 regression: _decimal_store has "
            f"{store_size} entries after 5 000 decimal_add "
            f"iterations.  Pre-fix this was monotonic at "
            f"~10 000+; post-fix Phase 2c reclaims unreachable "
            f"Decimal wrappers via `kind == 3` in "
            f"host_decref_handle.  A size > 1 500 indicates "
            f"reclamation isn't keeping pace with allocation."
        )

    def test_json_only_module_includes_wrap_table(self) -> None:
        """A module that uses ONLY ``json_parse`` (no user-level
        ``map_*`` ops) still emits the wrap-table infrastructure
        (``host_decref_handle`` import, ``$register_wrapper``, export).

        The ``_decref_used`` / ``_needs_wrap_table`` predicates flip on
        ``_json_ops_used`` / ``_html_ops_used`` (this was #573 finding
        5: JSON / HTML modules must not trap at instantiation when the
        host accesses the ``register_wrapper`` export).  Post-#706
        ``write_json``'s JObject branch builds its ``Map<String, Json>``
        as a bucket-as-truth wrapper, which does NOT register — so this
        infra is conservatively emitted but unused for a JSON-only
        module (Decimal is the only registerer post-#706).  This
        structural test pins that the emission + instantiation path
        stays present and trap-free.
        """
        src = """
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Result<Json, String> = json_parse("{\\"a\\": 1}");
  match @Result<Json, String>.0 {
    Ok(@Json) -> 1,
    Err(@String) -> 0
  }
}
"""
        wat = _compile_ok(src).wat
        assert (
            'import "vera" "host_decref_handle"' in wat
        ), (
            "#573 finding 5 regression: JSON-only program is "
            "missing the host_decref_handle import (gated on "
            "_json_ops_used so the wrap-table machinery is present)."
        )
        assert "$register_wrapper" in wat, (
            "#573 finding 5 regression: JSON-only program is "
            "missing the $register_wrapper helper; the host must not "
            "trap at instantiation reaching for the export."
        )
        assert '(export "register_wrapper"' in wat, (
            "#573 finding 5 regression: JSON-only program is "
            "missing the register_wrapper export."
        )
        # Functional check too: the program runs and returns 1.
        assert _run(src) == 1

    def test_html_only_module_includes_wrap_table(self) -> None:
        """An HTML-using program emits the wrap-table machinery
        (mirror of ``test_json_only_module_includes_wrap_table``).

        ``write_html``'s HtmlElement attrs branch builds its
        ``Map<String, String>`` as a bucket-as-truth wrapper exactly
        like ``write_json``'s JObject branch — neither registers
        post-#706, so the infra is emitted (gated on ``_html_ops_used``)
        but unused here.  Compiling ``html_parse`` typically also pulls
        in the prelude's ``html_attr`` (which dispatches to
        ``map_get``), so ``_map_ops_used`` is set anyway in practice —
        but the ``_html_ops_used`` gating is the load-bearing one if
        that prelude transitivity ever changes.
        """
        src = """
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  match html_parse("<p>hello</p>") {
    Ok(@HtmlNode) -> 1,
    Err(@String) -> 0
  }
}
"""
        wat = _compile_ok(src).wat
        assert (
            'import "vera" "host_decref_handle"' in wat
        ), (
            "#573 finding 5 regression (HTML): missing "
            "host_decref_handle import (gated on _html_ops_used so "
            "the wrap-table machinery is present)."
        )
        assert "$register_wrapper" in wat, (
            "#573 finding 5 regression (HTML): missing "
            "$register_wrapper helper."
        )
        assert '(export "register_wrapper"' in wat, (
            "#573 finding 5 regression (HTML): missing "
            "register_wrapper export."
        )
        assert _run(src) == 1

    def test_register_wrapper_has_compaction_slow_path(self) -> None:
        """``$register_wrapper`` triggers ``$gc_collect`` on
        overflow before trapping (#579).

        Pre-#579 the function trapped with ``unreachable`` the
        moment ``$gc_wrap_ptr >= $gc_wrap_end`` — even if
        compaction would have freed thousands of dead entries.
        Post-fix the slow path roots the in-flight wrapper on
        the shadow stack, calls ``$gc_collect`` (which runs
        Phase 2c compaction), pops the root, and re-checks; only
        if the table is still full does it trap.

        This is a structural test rather than functional because
        triggering the slow path under a real workload is hard:
        every wrapper IS also a heap allocation, so wrap-table-
        full and heap-full happen at similar cadences and
        ``$alloc`` triggers GC first under normal conditions.
        Asserting the slow-path WAT is present pins that the
        emitter wired up the compaction call correctly; if a
        future refactor reverts to the unconditional trap, this
        test catches it.
        """
        src = """
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Map<Int, Int> = map_new();
  match map_get(@Map<Int, Int>.0, 1) {
    Some(@Int) -> @Int.0,
    None -> 0
  }
}
"""
        wat = _compile_ok(src).wat
        # Locate the $register_wrapper function body.
        fn_match = re.search(
            r"\(func \$register_wrapper\b.*?(?=\n  \(func |\n\s*\)\s*$)",
            wat, re.DOTALL,
        )
        assert fn_match is not None, (
            "$register_wrapper not emitted in WAT — wrap-table "
            "infrastructure may be missing despite a Map op being "
            "used"
        )
        body = fn_match.group(0)
        # Slow path must call $gc_collect.
        assert "call $gc_collect" in body, (
            "#579 regression: $register_wrapper has no "
            "$gc_collect call in its overflow path.  Pre-#579 it "
            "trapped unconditionally; post-fix it must compact "
            "first.  Without the slow path, programs hitting the "
            "wrap-table ceiling trap even when most entries are "
            "dead and would be reclaimed by Phase 2c."
        )
        # Slow path must shadow-push the in-flight wrapper before
        # the collect (otherwise GC frees the just-allocated
        # wrapper body and we append to a dangling pointer).
        # The push idiom: global.get $gc_sp; local.get $ptr;
        # i32.store; ...; global.set $gc_sp.
        push_before_collect = re.search(
            r"global\.get \$gc_sp\s+"
            r"local\.get \$ptr\s+"
            r"i32\.store\s+"
            r"global\.get \$gc_sp\s+"
            r"i32\.const 4\s+"
            r"i32\.add\s+"
            r"global\.set \$gc_sp.*?"
            r"call \$gc_collect",
            body, re.DOTALL,
        )
        assert push_before_collect is not None, (
            "#579 regression: $register_wrapper calls "
            "$gc_collect but doesn't shadow-push $ptr first.  "
            "Without rooting, Phase 2b marks the in-flight "
            "wrapper unreachable, Phase 3 frees it, and the "
            "post-collect append writes to a freed object."
        )
        # And there should be a re-check after the collect — two
        # `i32.ge_u` operations (the initial overflow check, and
        # the post-compaction re-check).
        assert body.count("i32.ge_u") >= 2, (
            "#579 regression: $register_wrapper has fewer than 2 "
            "`i32.ge_u` ops; the post-compaction re-check is "
            "likely missing."
        )
        # Shadow-stack must be balanced on the trap path.  The
        # pop of the temporary root must appear BEFORE the
        # re-check guard — if the trap fires, the pop has
        # already executed and the shadow stack is balanced.
        # Pop idiom: ``global.get $gc_sp; i32.const 4; i32.sub;
        # global.set $gc_sp``.  Re-check idiom: ``global.get
        # $gc_wrap_ptr; global.get $gc_wrap_end; i32.ge_u``.
        # Match both with the pop strictly preceding the
        # re-check (in the same slow-path region).
        balance_pattern = re.search(
            r"call \$gc_collect.*?"
            r"global\.get \$gc_sp\s+"
            r"i32\.const 4\s+"
            r"i32\.sub\s+"
            r"global\.set \$gc_sp.*?"
            r"global\.get \$gc_wrap_ptr\s+"
            r"global\.get \$gc_wrap_end\s+"
            r"i32\.ge_u",
            body, re.DOTALL,
        )
        assert balance_pattern is not None, (
            "#579 regression: shadow-stack imbalance on trap "
            "path.  The pop of the temporary root must appear "
            "between $gc_collect and the post-compaction "
            "re-check guard — otherwise the trap leaves $gc_sp "
            "one slot above its caller-entry level.  Today the "
            "trap is `unreachable` and the WASM module aborts, "
            "so the imbalance has no observable effect, but "
            "treating WAT shadow-stack discipline as a hard "
            "invariant catches regressions before any future "
            "change makes the trap recoverable."
        )

    def test_decimal_value_correct_after_gc_pressure(self) -> None:
        """Functional integrity for Decimal under GC pressure.

        Same shape as ``test_map_value_lookup_after_gc_pressure``:
        if the Decimal destructor mechanism had a bug that evicted
        live wrappers, ``decimal_eq`` would either return false or
        trap on a missing host-store entry.
        """
        src = """
public fn main(@Unit -> @Bool)
  requires(true) ensures(true) effects(pure)
{
  let @Decimal = array_fold(
    array_range(1, 1001),
    decimal_from_int(0),
    fn(@Decimal, @Int -> @Decimal) effects(pure) {
      decimal_add(
        @Decimal.0,
        decimal_mul(decimal_from_int(@Int.0), decimal_from_int(2))
      )
    }
  );
  --Sum 2*(1+2+...+1000) = 2 * 500 500 = 1 001 000.
  decimal_eq(@Decimal.0, decimal_from_int(1001000))
}
"""
        assert _run(src) == 1


# =====================================================================
# #692: host-walker GC rooting regression
# =====================================================================


class TestHostWalkerGCRooting692:
    """Pin the #692 fix: host-side tree walkers (``write_html`` /
    ``write_json`` / ``write_md_block``) must root intermediate
    WASM heap pointers on the shadow stack across recursion, so a
    ``$gc_collect`` triggered by sub-allocs does not reclaim them
    and corrupt the free list.

    The bug was reported externally with the current `FAQ.md`
    body (~25 KB) as the trigger.  These tests use a checked-in
    fixture path so the regression survives FAQ edits.

    Cousin tests for the WAT-side shadow-stack class:
    ``TestArrayMapGCRooting570``, ``TestFoldAccumulator515``,
    ``TestClosureReturnShadowAsymmetry593``.
    """

    def test_html_parse_500_element_siblings(self) -> None:
        """500 ``<a>x</a>`` siblings — exercises ``write_html``'s
        element branch (arr_ptr, name_ptr, wrapper_ptr) across
        500 iterations.  Heap grows from 1 page to ~3 pages,
        firing multiple ``$gc_collect`` cycles during the walk.
        Pre-#692-fix this trapped with ``Out-of-bounds memory
        access`` at ``0xfffffffd`` from inside ``$alloc``."""
        src = """
effect IO { op print(String -> Unit); }
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @String = string_repeat("<a>x</a>", 500);
  match html_parse(@String.0) {
    Ok(_) -> IO.print("ok"),
    Err(_) -> IO.print("err")
  }
}
"""
        assert _run_io(src) == "ok"

    def test_json_parse_1000_number_array(self) -> None:
        """1000-element JArray of JNumbers — exercises
        ``write_json``'s JArray branch (arr_ptr rooting across
        1000 sub-allocs).  Each JNumber is 16 bytes of heap so
        the array alone produces ~16 KB of allocations on top of
        the input string."""
        src = """
effect IO { op print(String -> Unit); }
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @String = string_concat(
    "[", string_concat(string_repeat("1,", 999), "1]")
  );
  match json_parse(@String.0) {
    Ok(_) -> IO.print("ok"),
    Err(_) -> IO.print("err")
  }
}
"""
        assert _run_io(src) == "ok"

    def test_json_parse_500_string_array(self) -> None:
        """500-element JArray of JStrings — exercises BOTH the
        JArray arr_ptr rooting AND the JString fields-first-then-
        body convention.  Each iteration allocates a string body
        and a 16-byte JString wrapper, doubling the alloc count
        per element vs the JNumber test above."""
        src = """
effect IO { op print(String -> Unit); }
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @String = string_concat(
    "[",
    string_concat(string_repeat("\\"hello world\\",", 499), "\\"end\\"]")
  );
  match json_parse(@String.0) {
    Ok(_) -> IO.print("ok"),
    Err(_) -> IO.print("err")
  }
}
"""
        assert _run_io(src) == "ok"

    def test_md_parse_200_headings(self) -> None:
        """200 H1 + paragraph blocks — exercises ``write_md_block``
        and ``write_md_inline`` walkers, including the
        ``_write_inline_array`` / ``_write_block_array`` backing
        rooting."""
        src = """
effect IO { op print(String -> Unit); }
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @String = string_repeat("# heading\\n\\nparagraph text\\n\\n", 200);
  match md_parse(@String.0) {
    Ok(_) -> IO.print("ok"),
    Err(_) -> IO.print("err")
  }
}
"""
        assert _run_io(src) == "ok"

    def test_html_query_30_matches(self) -> None:
        """``html_query`` over 30 matches — exercises the
        ``host_html_query`` `_ShadowGuard` path that also gained
        rooting in #692.  Without the guard, ``arr_ptr`` for the
        match-array would be reclaimed when recursive
        ``write_html`` calls grow the heap mid-walk.  Per the
        pr-review-toolkit pr-test-analyzer review on #693.

        Sized conservatively (30 vs the 500 used by html_parse
        tests above): ``host_html_query`` re-walks every matched
        subtree via ``write_html`` within a single guard window,
        accumulating pushes across all iterations.  The
        shadow-stack budget per match in practice (including the
        ``_alloc_map_wrapper`` and ``_register_wrapper`` calls
        and the WAT-side ``$alloc`` accounting) is materially
        higher than the four nominal pushes (name, wrapper, arr,
        s_ptr) of write_html element-branch — 100 matches
        empirically overflowed the 4096-entry stack.  30 still
        triggers GC during the walk while staying comfortable
        under the limit."""
        src = """
effect IO { op print(String -> Unit); }
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @String = string_concat(
    "<root>",
    string_concat(string_repeat("<p>x</p>", 30), "</root>")
  );
  match html_parse(@String.0) {
    Ok(@HtmlNode) -> {
      let @Array<HtmlNode> = html_query(@HtmlNode.0, "p");
      IO.print("ok")
    },
    Err(_) -> IO.print("parse_err")
  }
}
"""
        assert _run_io(src) == "ok"

    def test_json_parse_500_key_object(self) -> None:
        """500-key flat JObject — exercises the JObject branch of
        ``write_json`` (val_ptr push per iteration, wrapper_ptr
        push, then body alloc).  Pre-fix, the val_ptrs held in
        ``map_dict`` as Python ints were invisible to the
        conservative GC scan; a sub-walk's GC could free them.
        Per the pr-review-toolkit pr-test-analyzer review on #693."""
        src = """
effect IO { op print(String -> Unit); }
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @String = string_concat(
    "{",
    string_concat(
      string_repeat("\\"k\\":0,", 499),
      "\\"last\\":0}"
    )
  );
  match json_parse(@String.0) {
    Ok(_) -> IO.print("ok"),
    Err(_) -> IO.print("err")
  }
}
"""
        assert _run_io(src) == "ok"


class TestMapHostStoreGCReachability695:
    """Regression suite for #695 / #705 — pre-fix, ``Map<K, T_heap>``
    and ``Set<T_heap>`` values stored in Python-side ``_map_store`` /
    ``_set_store`` were invisible to the conservative GC scan, so a
    ``$gc_collect`` between map / set construction and value access
    reclaimed the heap blocks pointed to from the dict.

    Empirically pre-fix: with ``VERA_EAGER_GC=1`` (forces a
    ``$gc_collect`` on every alloc), the reproducer printed ``0``
    instead of the JArray's actual length ``10`` — silent
    use-after-free, no trap.  The ``0`` came from the free-list's
    next-pointer overwriting the freed block's first word, which
    ``json_array_length`` then read as a length.

    Post-fix (#706 bucket-as-truth): every Map / Set wrapper carries a
    ``bucket_ptr`` at body offset +8 pointing to a WASM-resident bucket
    that IS the map / set — there is no ``_map_store`` / ``_set_store``
    anymore.  The conservative scan reaches the values via shadow stack
    → wrapper → bucket → val_ptr, so a ``Json`` value held only inside a
    Set or JObject stays reachable across the synchronous host call.

    Each test in this class drives the reproducer under
    ``VERA_EAGER_GC=1`` and asserts the post-fix value (e.g. ``10``)
    is observed.  A regression that breaks bucket reachability — the
    encode-time shadow-rooting of the new wrapper + bucket in
    ``_encode_entries`` / ``_alloc_map_wrapper``, or the match-arm /
    let-binding shadow-rooting in ``vera/wasm/data.py`` /
    ``vera/wasm/context.py`` — flips the assertion back to ``0``.
    """

    def test_eager_gc_set_of_json_post_walk_uaf(
        self,
        monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        """Regression for the Set sibling bug (#705).

        Builds a ``Set<Json>`` inside a helper function so the
        original ``@Json`` local goes out of scope when the helper
        returns.  After that, the JArray's heap pointer is held
        only via ``_set_store[handle]`` (Python, invisible to GC)
        — without the bucket-array fix, ``VERA_EAGER_GC=1``
        reclaims the JArray block during ``set_to_array``'s alloc
        and ``json_array_length`` reads from freed memory,
        returning 0.

        Sister test to ``test_eager_gc_json_object_with_array_
        child_post_walk_uaf``: same bug class (host-store values
        invisible to conservative scan), different container.
        """
        src = """
effect IO { op print(String -> Unit); }

private fn build_set(-> @Set<Json>)
  requires(true) ensures(true) effects(pure)
{
  let @Result<Json, String> = json_parse(
    "[1,2,3,4,5,6,7,8,9,10]"
  );
  match @Result<Json, String>.0 {
    Ok(@Json) -> set_add(set_new(), @Json.0),
    Err(@String) -> set_new()
  }
}

public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Set<Json> = build_set();
  let @Array<Json> = set_to_array(@Set<Json>.0);
  let @Int = array_fold(@Array<Json>.0, 0, fn(@Int, @Json -> @Int) effects(pure) {
    json_array_length(@Json.0) + @Int.0
  });
  IO.print(int_to_string(@Int.0))
}
"""
        monkeypatch.setenv("VERA_EAGER_GC", "1")
        assert _run_io(src) == "10"

    def test_eager_gc_json_object_with_array_child_post_walk_uaf(
        self,
        monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        """``json_parse`` builds ``Map<String, Json>`` where the
        "key" entry is a JArray heap block.  The block is held only
        via ``_map_store[handle]["key"]`` — a Python int the
        conservative scan never visits.

        With ``VERA_EAGER_GC=1`` the ``Option`` alloc inside
        ``json_get`` triggers ``$gc_collect`` between ``json_parse``
        returning and the array length being read, freeing the
        JArray block.  ``json_array_length`` reads from the freed
        block and returns 0 instead of 10.

        Post-fix (this PR, "mirror" approach): the JArray pointer is
        also written to the bucket array at slot+8 by
        ``_alloc_map_wrapper`` / ``_attach_bucket_from_dict``, so
        the conservative scan reaches it via wrapper → bucket → slot.
        ``json_get`` retrieves the still-live block and the assertion
        observes ``10``.  The architectural follow-up — move ``_map_store``
        reads into the bucket array and delete the Python store entirely
        — is tracked as #706.
        """
        src = """
effect IO { op print(String -> Unit); }

public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Result<Json, String> = json_parse(
    "{\\"key\\": [1,2,3,4,5,6,7,8,9,10]}"
  );
  match @Result<Json, String>.0 {
    Ok(@Json) -> {
      let @Option<Json> = json_get(@Json.0, "key");
      match @Option<Json>.0 {
        Some(@Json) -> {
          let @Int = json_array_length(@Json.0);
          IO.print(int_to_string(@Int.0))
        },
        None -> IO.print("none")
      }
    },
    Err(@String) -> IO.print("err")
  }
}
"""
        monkeypatch.setenv("VERA_EAGER_GC", "1")
        assert _run_io(src) == "10"

    def test_eager_gc_map_of_json_user_level_post_walk_uaf(
        self,
        monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        """Regression for the user-level ``Map<String, T_heap>`` path.

        Where ``test_eager_gc_json_object_with_array_child_post_walk_uaf``
        exercises the JSON parser's internal ``Map<String, Json>``
        construction (via ``_alloc_map_wrapper`` / ``json_parse``),
        this test exercises the user-level path: a Vera program
        explicitly calling ``map_insert`` on a ``Json`` value
        returned from ``json_parse``.  Same bug class but a
        different alloc / wrap entry point — without the bucket
        array mirror, the JArray's heap pointer is held only via
        ``_map_store[handle]["arr"]`` (a Python int) until the
        ``map_get`` retrieves it; ``VERA_EAGER_GC=1`` triggers a
        ``$gc_collect`` during the intervening Option / Json
        accessor allocs and reclaims the JArray block.

        Closes the scope gap discussed on #705: the user-level
        wrapper path was tested for Set but not yet for Map.
        """
        src = """
effect IO { op print(String -> Unit); }

private fn build_map(-> @Map<String, Json>)
  requires(true) ensures(true) effects(pure)
{
  let @Result<Json, String> = json_parse(
    "[1,2,3,4,5,6,7,8,9,10]"
  );
  match @Result<Json, String>.0 {
    Ok(@Json) -> map_insert(map_new(), "arr", @Json.0),
    Err(@String) -> map_new()
  }
}

public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Map<String, Json> = build_map();
  let @Option<Json> = map_get(@Map<String, Json>.0, "arr");
  match @Option<Json>.0 {
    Some(@Json) -> {
      let @Int = json_array_length(@Json.0);
      IO.print(int_to_string(@Int.0))
    },
    None -> IO.print("none")
  }
}
"""
        monkeypatch.setenv("VERA_EAGER_GC", "1")
        assert _run_io(src) == "10"

    def test_eager_gc_let_destruct_with_json_field_post_walk_uaf(
        self,
        monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        """Regression for the ``let Ctor(@T_heap, ...) = ...`` path.

        PR #707 review (pr-test-analyzer I1): the round-2 fix in
        ``vera/wasm/data.py::_translate_let_destruct`` and the
        round-3 pair-type extension there had NO regression test
        — a refactor that drops the ``self.needs_alloc = True;
        gc_shadow_push(local_idx)`` block would silently pass CI.

        This test:
          1. ``let Tuple<@Json, @String> = Tuple(json_ptr, "tag");``
             extracts BOTH an ``i32`` heap-pointer field (`@Json`)
             and a pair-type field (`@String`).
          2. ``json_array_length(@Json.0)`` then allocates inside
             the EAGER_GC window — without the shadow-push fix on
             either rooting site, the Json buffer would be reclaimed
             between the extraction and the access.

        Asserts ``10`` (the JArray length).  A regression would
        print ``0`` from a freed-block-misread.
        """
        src = """
effect IO { op print(String -> Unit); }

public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Result<Json, String> = json_parse(
    "[1,2,3,4,5,6,7,8,9,10]"
  );
  match @Result<Json, String>.0 {
    Ok(@Json) -> {
      let Tuple<@Json, @String> = Tuple(@Json.0, "tag");
      let @Int = json_array_length(@Json.0);
      IO.print(int_to_string(@Int.0))
    },
    Err(@String) -> IO.print("err")
  }
}
"""
        monkeypatch.setenv("VERA_EAGER_GC", "1")
        assert _run_io(src) == "10"

    def test_eager_gc_match_binding_pattern_heap_pointer_post_walk_uaf(
        self,
        monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        """Regression for the ``match expr { @T_heap -> ... }`` path.

        PR #707 review (pr-test-analyzer I2): the round-1 fix in
        ``vera/wasm/data.py`` ``ast.BindingPattern`` handler (the
        ``match @Json.0 { @Json -> ... }`` shape) was unexercised.
        All three existing regression tests use the
        ``ConstructorPattern`` shape (`Ok(@Json) ->`), which goes
        through ``_extract_constructor_fields`` — a different code
        path.  Dropping the ``gc_shadow_push(local_idx)`` block in
        the ``BindingPattern`` branch left no test to catch it.

        This test exercises the bare ``@Json`` binding-pattern with
        an intervening allocation (``set_add(set_new(), @Json.0)``)
        between binding and the final array-length probe.  A
        regression would reclaim the bound Json buffer mid-set-add
        and the assertion would observe ``0``.
        """
        src = """
effect IO { op print(String -> Unit); }

public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Result<Json, String> = json_parse("[10,20,30]");
  match @Result<Json, String>.0 {
    Ok(@Json) -> match @Json.0 {
      @Json -> {
        let @Set<Json> = set_add(set_new(), @Json.0);
        IO.print(int_to_string(json_array_length(@Json.0)))
      }
    },
    Err(@String) -> IO.print("err")
  }
}
"""
        monkeypatch.setenv("VERA_EAGER_GC", "1")
        assert _run_io(src) == "3"
