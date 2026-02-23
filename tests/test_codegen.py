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

from vera.codegen import CompileResult, ExecuteResult, compile, execute
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
        assert _run("fn f(-> @Int) requires(true) ensures(true) effects(pure) { 0 }") == 0

    def test_positive(self) -> None:
        assert _run("fn f(-> @Int) requires(true) ensures(true) effects(pure) { 42 }") == 42

    def test_negative(self) -> None:
        assert _run("fn f(-> @Int) requires(true) ensures(true) effects(pure) { -1 }") == -1

    def test_large(self) -> None:
        assert _run(
            "fn f(-> @Int) requires(true) ensures(true) effects(pure) "
            "{ 9999999999 }"
        ) == 9999999999


class TestBoolLit:
    def test_true(self) -> None:
        assert _run("fn f(-> @Bool) requires(true) ensures(true) effects(pure) { true }") == 1

    def test_false(self) -> None:
        assert _run("fn f(-> @Bool) requires(true) ensures(true) effects(pure) { false }") == 0


class TestCompileResult:
    def test_wat_not_empty(self) -> None:
        result = _compile_ok("fn f(-> @Int) requires(true) ensures(true) effects(pure) { 42 }")
        assert "(module" in result.wat
        assert "i64.const 42" in result.wat

    def test_wasm_bytes_not_empty(self) -> None:
        result = _compile_ok("fn f(-> @Int) requires(true) ensures(true) effects(pure) { 42 }")
        assert len(result.wasm_bytes) > 0

    def test_exports_list(self) -> None:
        result = _compile_ok("fn f(-> @Int) requires(true) ensures(true) effects(pure) { 42 }")
        assert "f" in result.exports

    def test_ok_property(self) -> None:
        result = _compile_ok("fn f(-> @Int) requires(true) ensures(true) effects(pure) { 42 }")
        assert result.ok is True


# =====================================================================
# 5b: Slot references + arithmetic
# =====================================================================


class TestSlotRef:
    def test_identity_int(self) -> None:
        """fn id(@Int -> @Int) { @Int.0 }"""
        assert _run(
            "fn id(@Int -> @Int) requires(true) ensures(true) effects(pure) "
            "{ @Int.0 }",
            fn="id", args=[7],
        ) == 7

    def test_identity_bool(self) -> None:
        assert _run(
            "fn id(@Bool -> @Bool) requires(true) ensures(true) effects(pure) "
            "{ @Bool.0 }",
            fn="id", args=[1],
        ) == 1

    def test_two_params_same_type(self) -> None:
        """@Int.0 = second param, @Int.1 = first param."""
        assert _run(
            "fn first(@Int, @Int -> @Int) requires(true) ensures(true) "
            "effects(pure) { @Int.1 }",
            fn="first", args=[10, 20],
        ) == 10

    def test_second_param(self) -> None:
        assert _run(
            "fn second(@Int, @Int -> @Int) requires(true) ensures(true) "
            "effects(pure) { @Int.0 }",
            fn="second", args=[10, 20],
        ) == 20


class TestArithmetic:
    def test_add(self) -> None:
        assert _run(
            "fn add(@Int, @Int -> @Int) requires(true) ensures(true) "
            "effects(pure) { @Int.1 + @Int.0 }",
            fn="add", args=[3, 4],
        ) == 7

    def test_sub(self) -> None:
        assert _run(
            "fn sub(@Int, @Int -> @Int) requires(true) ensures(true) "
            "effects(pure) { @Int.1 - @Int.0 }",
            fn="sub", args=[10, 3],
        ) == 7

    def test_mul(self) -> None:
        assert _run(
            "fn mul(@Int, @Int -> @Int) requires(true) ensures(true) "
            "effects(pure) { @Int.1 * @Int.0 }",
            fn="mul", args=[6, 7],
        ) == 42

    def test_div(self) -> None:
        assert _run(
            "fn div(@Int, @Int -> @Int) requires(@Int.0 != 0) ensures(true) "
            "effects(pure) { @Int.1 / @Int.0 }",
            fn="div", args=[10, 3],
        ) == 3

    def test_mod(self) -> None:
        assert _run(
            "fn rem(@Int, @Int -> @Int) requires(@Int.0 != 0) ensures(true) "
            "effects(pure) { @Int.1 % @Int.0 }",
            fn="rem", args=[10, 3],
        ) == 1

    def test_nested_arithmetic(self) -> None:
        """(a + b) * (a - b)"""
        assert _run(
            "fn f(@Int, @Int -> @Int) requires(true) ensures(true) "
            "effects(pure) { (@Int.1 + @Int.0) * (@Int.1 - @Int.0) }",
            fn="f", args=[5, 3],
        ) == (5 + 3) * (5 - 3)


class TestComparison:
    def test_eq_true(self) -> None:
        assert _run(
            "fn f(@Int, @Int -> @Bool) requires(true) ensures(true) "
            "effects(pure) { @Int.1 == @Int.0 }",
            fn="f", args=[5, 5],
        ) == 1

    def test_eq_false(self) -> None:
        assert _run(
            "fn f(@Int, @Int -> @Bool) requires(true) ensures(true) "
            "effects(pure) { @Int.1 == @Int.0 }",
            fn="f", args=[5, 6],
        ) == 0

    def test_neq(self) -> None:
        assert _run(
            "fn f(@Int, @Int -> @Bool) requires(true) ensures(true) "
            "effects(pure) { @Int.1 != @Int.0 }",
            fn="f", args=[5, 6],
        ) == 1

    def test_lt(self) -> None:
        assert _run(
            "fn f(@Int, @Int -> @Bool) requires(true) ensures(true) "
            "effects(pure) { @Int.1 < @Int.0 }",
            fn="f", args=[3, 5],
        ) == 1

    def test_gt(self) -> None:
        assert _run(
            "fn f(@Int, @Int -> @Bool) requires(true) ensures(true) "
            "effects(pure) { @Int.1 > @Int.0 }",
            fn="f", args=[5, 3],
        ) == 1

    def test_le(self) -> None:
        assert _run(
            "fn f(@Int, @Int -> @Bool) requires(true) ensures(true) "
            "effects(pure) { @Int.1 <= @Int.0 }",
            fn="f", args=[5, 5],
        ) == 1

    def test_ge(self) -> None:
        assert _run(
            "fn f(@Int, @Int -> @Bool) requires(true) ensures(true) "
            "effects(pure) { @Int.1 >= @Int.0 }",
            fn="f", args=[5, 3],
        ) == 1


class TestBooleanLogic:
    def test_and(self) -> None:
        assert _run(
            "fn f(@Bool, @Bool -> @Bool) requires(true) ensures(true) "
            "effects(pure) { @Bool.1 && @Bool.0 }",
            fn="f", args=[1, 1],
        ) == 1

    def test_and_false(self) -> None:
        assert _run(
            "fn f(@Bool, @Bool -> @Bool) requires(true) ensures(true) "
            "effects(pure) { @Bool.1 && @Bool.0 }",
            fn="f", args=[1, 0],
        ) == 0

    def test_or(self) -> None:
        assert _run(
            "fn f(@Bool, @Bool -> @Bool) requires(true) ensures(true) "
            "effects(pure) { @Bool.1 || @Bool.0 }",
            fn="f", args=[0, 1],
        ) == 1

    def test_not(self) -> None:
        assert _run(
            "fn f(@Bool -> @Bool) requires(true) ensures(true) "
            "effects(pure) { !@Bool.0 }",
            fn="f", args=[1],
        ) == 0

    def test_implies_true(self) -> None:
        """false ==> anything is true."""
        assert _run(
            "fn f(@Bool, @Bool -> @Bool) requires(true) ensures(true) "
            "effects(pure) { @Bool.1 ==> @Bool.0 }",
            fn="f", args=[0, 0],
        ) == 1

    def test_implies_false(self) -> None:
        """true ==> false is false."""
        assert _run(
            "fn f(@Bool, @Bool -> @Bool) requires(true) ensures(true) "
            "effects(pure) { @Bool.1 ==> @Bool.0 }",
            fn="f", args=[1, 0],
        ) == 0


class TestUnaryOps:
    def test_neg(self) -> None:
        assert _run(
            "fn neg(@Int -> @Int) requires(true) ensures(true) "
            "effects(pure) { -@Int.0 }",
            fn="neg", args=[5],
        ) == -5

    def test_neg_negative(self) -> None:
        assert _run(
            "fn neg(@Int -> @Int) requires(true) ensures(true) "
            "effects(pure) { -@Int.0 }",
            fn="neg", args=[-3],
        ) == 3

    def test_not_true(self) -> None:
        assert _run(
            "fn f(@Bool -> @Bool) requires(true) ensures(true) "
            "effects(pure) { !@Bool.0 }",
            fn="f", args=[1],
        ) == 0

    def test_not_false(self) -> None:
        assert _run(
            "fn f(@Bool -> @Bool) requires(true) ensures(true) "
            "effects(pure) { !@Bool.0 }",
            fn="f", args=[0],
        ) == 1


# =====================================================================
# 5c: Control flow + let bindings
# =====================================================================


class TestIfExpr:
    def test_if_true(self) -> None:
        source = """\
fn f(@Bool -> @Int)
  requires(true) ensures(true) effects(pure)
{ if @Bool.0 then { 1 } else { 0 } }
"""
        assert _run(source, fn="f", args=[1]) == 1

    def test_if_false(self) -> None:
        source = """\
fn f(@Bool -> @Int)
  requires(true) ensures(true) effects(pure)
{ if @Bool.0 then { 1 } else { 0 } }
"""
        assert _run(source, fn="f", args=[0]) == 0

    def test_absolute_value(self) -> None:
        source = """\
fn absolute_value(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ if @Int.0 >= 0 then { @Int.0 } else { -@Int.0 } }
"""
        assert _run(source, fn="absolute_value", args=[5]) == 5
        assert _run(source, fn="absolute_value", args=[-5]) == 5
        assert _run(source, fn="absolute_value", args=[0]) == 0

    def test_nested_if(self) -> None:
        source = """\
fn clamp(@Int -> @Int)
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
fn is_positive(@Int -> @Bool)
  requires(true) ensures(true) effects(pure)
{ if @Int.0 > 0 then { true } else { false } }
"""
        assert _run(source, fn="is_positive", args=[5]) == 1
        assert _run(source, fn="is_positive", args=[-1]) == 0


class TestLetBindings:
    def test_simple_let(self) -> None:
        source = """\
fn f(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Int = @Int.0 + 1;
  @Int.0
}
"""
        assert _run(source, fn="f", args=[5]) == 6

    def test_multiple_lets(self) -> None:
        source = """\
fn f(@Int -> @Int)
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
fn f(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Int = @Int.0 * 2;
  @Int.0 + @Int.1
}
"""
        assert _run(source, fn="f", args=[5]) == 15  # 10 + 5

    def test_let_different_types(self) -> None:
        source = """\
fn f(@Int -> @Bool)
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
fn f(@Int -> @Int)
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
fn double(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 * 2 }

fn f(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ double(@Int.0) }
"""
        assert _run(source, fn="f", args=[5]) == 10

    def test_call_chain(self) -> None:
        source = """\
fn inc(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 + 1 }

fn double_inc(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ inc(inc(@Int.0)) }
"""
        assert _run(source, fn="double_inc", args=[5]) == 7

    def test_multiple_args(self) -> None:
        source = """\
fn add(@Int, @Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.1 + @Int.0 }

fn f(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ add(@Int.0, @Int.0) }
"""
        assert _run(source, fn="f", args=[5]) == 10


class TestRecursion:
    def test_factorial(self) -> None:
        source = """\
fn factorial(@Nat -> @Nat)
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
fn fib(@Nat -> @Nat)
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
fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{ IO.print("Hello, World!") }
"""
        assert _run_io(source, fn="main") == "Hello, World!"

    def test_empty_string(self) -> None:
        source = _IO_PRELUDE + """\
fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{ IO.print("") }
"""
        assert _run_io(source, fn="main") == ""

    def test_multiple_prints(self) -> None:
        source = _IO_PRELUDE + """\
fn main(@Unit -> @Unit)
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
fn main(@Unit -> @Unit)
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
fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{ IO.print("Hello, World! 123 @#$") }
"""
        assert _run_io(source, fn="main") == "Hello, World! 123 @#$"

    def test_io_with_pure_functions(self) -> None:
        """IO functions coexist with pure functions in the same module."""
        source = _IO_PRELUDE + """\
fn add(@Int, @Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.1 + @Int.0 }

fn main(@Unit -> @Unit)
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
fn positive(@Int -> @Int)
  requires(@Int.0 > 0)
  ensures(true)
  effects(pure)
{ @Int.0 }
"""
        assert _run(source, fn="positive", args=[5]) == 5

    def test_requires_traps(self) -> None:
        """Non-trivial precondition violated — WASM trap."""
        source = """\
fn positive(@Int -> @Int)
  requires(@Int.0 > 0)
  ensures(true)
  effects(pure)
{ @Int.0 }
"""
        _run_trap(source, fn="positive", args=[0])

    def test_requires_boundary(self) -> None:
        """Precondition with exact boundary value."""
        source = """\
fn nonneg(@Int -> @Int)
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
fn safe_div(@Int, @Int -> @Int)
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
fn f(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 }
"""
        result = _compile_ok(source)
        # No unreachable in WAT (no contract checks needed)
        assert "unreachable" not in result.wat

    def test_multiple_requires(self) -> None:
        """Multiple preconditions — all must hold."""
        source = """\
fn bounded(@Int -> @Int)
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
fn double(@Int -> @Int)
  requires(true)
  ensures(@Int.result >= 0)
  effects(pure)
{ @Int.0 * 2 }
"""
        assert _run(source, fn="double", args=[5]) == 10

    def test_ensures_traps(self) -> None:
        """Postcondition violated — WASM trap."""
        source = """\
fn negate(@Int -> @Int)
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
fn inc(@Int -> @Int)
  requires(true)
  ensures(@Int.result > @Int.0)
  effects(pure)
{ @Int.0 + 1 }
"""
        assert _run(source, fn="inc", args=[5]) == 6

    def test_ensures_result_eq(self) -> None:
        """Postcondition checking exact result value."""
        source = """\
fn always_zero(-> @Int)
  requires(true)
  ensures(@Int.result == 0)
  effects(pure)
{ 0 }
"""
        assert _run(source, fn="always_zero") == 0

    def test_ensures_result_traps(self) -> None:
        """Postcondition checking exact value — wrong result traps."""
        source = """\
fn buggy(-> @Int)
  requires(true)
  ensures(@Int.result == 0)
  effects(pure)
{ 42 }
"""
        _run_trap(source, fn="buggy")

    def test_trivial_ensures_no_overhead(self) -> None:
        """ensures(true) should not produce any trap instructions."""
        source = """\
fn f(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 }
"""
        result = _compile_ok(source)
        assert "unreachable" not in result.wat

    def test_ensures_bool_result(self) -> None:
        """Postcondition on a Bool-returning function."""
        source = """\
fn is_pos(@Int -> @Bool)
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
fn safe_inc(@Int -> @Int)
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
fn safe_inc(@Int -> @Int)
  requires(@Int.0 >= 0)
  ensures(@Int.result > @Int.0)
  effects(pure)
{ @Int.0 + 1 }
"""
        _run_trap(source, fn="safe_inc", args=[-1])

    def test_contracts_with_recursion(self) -> None:
        """Runtime contracts on a recursive function."""
        source = """\
fn factorial(@Nat -> @Nat)
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
    def test_adt_function_skipped(self) -> None:
        """Functions with ADT types produce warnings, not errors."""
        source = """\
data Option<T> { None, Some(T) }

fn make_none(-> @Option<Int>)
  requires(true) ensures(true) effects(pure)
{ None }

fn simple(-> @Int)
  requires(true) ensures(true) effects(pure)
{ 1 }
"""
        result = _compile(source)
        errors = [d for d in result.diagnostics if d.severity == "error"]
        warnings = [d for d in result.diagnostics if d.severity == "warning"]
        assert not errors
        assert len(warnings) > 0
        # The simple function should still be compiled
        assert "simple" in result.exports
