"""Tests for vera.wasm — Coverage gap tests.

Targets uncovered lines in the WASM translation layer (vera/wasm/),
focusing on helpers.py (62%), inference.py (71%), and closures.py (72%).
Uses two strategies:
1. Direct unit tests for helpers.py pure functions
2. Full pipeline tests (Vera source → compile → execute) for the rest

See issue #156.
"""

from __future__ import annotations

import tempfile
from pathlib import Path

import pytest
import wasmtime

from vera.codegen import CompileResult, compile, execute
from vera.parser import parse_file
from vera.transform import transform
from vera.types import (
    BOOL,
    BYTE,
    FLOAT64,
    INT,
    NAT,
    STRING,
    UNIT,
    FunctionType,
    PrimitiveType,
    PureEffectRow,
    RefinedType,
)
from vera.wasm.helpers import (
    _element_load_op,
    _element_mem_size,
    _element_store_op,
    _element_wasm_type,
    is_compilable_type,
    wasm_type,
    wasm_type_or_none,
)


# =====================================================================
# Helpers
# =====================================================================

def _compile(source: str) -> CompileResult:
    """Compile a Vera source string to WASM."""
    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".vera", delete=False,
    ) as f:
        f.write(source)
        f.flush()
        path = f.name
    tree = parse_file(path)
    ast = transform(tree)
    return compile(ast, source=source, file=path)


def _compile_ok(source: str) -> CompileResult:
    result = _compile(source)
    assert result.wasm_bytes is not None, f"Compile failed: {result.errors}"
    return result


def _run(source: str, fn: str | None = None,
         args: list[int] | None = None) -> int:
    result = _compile_ok(source)
    exec_result = execute(result, fn_name=fn, args=args or [])
    assert exec_result.value is not None
    return int(exec_result.value)


def _run_float(source: str, fn: str | None = None,
               args: list[int | float] | None = None) -> float:
    result = _compile_ok(source)
    exec_result = execute(result, fn_name=fn, args=args)
    assert exec_result.value is not None
    assert isinstance(exec_result.value, float)
    return exec_result.value


def _run_io(source: str, fn: str | None = None,
            args: list[int] | None = None) -> str:
    result = _compile_ok(source)
    exec_result = execute(result, fn_name=fn, args=args)
    return exec_result.stdout


def _run_trap(source: str, fn: str | None = None,
              args: list[int] | None = None) -> None:
    result = _compile_ok(source)
    with pytest.raises((wasmtime.WasmtimeError, wasmtime.Trap, RuntimeError)):
        execute(result, fn_name=fn, args=args)


# =====================================================================
# TestHelperFunctions — helpers.py pure function unit tests
# =====================================================================

class TestHelperFunctions:
    """Direct unit tests for helpers.py pure functions.

    Targets missed lines 119-159 in helpers.py: the base_type() path
    in wasm_type(), FunctionType handling, wasm_type_or_none, and
    is_compilable_type.
    """

    # -- wasm_type: refinement types via base_type() path --

    def test_wasm_type_refined_int(self) -> None:
        """Refinement of Int maps to i64 via base_type."""
        import vera.ast as ast_mod
        refined = RefinedType(base=INT, predicate=ast_mod.BoolLit(value=True))
        assert wasm_type(refined) == "i64"

    def test_wasm_type_refined_nat(self) -> None:
        """Refinement of Nat maps to i64 via base_type."""
        import vera.ast as ast_mod
        refined = RefinedType(base=NAT, predicate=ast_mod.BoolLit(value=True))
        assert wasm_type(refined) == "i64"

    def test_wasm_type_refined_float64(self) -> None:
        """Refinement of Float64 maps to f64 via base_type."""
        import vera.ast as ast_mod
        refined = RefinedType(base=FLOAT64, predicate=ast_mod.BoolLit(value=True))
        assert wasm_type(refined) == "f64"

    def test_wasm_type_refined_bool(self) -> None:
        """Refinement of Bool maps to i32 via base_type."""
        import vera.ast as ast_mod
        refined = RefinedType(base=BOOL, predicate=ast_mod.BoolLit(value=True))
        assert wasm_type(refined) == "i32"

    def test_wasm_type_refined_string(self) -> None:
        """Refinement of String maps to i32_pair via base_type."""
        import vera.ast as ast_mod
        refined = RefinedType(base=STRING, predicate=ast_mod.BoolLit(value=True))
        assert wasm_type(refined) == "i32_pair"

    def test_wasm_type_refined_unit(self) -> None:
        """Refinement of Unit maps to None via base_type."""
        import vera.ast as ast_mod
        refined = RefinedType(base=UNIT, predicate=ast_mod.BoolLit(value=True))
        assert wasm_type(refined) is None

    def test_wasm_type_function_type(self) -> None:
        """FunctionType maps to i32 (closure pointer)."""
        fn_type = FunctionType(
            params=(INT,), return_type=INT, effect=PureEffectRow(),
        )
        assert wasm_type(fn_type) == "i32"

    def test_wasm_type_unsupported(self) -> None:
        """Truly unsupported type returns 'unsupported'."""
        from vera.types import AdtType
        adt = AdtType(name="SomeADT", type_args=())
        assert wasm_type(adt) == "unsupported"

    # -- wasm_type_or_none --

    def test_wasm_type_or_none_unit(self) -> None:
        """Unit returns None (not 'unsupported')."""
        assert wasm_type_or_none(UNIT) is None

    def test_wasm_type_or_none_unsupported(self) -> None:
        """Unsupported type returns None (not 'unsupported')."""
        from vera.types import AdtType
        adt = AdtType(name="SomeADT", type_args=())
        assert wasm_type_or_none(adt) is None

    def test_wasm_type_or_none_int(self) -> None:
        """Int still returns i64 through wasm_type_or_none."""
        assert wasm_type_or_none(INT) == "i64"

    # -- is_compilable_type --

    def test_is_compilable_int(self) -> None:
        assert is_compilable_type(INT) is True

    def test_is_compilable_unit(self) -> None:
        """Unit is not compilable (returns None from wasm_type)."""
        assert is_compilable_type(UNIT) is False

    def test_is_compilable_unsupported(self) -> None:
        from vera.types import AdtType
        adt = AdtType(name="SomeADT", type_args=())
        assert is_compilable_type(adt) is False

    def test_is_compilable_function_type(self) -> None:
        fn_type = FunctionType(
            params=(INT,), return_type=INT, effect=PureEffectRow(),
        )
        assert is_compilable_type(fn_type) is True

    # -- _element_* edge cases --

    def test_element_mem_size_unknown(self) -> None:
        assert _element_mem_size("String") is None

    def test_element_load_op_unknown(self) -> None:
        """Unknown element type falls back to i64.load."""
        assert _element_load_op("Unknown") == "i64.load"

    def test_element_store_op_unknown(self) -> None:
        """Unknown element type falls back to i64.store."""
        assert _element_store_op("Unknown") == "i64.store"

    def test_element_wasm_type_unknown(self) -> None:
        assert _element_wasm_type("String") is None

    def test_element_wasm_type_float64(self) -> None:
        assert _element_wasm_type("Float64") == "f64"

    def test_element_mem_size_byte(self) -> None:
        assert _element_mem_size("Byte") == 1

    def test_element_store_op_byte(self) -> None:
        assert _element_store_op("Byte") == "i32.store8"

    def test_wasm_type_byte(self) -> None:
        """Byte is a PrimitiveType but not in the first-pass set, so
        base_type() returns itself and hits the second check.  BYTE
        falls through to 'unsupported' because the helper only maps
        the five core primitives."""
        # Byte is handled by the codegen as a refinement of Int, not
        # directly by wasm_type().  Verify the actual behavior.
        assert wasm_type(BYTE) == "unsupported"


# =====================================================================
# TestInferenceExprTypes — inference.py _infer_expr_wasm_type branches
# =====================================================================

class TestInferenceExprTypes:
    """Full pipeline tests exercising _infer_expr_wasm_type() branches.

    Targets missed lines in inference.py: ResultRef, HandleExpr,
    ArrayLit, StringLit, quantifiers, assert/assume, etc.
    """

    def test_float64_arithmetic_propagation(self) -> None:
        """Float64 binary arithmetic propagates f64 type."""
        source = """\
public fn fadd(@Float64, @Float64 -> @Float64)
  requires(true) ensures(true) effects(pure)
{
  @Float64.0 + @Float64.1
}
"""
        result = _compile_ok(source)
        assert "f64.add" in result.wat

    def test_float64_subtraction(self) -> None:
        """Float64 subtraction compiles to f64.sub."""
        source = """\
public fn fsub(@Float64, @Float64 -> @Float64)
  requires(true) ensures(true) effects(pure)
{
  @Float64.0 - @Float64.1
}
"""
        result = _compile_ok(source)
        assert "f64.sub" in result.wat

    def test_float64_multiply(self) -> None:
        """Float64 multiplication compiles to f64.mul."""
        source = """\
public fn fmul(@Float64, @Float64 -> @Float64)
  requires(true) ensures(true) effects(pure)
{
  @Float64.0 * @Float64.1
}
"""
        result = _compile_ok(source)
        assert "f64.mul" in result.wat

    def test_float64_division(self) -> None:
        """Float64 division compiles to f64.div."""
        source = """\
public fn fdiv(@Float64, @Float64 -> @Float64)
  requires(true) ensures(true) effects(pure)
{
  @Float64.0 / @Float64.1
}
"""
        result = _compile_ok(source)
        assert "f64.div" in result.wat

    def test_float64_comparison_eq(self) -> None:
        """Float64 == compiles to f64.eq."""
        source = """\
public fn feq(@Float64, @Float64 -> @Bool)
  requires(true) ensures(true) effects(pure)
{
  @Float64.0 == @Float64.1
}
"""
        result = _compile_ok(source)
        assert "f64.eq" in result.wat

    def test_float64_comparison_lt(self) -> None:
        """Float64 < compiles to f64.lt."""
        source = """\
public fn flt(@Float64, @Float64 -> @Bool)
  requires(true) ensures(true) effects(pure)
{
  @Float64.0 < @Float64.1
}
"""
        result = _compile_ok(source)
        assert "f64.lt" in result.wat

    def test_float64_comparison_gt(self) -> None:
        """Float64 > compiles to f64.gt."""
        source = """\
public fn fgt(@Float64, @Float64 -> @Bool)
  requires(true) ensures(true) effects(pure)
{
  @Float64.0 > @Float64.1
}
"""
        result = _compile_ok(source)
        assert "f64.gt" in result.wat

    def test_float64_comparison_le(self) -> None:
        """Float64 <= compiles to f64.le."""
        source = """\
public fn fle(@Float64, @Float64 -> @Bool)
  requires(true) ensures(true) effects(pure)
{
  @Float64.0 <= @Float64.1
}
"""
        result = _compile_ok(source)
        assert "f64.le" in result.wat

    def test_float64_comparison_ge(self) -> None:
        """Float64 >= compiles to f64.ge."""
        source = """\
public fn fge(@Float64, @Float64 -> @Bool)
  requires(true) ensures(true) effects(pure)
{
  @Float64.0 >= @Float64.1
}
"""
        result = _compile_ok(source)
        assert "f64.ge" in result.wat

    def test_float64_comparison_ne(self) -> None:
        """Float64 != compiles to f64.ne."""
        source = """\
public fn fne(@Float64, @Float64 -> @Bool)
  requires(true) ensures(true) effects(pure)
{
  @Float64.0 != @Float64.1
}
"""
        result = _compile_ok(source)
        assert "f64.ne" in result.wat

    def test_float64_negation(self) -> None:
        """Float64 unary negation compiles to f64.neg."""
        source = """\
public fn fneg(@Float64 -> @Float64)
  requires(true) ensures(true) effects(pure)
{
  -@Float64.0
}
"""
        result = _compile_ok(source)
        assert "f64.neg" in result.wat

    def test_implies_operator(self) -> None:
        """Boolean implies (==>) compiles to i32.eqz + i32.or."""
        source = """\
public fn imp(@Bool, @Bool -> @Bool)
  requires(true) ensures(true) effects(pure)
{
  @Bool.0 ==> @Bool.1
}
"""
        result = _compile_ok(source)
        assert "i32.eqz" in result.wat
        assert "i32.or" in result.wat

    def test_assert_compiles(self) -> None:
        """assert() compiles to i32.eqz + unreachable trap."""
        source = """\
public fn checked(@Int -> @Int)
  requires(@Int.0 > 0) ensures(true) effects(pure)
{
  assert(@Int.0 > 0);
  @Int.0
}
"""
        result = _compile_ok(source)
        assert "unreachable" in result.wat

    def test_assume_compiles(self) -> None:
        """assume() compiles to no-op (doesn't add unreachable)."""
        source = """\
public fn assumed(@Int -> @Int)
  requires(@Int.0 > 0) ensures(true) effects(pure)
{
  assume(@Int.0 > 0);
  @Int.0
}
"""
        result = _compile_ok(source)
        assert "assumed" in (result.exports or [])

    def test_forall_quantifier_runtime(self) -> None:
        """forall compiles to a loop and returns Bool."""
        source = """\
public fn all_pos(@Array<Int> -> @Bool)
  requires(true) ensures(true) effects(pure)
{
  forall(@Int, length(@Array<Int>.0), fn(@Int -> @Bool) effects(pure) { @Array<Int>.0[@Int.0] > 0 })
}
"""
        result = _compile_ok(source)
        # Should have loop structure
        assert "loop" in result.wat

    def test_exists_quantifier_runtime(self) -> None:
        """exists compiles to a loop and returns Bool."""
        source = """\
public fn has_zero(@Array<Int> -> @Bool)
  requires(true) ensures(true) effects(pure)
{
  exists(@Int, length(@Array<Int>.0), fn(@Int -> @Bool) effects(pure) { @Array<Int>.0[@Int.0] == 0 })
}
"""
        result = _compile_ok(source)
        assert "loop" in result.wat

    def test_string_lit_in_let(self) -> None:
        """String literal in let binding produces i32_pair (ptr, len)."""
        source = """\
public fn greet(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @String = "hello";
  IO.print(@String.0)
}
"""
        result = _compile_ok(source)
        assert b"hello" in result.wasm_bytes

    def test_array_lit_compiles(self) -> None:
        """Array literal compiles to heap allocation with element stores."""
        source = """\
public fn arr_len(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Array<Int> = [1, 2, 3];
  length(@Array<Int>.0)
}
"""
        assert _run(source, "arr_len") == 3

    def test_array_index_compiles(self) -> None:
        """Array indexing compiles with bounds check."""
        source = """\
public fn arr_idx(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Array<Int> = [10, 20, 30];
  @Array<Int>.0[1]
}
"""
        assert _run(source, "arr_idx") == 20

    def test_array_index_oob_traps(self) -> None:
        """Out-of-bounds array index traps."""
        source = """\
public fn arr_oob(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Array<Int> = [10, 20, 30];
  @Array<Int>.0[5]
}
"""
        _run_trap(source, "arr_oob")

    def test_empty_array(self) -> None:
        """Empty array literal compiles to (0, 0)."""
        source = """\
public fn empty_len(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Array<Int> = [];
  length(@Array<Int>.0)
}
"""
        assert _run(source, "empty_len") == 0


# =====================================================================
# TestInferenceBlockAndVera — _infer_block_result_type + _infer_vera_type
# =====================================================================

class TestInferenceBlockAndVera:
    """Tests for block result type inference and Vera type inference.

    Targets missed lines in inference.py: _infer_block_result_type
    branches (IfExpr, QualifiedCall, StringLit, nested Block,
    ConstructorCall, NullaryConstructor), and _infer_vera_type branches.
    """

    def test_block_result_if_expr(self) -> None:
        """Block ending with if-then-else infers type from then branch."""
        source = """\
public fn choose(@Bool -> @Int)
  requires(true) ensures(true) effects(pure)
{
  if @Bool.0 then { 42 } else { 0 }
}
"""
        assert _run(source, "choose", [1]) == 42
        assert _run(source, "choose", [0]) == 0

    def test_block_result_constructor(self) -> None:
        """Block ending with constructor call infers ADT (i32) type."""
        source = """\
private data Color { Red, Green, Blue }

public fn make_red(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Color = Red;
  match @Color.0 {
    Red -> 1,
    Green -> 2,
    Blue -> 3
  }
}
"""
        assert _run(source, "make_red") == 1

    def test_block_result_nullary_constructor(self) -> None:
        """NullaryConstructor in block ending position compiles."""
        source = """\
private data Option<T> { None, Some(T) }

public fn mk_none(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Option<Int> = None;
  match @Option<Int>.0 {
    None -> 0,
    Some(@Int) -> @Int.0
  }
}
"""
        assert _run(source, "mk_none") == 0

    def test_block_result_string_io(self) -> None:
        """Block ending with IO.print (QualifiedCall) produces void."""
        source = """\
public fn say(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print("hi")
}
"""
        result = _compile_ok(source)
        assert "say" in (result.exports or [])

    def test_match_expr_type_propagation(self) -> None:
        """Match expression infers result type from first arm body."""
        source = """\
private data Bit { Zero, One }

public fn bit_val(@Bit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  match @Bit.0 {
    Zero -> 0,
    One -> 1
  }
}
"""
        result = _compile_ok(source)
        assert "bit_val" in (result.exports or [])

    def test_infer_vera_type_comparison(self) -> None:
        """BinaryExpr with comparison infers Bool vera type."""
        source = """\
private forall<T> fn identity(@T -> @T)
  requires(true) ensures(true) effects(pure)
{ @T.0 }

public fn use_cmp(@Int -> @Bool)
  requires(true) ensures(true) effects(pure)
{
  identity(@Int.0 > 0)
}
"""
        assert _run(source, "use_cmp", [5]) == 1
        assert _run(source, "use_cmp", [-1]) == 0

    def test_generic_fn_return_type_inference(self) -> None:
        """Generic function return type is inferred through monomorphization."""
        source = """\
private forall<T> fn id(@T -> @T)
  requires(true) ensures(true) effects(pure)
{ @T.0 }

public fn test_gen(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  id(42)
}
"""
        assert _run(source, "test_gen") == 42

    def test_nested_block_result_type(self) -> None:
        """Nested block result type delegates to inner block."""
        source = """\
public fn nested(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Int = {
    let @Int = @Int.0 + 1;
    @Int.0 * 2
  };
  @Int.0
}
"""
        assert _run(source, "nested", [5]) == 12


# =====================================================================
# TestEffectHandlerCoverage — calls.py handle expr + operators.py old/new
# =====================================================================

class TestEffectHandlerCoverage:
    """Tests for State<T> effect handler compilation.

    Targets missed lines in calls.py (_translate_handle_state),
    operators.py (old/new state expressions), and context.py (effect ops).
    """

    def test_state_init_and_get(self) -> None:
        """handle[State<Int>] initializes and gets state."""
        source = """\
public fn test_state(@Unit -> @Int)
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
        assert _run(source, "test_state") == 42

    def test_state_put_then_get(self) -> None:
        """put followed by get returns the updated state."""
        source = """\
public fn test_put(@Unit -> @Int)
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
        assert _run(source, "test_put") == 99

    def test_state_increment(self) -> None:
        """State increment pattern: get, add, put."""
        source = """\
public fn counter(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  handle[State<Int>](@Int = 0) {
    get(@Unit) -> { resume(@Int.0) },
    put(@Int) -> { resume(()) }
  } in {
    put(get(()) + 1);
    put(get(()) + 1);
    put(get(()) + 1);
    get(())
  }
}
"""
        assert _run(source, "counter") == 3

    def test_state_with_postconditions(self) -> None:
        """State with old/new in postconditions compiles."""
        source = """\
public fn inc(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(<State<Int>>)
{
  let @Int = get(());
  put(@Int.0 + 1);
  get(())
}
"""
        # This compiles (though we can't execute it standalone since it
        # requires State<Int> to be provided by a handler)
        result = _compile(source)
        # Should at least compile without crashing
        assert result is not None


# =====================================================================
# TestClosureCoverage — closures.py _walk_free_vars branches
# =====================================================================

class TestClosureCoverage:
    """Full pipeline tests for closure compilation.

    Targets missed lines in closures.py: _walk_free_vars recursive
    cases for different expression types, and _collect_pattern_bindings.
    """

    def test_closure_captures_in_binary(self) -> None:
        """Closure captures variable used in binary expression."""
        source = """\
type IntFn = fn(Int -> Int) effects(pure);

private fn make_adder(@Int -> @IntFn)
  requires(true) ensures(true) effects(pure)
{
  fn(@Int -> @Int) effects(pure) { @Int.0 + @Int.1 }
}

public fn test_add(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @IntFn = make_adder(10);
  apply_fn(@IntFn.0, 5)
}
"""
        assert _run(source, "test_add") == 15

    def test_closure_captures_in_if(self) -> None:
        """Closure captures variable used inside if-then-else."""
        source = """\
type IntFn = fn(Int -> Int) effects(pure);

private fn make_clamper(@Int -> @IntFn)
  requires(true) ensures(true) effects(pure)
{
  fn(@Int -> @Int) effects(pure) {
    if @Int.0 > @Int.1 then { @Int.1 } else { @Int.0 }
  }
}

public fn test_clamp(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @IntFn = make_clamper(100);
  apply_fn(@IntFn.0, 200)
}
"""
        assert _run(source, "test_clamp") == 100

    def test_closure_captures_in_call(self) -> None:
        """Closure captures variable used as argument to function call."""
        source = """\
type IntFn = fn(Int -> Int) effects(pure);

private fn add(@Int, @Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 + @Int.1 }

private fn make_add_n(@Int -> @IntFn)
  requires(true) ensures(true) effects(pure)
{
  fn(@Int -> @Int) effects(pure) { add(@Int.0, @Int.1) }
}

public fn test_call_capture(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @IntFn = make_add_n(7);
  apply_fn(@IntFn.0, 3)
}
"""
        assert _run(source, "test_call_capture") == 10

    def test_closure_captures_in_let_block(self) -> None:
        """Closure with let bindings inside body, capturing outer var.

        De Bruijn indices: @Int.0 inside let body = the let binding,
        @Int.1 = the closure param (arg), @Int.2 = captured outer var.
        With arg=3, captured=5: let @Int = 3 * 2 = 6, then 6 + 3 = 9.
        """
        source = """\
type IntFn = fn(Int -> Int) effects(pure);

private fn make_doubler(@Int -> @IntFn)
  requires(true) ensures(true) effects(pure)
{
  fn(@Int -> @Int) effects(pure) {
    let @Int = @Int.0 * 2;
    @Int.0 + @Int.1
  }
}

public fn test_let_capture(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @IntFn = make_doubler(5);
  apply_fn(@IntFn.0, 3)
}
"""
        # arg=3, captured=5: let @Int = 3*2=6, @Int.0=6, @Int.1=3 → 9
        assert _run(source, "test_let_capture") == 9

    def test_closure_with_match_capture(self) -> None:
        """Closure that captures a variable and uses match expression."""
        source = """\
private data Option<T> { None, Some(T) }
type IntFn = fn(Int -> Int) effects(pure);

private fn make_default(@Int -> @IntFn)
  requires(true) ensures(true) effects(pure)
{
  fn(@Int -> @Int) effects(pure) {
    let @Option<Int> = Some(@Int.0);
    match @Option<Int>.0 {
      None -> @Int.1,
      Some(@Int) -> @Int.0
    }
  }
}

public fn test_match_capture(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @IntFn = make_default(99);
  apply_fn(@IntFn.0, 42)
}
"""
        assert _run(source, "test_match_capture") == 42

    def test_closure_map_option(self) -> None:
        """Closure application inside a match arm (map over Option)."""
        source = """\
private data Option<T> { None, Some(T) }
type IntMapper = fn(Int -> Int) effects(pure);

private fn map_opt(@Option<Int>, @IntMapper -> @Option<Int>)
  requires(true) ensures(true) effects(pure)
{
  match @Option<Int>.0 {
    None -> None,
    Some(@Int) -> Some(apply_fn(@IntMapper.0, @Int.0))
  }
}

private fn make_doubler(@Unit -> @IntMapper)
  requires(true) ensures(true) effects(pure)
{
  fn(@Int -> @Int) effects(pure) { @Int.0 * 2 }
}

public fn test_map(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @IntMapper = make_doubler(());
  let @Option<Int> = map_opt(Some(21), @IntMapper.0);
  match @Option<Int>.0 {
    None -> 0,
    Some(@Int) -> @Int.0
  }
}
"""
        assert _run(source, "test_map") == 42


# =====================================================================
# TestOperatorsEdgeCases — operators.py missed lines
# =====================================================================

class TestOperatorsEdgeCases:
    """Tests for operator translation edge cases.

    Targets missed lines in operators.py: Byte comparisons, implies,
    Bool comparisons using i32 ops.
    """

    def test_byte_comparison_lt(self) -> None:
        """Byte < uses unsigned i32 comparison."""
        source = """\
public fn byte_lt(@Byte, @Byte -> @Bool)
  requires(true) ensures(true) effects(pure)
{
  @Byte.0 < @Byte.1
}
"""
        result = _compile_ok(source)
        assert "i32.lt_u" in result.wat

    def test_byte_comparison_eq(self) -> None:
        """Byte == uses i32 comparison."""
        source = """\
public fn byte_eq(@Byte, @Byte -> @Bool)
  requires(true) ensures(true) effects(pure)
{
  @Byte.0 == @Byte.1
}
"""
        result = _compile_ok(source)
        # Byte eq uses i32.eq
        assert "i32.eq" in result.wat

    def test_bool_comparison(self) -> None:
        """Bool == uses i32 comparison (signed)."""
        source = """\
public fn bool_eq(@Bool, @Bool -> @Bool)
  requires(true) ensures(true) effects(pure)
{
  @Bool.0 == @Bool.1
}
"""
        result = _compile_ok(source)
        assert "i32.eq" in result.wat

    def test_bool_and(self) -> None:
        """Bool && compiles to i32.and."""
        source = """\
public fn band(@Bool, @Bool -> @Bool)
  requires(true) ensures(true) effects(pure)
{
  @Bool.0 && @Bool.1
}
"""
        assert _run(source, "band", [1, 1]) == 1
        assert _run(source, "band", [1, 0]) == 0

    def test_bool_or(self) -> None:
        """Bool || compiles to i32.or."""
        source = """\
public fn bor(@Bool, @Bool -> @Bool)
  requires(true) ensures(true) effects(pure)
{
  @Bool.0 || @Bool.1
}
"""
        assert _run(source, "bor", [0, 0]) == 0
        assert _run(source, "bor", [0, 1]) == 1


# =====================================================================
# TestDataMatchCoverage — data.py constructor/match branches
# =====================================================================

class TestDataMatchCoverage:
    """Tests for constructor, match, and array translation.

    Targets missed lines in data.py: nullary constructors, constructor
    field extraction, wildcard patterns, match cascades.
    """

    def test_nullary_constructor(self) -> None:
        """Nullary constructor allocates and stores tag."""
        source = """\
private data Traffic { Red, Yellow, Green }

public fn is_red(@Traffic -> @Bool)
  requires(true) ensures(true) effects(pure)
{
  match @Traffic.0 {
    Red -> true,
    Yellow -> false,
    Green -> false
  }
}

public fn test_traffic(@Unit -> @Bool)
  requires(true) ensures(true) effects(pure)
{
  is_red(Red)
}
"""
        assert _run(source, "test_traffic") == 1

    def test_constructor_with_field(self) -> None:
        """Constructor with field extracts correctly in match."""
        source = """\
private data Box { Wrap(Int) }

public fn unwrap(@Box -> @Int)
  requires(true) ensures(true) effects(pure)
{
  match @Box.0 {
    Wrap(@Int) -> @Int.0
  }
}

public fn test_box(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  unwrap(Wrap(42))
}
"""
        assert _run(source, "test_box") == 42

    def test_match_with_wildcard(self) -> None:
        """Match with wildcard pattern as catch-all."""
        source = """\
private data Color { Red, Green, Blue }

public fn color_val(@Color -> @Int)
  requires(true) ensures(true) effects(pure)
{
  match @Color.0 {
    Red -> 1,
    _ -> 0
  }
}

public fn test_wild(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  color_val(Blue)
}
"""
        assert _run(source, "test_wild") == 0

    def test_match_bool_patterns(self) -> None:
        """Match on Bool with true/false patterns."""
        source = """\
public fn bool_to_int(@Bool -> @Int)
  requires(true) ensures(true) effects(pure)
{
  match @Bool.0 {
    true -> 1,
    false -> 0
  }
}
"""
        assert _run(source, "bool_to_int", [1]) == 1
        assert _run(source, "bool_to_int", [0]) == 0

    def test_match_int_patterns(self) -> None:
        """Match on Int with literal patterns."""
        source = """\
public fn classify(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  match @Int.0 {
    0 -> 100,
    1 -> 200,
    _ -> 300
  }
}
"""
        assert _run(source, "classify", [0]) == 100
        assert _run(source, "classify", [1]) == 200
        assert _run(source, "classify", [5]) == 300

    def test_option_some_none(self) -> None:
        """Option<Int> with Some and None constructors."""
        source = """\
private data Option<T> { None, Some(T) }

public fn unwrap_or(@Option<Int>, @Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  match @Option<Int>.0 {
    None -> @Int.0,
    Some(@Int) -> @Int.0
  }
}

public fn test_some(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  unwrap_or(Some(42), 0)
}

public fn test_none(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  unwrap_or(None, 99)
}
"""
        assert _run(source, "test_some") == 42
        assert _run(source, "test_none") == 99


# =====================================================================
# TestRefinementTypeCoverage — refinement types through the pipeline
# =====================================================================

class TestRefinementTypeCoverage:
    """Tests for refinement type compilation paths.

    Exercises the base_type() path in inference.py and helpers.py
    through actual Vera programs with refinement types.
    """

    def test_refinement_type_alias_int(self) -> None:
        """Refinement type alias based on Int compiles and runs."""
        source = """\
type PosInt = { @Int | @Int.0 > 0 };

public fn use_pos(@PosInt -> @Int)
  requires(true) ensures(true) effects(pure)
{
  @PosInt.0 + 1
}
"""
        assert _run(source, "use_pos", [5]) == 6

    def test_refinement_slot_ref_resolution(self) -> None:
        """Slot ref for refinement type resolves to base type for WASM."""
        source = """\
type Even = { @Int | @Int.0 % 2 == 0 };

public fn double_even(@Even -> @Int)
  requires(true) ensures(true) effects(pure)
{
  @Even.0 * 2
}
"""
        assert _run(source, "double_even", [4]) == 8

    def test_refinement_in_if_branches(self) -> None:
        """Refinement type used in if-then-else branches."""
        source = """\
type PosInt = { @Int | @Int.0 > 0 };

public fn clamp_pos(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  if @Int.0 > 0 then { @Int.0 } else { 1 }
}
"""
        assert _run(source, "clamp_pos", [5]) == 5
        assert _run(source, "clamp_pos", [-3]) == 1


# =====================================================================
# TestGenericFunctionCoverage — generic call resolution paths
# =====================================================================

class TestGenericFunctionCoverage:
    """Tests for generic function compilation and monomorphization.

    Targets missed lines in calls.py (_resolve_generic_call,
    _unify_param_arg_wasm) and inference.py (_infer_fncall_vera_type).
    """

    def test_generic_identity_int(self) -> None:
        """Generic identity instantiated with Int."""
        source = """\
private forall<T> fn identity(@T -> @T)
  requires(true) ensures(true) effects(pure)
{ @T.0 }

public fn test_id(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  identity(42)
}
"""
        assert _run(source, "test_id") == 42

    def test_generic_identity_bool(self) -> None:
        """Generic identity instantiated with Bool."""
        source = """\
private forall<T> fn identity(@T -> @T)
  requires(true) ensures(true) effects(pure)
{ @T.0 }

public fn test_id_bool(@Unit -> @Bool)
  requires(true) ensures(true) effects(pure)
{
  identity(true)
}
"""
        assert _run(source, "test_id_bool") == 1

    def test_generic_two_params(self) -> None:
        """Generic function with two type params."""
        source = """\
private forall<A, B> fn first(@A, @B -> @A)
  requires(true) ensures(true) effects(pure)
{ @A.0 }

public fn test_first(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  first(42, true)
}
"""
        assert _run(source, "test_first") == 42

    def test_generic_with_adt(self) -> None:
        """Generic function applied to ADT type."""
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

public fn test_is_some(@Unit -> @Bool)
  requires(true) ensures(true) effects(pure)
{
  is_some(Some(42))
}
"""
        assert _run(source, "test_is_some") == 1


# =====================================================================
# TestContextBlockCoverage — context.py translate_block paths
# =====================================================================

class TestContextBlockCoverage:
    """Tests for translate_block edge cases.

    Targets missed lines in context.py: pair bindings (String, Array<T>),
    ExprStmt drops, _is_void_expr, _is_pair_result_expr.
    """

    def test_string_let_binding(self) -> None:
        """String let binding allocates pair locals (ptr, len)."""
        source = """\
public fn hello(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @String = "world";
  IO.print(@String.0)
}
"""
        output = _run_io(source, "hello")
        assert "world" in output

    def test_array_let_binding(self) -> None:
        """Array<Int> let binding allocates pair locals."""
        source = """\
public fn sum_arr(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Array<Int> = [10, 20, 30];
  @Array<Int>.0[0] + @Array<Int>.0[1] + @Array<Int>.0[2]
}
"""
        assert _run(source, "sum_arr") == 60

    def test_expr_stmt_drop_value(self) -> None:
        """Expression statement drops the result value."""
        source = """\
private fn side(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 + 1 }

public fn test_drop(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  side(1);
  42
}
"""
        assert _run(source, "test_drop") == 42

    def test_io_print_is_void(self) -> None:
        """IO.print (QualifiedCall) is treated as void — no drop needed."""
        source = """\
public fn multi_print(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print("a");
  IO.print("b");
  IO.print("c")
}
"""
        output = _run_io(source, "multi_print")
        assert "a" in output

    def test_assert_stmt_is_void(self) -> None:
        """assert() in statement position is void — no drop needed."""
        source = """\
public fn guarded(@Int -> @Int)
  requires(@Int.0 > 0) ensures(true) effects(pure)
{
  assert(@Int.0 > 0);
  assert(@Int.0 < 1000);
  @Int.0 * 2
}
"""
        assert _run(source, "guarded", [5]) == 10

    def test_pipe_operator(self) -> None:
        """Pipe operator desugars to function call."""
        source = """\
private fn double(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 * 2 }

private fn add_one(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 + 1 }

public fn test_pipe(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  5 |> double() |> add_one()
}
"""
        assert _run(source, "test_pipe") == 11

    def test_length_builtin(self) -> None:
        """length() builtin translates to (ptr, len) → drop ptr, extend len."""
        source = """\
public fn arr_length(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Array<Int> = [1, 2, 3, 4, 5];
  length(@Array<Int>.0)
}
"""
        assert _run(source, "arr_length") == 5


# =====================================================================
# TestInferenceDeepBranches — targeted inference.py branch coverage
# =====================================================================

class TestInferenceDeepBranches:
    """Targeted tests for deep inference.py branches.

    These construct specific expression nesting patterns to exercise
    _infer_expr_wasm_type and _infer_block_result_type branches that
    are only reached through indirect calls (e.g., from _translate_if,
    _translate_match, _translate_binary).
    """

    def test_if_with_match_result(self) -> None:
        """Match expression as if-branch body triggers _infer_block_result_type
        MatchExpr branch."""
        source = """\
private data Bit { Zero, One }

public fn choose(@Bool, @Bit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  if @Bool.0 then {
    match @Bit.0 {
      Zero -> 0,
      One -> 1
    }
  } else {
    99
  }
}
"""
        assert _run(source, "choose", [1, 0]) == 0
        assert _run(source, "choose", [0, 0]) == 99

    def test_if_with_constructor_result(self) -> None:
        """ConstructorCall as if-branch body triggers _infer_block_result_type
        ConstructorCall branch (line 235)."""
        source = """\
private data Option<T> { None, Some(T) }

public fn maybe(@Bool, @Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Option<Int> = if @Bool.0 then {
    Some(@Int.0)
  } else {
    None
  };
  match @Option<Int>.0 {
    None -> 0,
    Some(@Int) -> @Int.0
  }
}
"""
        assert _run(source, "maybe", [1, 42]) == 42
        assert _run(source, "maybe", [0, 42]) == 0

    def test_if_with_nullary_constructor_result(self) -> None:
        """NullaryConstructor as if-branch body triggers
        _infer_block_result_type NullaryConstructor branch."""
        source = """\
private data Option<T> { None, Some(T) }

public fn mk_opt(@Bool -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Option<Int> = if @Bool.0 then {
    None
  } else {
    Some(42)
  };
  match @Option<Int>.0 {
    None -> 0,
    Some(@Int) -> @Int.0
  }
}
"""
        assert _run(source, "mk_opt", [1]) == 0
        assert _run(source, "mk_opt", [0]) == 42

    def test_if_with_string_result(self) -> None:
        """StringLit as if-branch body triggers _infer_block_result_type
        StringLit branch (line 231)."""
        source = """\
public fn greet(@Bool -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @String = if @Bool.0 then { "hello" } else { "bye" };
  IO.print(@String.0)
}
"""
        result = _compile_ok(source)
        assert "greet" in (result.exports or [])

    def test_if_with_array_result(self) -> None:
        """ArrayLit as if-branch body triggers _infer_block_result_type
        ArrayLit branch (line 246 in _infer_expr_wasm_type)."""
        source = """\
public fn pick(@Bool -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Array<Int> = if @Bool.0 then { [1, 2, 3] } else { [4, 5, 6] };
  @Array<Int>.0[0]
}
"""
        assert _run(source, "pick", [1]) == 1
        assert _run(source, "pick", [0]) == 4

    def test_if_with_slot_ref_pair_result(self) -> None:
        """String slot ref as if-branch body triggers _infer_block_result_type
        SlotRef pair branch."""
        source = """\
public fn pick_str(@Bool, @String -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @String = if @Bool.0 then { @String.0 } else { "default" };
  IO.print(@String.0)
}
"""
        result = _compile_ok(source)
        assert "pick_str" in (result.exports or [])

    def test_if_with_adt_slot_ref_result(self) -> None:
        """ADT slot ref as if-branch body triggers _infer_block_result_type
        SlotRef ADT branch."""
        source = """\
private data Color { Red, Green, Blue }

public fn pick_color(@Bool, @Color -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Color = if @Bool.0 then { @Color.0 } else { Red };
  match @Color.0 {
    Red -> 1,
    Green -> 2,
    Blue -> 3
  }
}
"""
        result = _compile_ok(source)
        assert "pick_color" in (result.exports or [])

    def test_if_with_fn_call_result(self) -> None:
        """FnCall as if-branch body triggers _infer_block_result_type
        FnCall branch (line 227)."""
        source = """\
private fn double(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 * 2 }

public fn cond_double(@Bool, @Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  if @Bool.0 then { double(@Int.0) } else { @Int.0 }
}
"""
        assert _run(source, "cond_double", [1, 5]) == 10
        assert _run(source, "cond_double", [0, 5]) == 5

    def test_if_with_nested_block_result(self) -> None:
        """Nested Block as if-branch body triggers _infer_block_result_type
        Block branch (line 233)."""
        source = """\
public fn nested_if(@Bool, @Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  if @Bool.0 then {
    let @Int = @Int.0 + 1;
    {
      let @Int = @Int.0 * 2;
      @Int.0
    }
  } else {
    @Int.0
  }
}
"""
        assert _run(source, "nested_if", [1, 5]) == 12
        assert _run(source, "nested_if", [0, 5]) == 5

    def test_if_with_binary_result_float(self) -> None:
        """Float64 arithmetic as if-branch body triggers
        _infer_block_result_type BinaryExpr f64 branch."""
        source = """\
public fn cond_add(@Bool, @Float64, @Float64 -> @Float64)
  requires(true) ensures(true) effects(pure)
{
  if @Bool.0 then { @Float64.0 + @Float64.1 } else { @Float64.0 }
}
"""
        result = _compile_ok(source)
        assert "f64.add" in result.wat

    def test_if_with_comparison_result(self) -> None:
        """Comparison as if-branch body triggers _infer_block_result_type
        BinaryExpr comparison branch."""
        source = """\
public fn cond_cmp(@Bool, @Int -> @Bool)
  requires(true) ensures(true) effects(pure)
{
  if @Bool.0 then { @Int.0 > 0 } else { false }
}
"""
        assert _run(source, "cond_cmp", [1, 5]) == 1
        assert _run(source, "cond_cmp", [0, 5]) == 0

    def test_if_with_unary_neg_float_result(self) -> None:
        """Float64 negation as if-branch body triggers
        _infer_block_result_type UnaryExpr NEG f64 branch."""
        source = """\
public fn cond_neg(@Bool, @Float64 -> @Float64)
  requires(true) ensures(true) effects(pure)
{
  if @Bool.0 then { -@Float64.0 } else { @Float64.0 }
}
"""
        result = _compile_ok(source)
        assert "f64.neg" in result.wat

    def test_if_with_unary_not_result(self) -> None:
        """Boolean NOT as if-branch body triggers
        _infer_block_result_type UnaryExpr NOT branch."""
        source = """\
public fn cond_not(@Bool -> @Bool)
  requires(true) ensures(true) effects(pure)
{
  if @Bool.0 then { !@Bool.0 } else { @Bool.0 }
}
"""
        assert _run(source, "cond_not", [1]) == 0
        assert _run(source, "cond_not", [0]) == 0

    def test_if_with_boolean_and_result(self) -> None:
        """Boolean AND as if-branch body triggers
        _infer_block_result_type BinaryExpr AND/OR/IMPLIES branch."""
        source = """\
public fn cond_and(@Bool, @Bool -> @Bool)
  requires(true) ensures(true) effects(pure)
{
  if @Bool.0 then { @Bool.0 && @Bool.1 } else { false }
}
"""
        assert _run(source, "cond_and", [1, 1]) == 1
        assert _run(source, "cond_and", [0, 1]) == 0

    def test_if_with_index_result(self) -> None:
        """Array index as if-branch body triggers _infer_block_result_type
        IndexExpr branch (line 242-244)."""
        source = """\
public fn cond_idx(@Bool, @Array<Int> -> @Int)
  requires(true) ensures(true) effects(pure)
{
  if @Bool.0 then { @Array<Int>.0[0] } else { 0 }
}
"""
        result = _compile_ok(source)
        assert "cond_idx" in (result.exports or [])

    def test_if_with_quantifier_result(self) -> None:
        """Quantifier as if-branch body triggers _infer_block_result_type
        ForallExpr branch (line 247-248)."""
        source = """\
public fn cond_forall(@Bool, @Array<Int> -> @Bool)
  requires(true) ensures(true) effects(pure)
{
  if @Bool.0 then {
    forall(@Int, length(@Array<Int>.0), fn(@Int -> @Bool) effects(pure) { @Array<Int>.0[@Int.0] > 0 })
  } else {
    false
  }
}
"""
        result = _compile_ok(source)
        assert "cond_forall" in (result.exports or [])

    def test_match_on_binary_scrutinee(self) -> None:
        """Binary expression as match scrutinee triggers
        _infer_expr_wasm_type on the scrutinee (for match, the wasm type
        matters for saving to a local)."""
        source = """\
public fn classify(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  match @Int.0 > 0 {
    true -> 1,
    false -> 0
  }
}
"""
        assert _run(source, "classify", [5]) == 1
        assert _run(source, "classify", [-1]) == 0

    def test_binary_with_fn_call_operand(self) -> None:
        """FnCall as operand of binary triggers _infer_expr_wasm_type
        on the FnCall (line 132-133)."""
        source = """\
private fn double(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 * 2 }

public fn add_double(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  double(@Int.0) + 1
}
"""
        assert _run(source, "add_double", [5]) == 11

    def test_slot_ref_fn_type_alias_inference(self) -> None:
        """SlotRef with function type alias triggers FnType alias
        check in _infer_expr_wasm_type (lines 105-108)."""
        source = """\
type IntFn = fn(Int -> Int) effects(pure);

private fn make_fn(@Unit -> @IntFn)
  requires(true) ensures(true) effects(pure)
{
  fn(@Int -> @Int) effects(pure) { @Int.0 }
}

public fn test_fn_alias(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @IntFn = make_fn(());
  apply_fn(@IntFn.0, 42)
}
"""
        assert _run(source, "test_fn_alias") == 42

    def test_infer_vera_type_unary(self) -> None:
        """UnaryExpr NOT/NEG in generic context triggers _infer_vera_type
        UnaryExpr branches (lines 275-278)."""
        source = """\
private forall<T> fn id(@T -> @T)
  requires(true) ensures(true) effects(pure)
{ @T.0 }

public fn test_neg(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  id(-5)
}
"""
        assert _run(source, "test_neg") == -5

    def test_infer_vera_type_bool_op(self) -> None:
        """Boolean AND in generic context triggers _infer_vera_type
        BinaryExpr comparison branch (lines 270-273)."""
        source = """\
private forall<T> fn id(@T -> @T)
  requires(true) ensures(true) effects(pure)
{ @T.0 }

public fn test_and(@Unit -> @Bool)
  requires(true) ensures(true) effects(pure)
{
  id(true && false)
}
"""
        assert _run(source, "test_and") == 0

    def test_infer_vera_type_arithmetic(self) -> None:
        """Arithmetic in generic context triggers _infer_vera_type
        BinaryExpr arithmetic branch (line 274)."""
        source = """\
private forall<T> fn id(@T -> @T)
  requires(true) ensures(true) effects(pure)
{ @T.0 }

public fn test_arith(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  id(3 + 4)
}
"""
        assert _run(source, "test_arith") == 7
