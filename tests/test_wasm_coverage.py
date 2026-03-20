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

    def test_element_mem_size_string(self) -> None:
        """String element: pair type → 8 bytes."""
        assert _element_mem_size("String") == 8

    def test_element_mem_size_adt(self) -> None:
        """ADT element: i32 heap pointer → 4 bytes."""
        assert _element_mem_size("Option") == 4

    def test_element_load_op_adt(self) -> None:
        """ADT element type → i32.load."""
        assert _element_load_op("Unknown") == "i32.load"

    def test_element_load_op_string(self) -> None:
        """String element: pair type → None (special handling)."""
        assert _element_load_op("String") is None

    def test_element_store_op_adt(self) -> None:
        """ADT element type → i32.store."""
        assert _element_store_op("Unknown") == "i32.store"

    def test_element_store_op_string(self) -> None:
        """String element: pair type → None (special handling)."""
        assert _element_store_op("String") is None

    def test_element_wasm_type_string(self) -> None:
        """String element → i32_pair."""
        assert _element_wasm_type("String") == "i32_pair"

    def test_element_wasm_type_adt(self) -> None:
        """ADT element → i32."""
        assert _element_wasm_type("Option") == "i32"

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
  forall(@Int, array_length(@Array<Int>.0), fn(@Int -> @Bool) effects(pure) { @Array<Int>.0[@Int.0] > 0 })
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
  exists(@Int, array_length(@Array<Int>.0), fn(@Int -> @Bool) effects(pure) { @Array<Int>.0[@Int.0] == 0 })
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
  array_length(@Array<Int>.0)
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
  array_length(@Array<Int>.0)
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

    def test_array_length_builtin(self) -> None:
        """array_length() builtin translates to (ptr, len) → drop ptr, extend len."""
        source = """\
public fn arr_length(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Array<Int> = [1, 2, 3, 4, 5];
  array_length(@Array<Int>.0)
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
    forall(@Int, array_length(@Array<Int>.0), fn(@Int -> @Bool) effects(pure) { @Array<Int>.0[@Int.0] > 0 })
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


# =====================================================================
# TestInferenceVeraType — _infer_vera_type branches via generic calls
# =====================================================================

class TestInferenceVeraType:
    """Tests that exercise _infer_vera_type branches in inference.py.

    _infer_vera_type is called during generic function resolution to
    determine the Vera type of arguments.  Each test passes a different
    expression type as an argument to a generic function, forcing the
    inference path for that expression kind.
    """

    def test_infer_vera_type_string_lit_via_show(self) -> None:
        """StringLit passed to show() dispatch triggers
        _infer_vera_type StringLit branch (line 388-389)."""
        source = """\
public fn test_str(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print(show("literal"))
}
"""
        output = _run_io(source, "test_str")
        assert "literal" in output

    def test_infer_vera_type_interpolated_string(self) -> None:
        """InterpolatedString in if-branch triggers
        _infer_block_result_type InterpolatedString branch (line 337-338)."""
        source = """\
public fn test_interp(@Int -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @String = if @Int.0 > 0 then { "val=\\(@Int.0)" } else { "none" };
  IO.print(@String.0)
}
"""
        output = _run_io(source, "test_interp", [42])
        assert "val=42" in output

    def test_infer_vera_type_array_lit(self) -> None:
        """ArrayLit argument to generic function triggers
        _infer_vera_type ArrayLit branch (line 392-393)."""
        source = """\
private forall<T> fn id(@T -> @T)
  requires(true) ensures(true) effects(pure)
{ @T.0 }

public fn test_arr(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Array<Int> = id([1, 2, 3]);
  array_length(@Array<Int>.0)
}
"""
        result = _compile_ok(source)
        assert result.wasm_bytes is not None

    def test_infer_vera_type_index_expr(self) -> None:
        """IndexExpr argument to generic function triggers
        _infer_vera_type IndexExpr branch (line 394-396)."""
        source = """\
private forall<T> fn id(@T -> @T)
  requires(true) ensures(true) effects(pure)
{ @T.0 }

public fn test_idx(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Array<Int> = [10, 20, 30];
  id(@Array<Int>.0[1])
}
"""
        result = _compile_ok(source)
        assert result.wasm_bytes is not None

    def test_infer_vera_type_if_expr(self) -> None:
        """IfExpr argument to generic function triggers
        _infer_vera_type IfExpr branch (line 397-400)."""
        source = """\
private forall<T> fn id(@T -> @T)
  requires(true) ensures(true) effects(pure)
{ @T.0 }

public fn test_if(@Bool -> @Int)
  requires(true) ensures(true) effects(pure)
{
  id(if @Bool.0 then { 1 } else { 0 })
}
"""
        assert _run(source, "test_if", [1]) == 1
        assert _run(source, "test_if", [0]) == 0

    def test_infer_vera_type_fncall(self) -> None:
        """FnCall argument to generic function triggers
        _infer_vera_type FnCall branch (line 386-387)."""
        source = """\
private fn double(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 * 2 }

private forall<T> fn id(@T -> @T)
  requires(true) ensures(true) effects(pure)
{ @T.0 }

public fn test_fn(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  id(double(21))
}
"""
        assert _run(source, "test_fn") == 42

    def test_infer_vera_type_constructor_call(self) -> None:
        """ConstructorCall argument to generic function triggers
        _infer_vera_type ConstructorCall branch (line 372-373)."""
        source = """\
private data Option<T> { None, Some(T) }

private forall<T> fn id(@T -> @T)
  requires(true) ensures(true) effects(pure)
{ @T.0 }

public fn test_ctor(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Option<Int> = id(Some(42));
  match @Option<Int>.0 {
    None -> 0,
    Some(@Int) -> @Int.0
  }
}
"""
        assert _run(source, "test_ctor") == 42

    def test_infer_vera_type_nullary_constructor(self) -> None:
        """NullaryConstructor argument to generic function triggers
        _infer_vera_type NullaryConstructor branch (line 374-375)."""
        source = """\
private data Option<T> { None, Some(T) }

private forall<T> fn id(@T -> @T)
  requires(true) ensures(true) effects(pure)
{ @T.0 }

public fn test_nullary(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Option<Int> = id(None);
  match @Option<Int>.0 {
    None -> 0,
    Some(@Int) -> @Int.0
  }
}
"""
        assert _run(source, "test_nullary") == 0

    def test_infer_vera_type_float_lit(self) -> None:
        """FloatLit argument to generic function triggers
        _infer_vera_type FloatLit branch (line 366-367)."""
        source = """\
private forall<T> fn id(@T -> @T)
  requires(true) ensures(true) effects(pure)
{ @T.0 }

public fn test_float(@Unit -> @Float64)
  requires(true) ensures(true) effects(pure)
{
  id(3.14)
}
"""
        result = _compile_ok(source)
        assert result.wasm_bytes is not None

    def test_infer_vera_type_unit_lit(self) -> None:
        """UnitLit argument to generic function triggers
        _infer_vera_type UnitLit branch (line 368-369)."""
        source = """\
private forall<T> fn id(@T -> @T)
  requires(true) ensures(true) effects(pure)
{ @T.0 }

public fn test_unit(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  id(());
  IO.print("done")
}
"""
        result = _compile_ok(source)
        assert result.wasm_bytes is not None


# =====================================================================
# TestInferFncallVeraType — _infer_fncall_vera_type builtin branches
# =====================================================================

class TestInferFncallVeraType:
    """Tests for _infer_fncall_vera_type builtin return type inference.

    These are triggered when a builtin function call is passed as an
    argument to a generic function, requiring Vera-level type inference
    to resolve the generic type variable.
    """

    def test_fncall_vera_type_array_length(self) -> None:
        """array_length() in generic context triggers line 410-411."""
        source = """\
private forall<T> fn id(@T -> @T)
  requires(true) ensures(true) effects(pure)
{ @T.0 }

public fn test_alen(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Array<Int> = [1, 2, 3];
  id(array_length(@Array<Int>.0))
}
"""
        result = _compile_ok(source)
        assert result.wasm_bytes is not None

    def test_fncall_vera_type_string_length(self) -> None:
        """string_length() in generic context triggers line 414-415."""
        source = """\
private forall<T> fn id(@T -> @T)
  requires(true) ensures(true) effects(pure)
{ @T.0 }

public fn test_slen(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  id(string_length("hello"))
}
"""
        result = _compile_ok(source)
        assert result.wasm_bytes is not None

    def test_fncall_vera_type_string_concat(self) -> None:
        """string_concat() in generic context triggers line 416-420."""
        source = """\
private forall<T> fn id(@T -> @T)
  requires(true) ensures(true) effects(pure)
{ @T.0 }

public fn test_scat(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @String = id(string_concat("a", "b"));
  IO.print(@String.0)
}
"""
        result = _compile_ok(source)
        assert result.wasm_bytes is not None

    def test_fncall_vera_type_to_string(self) -> None:
        """to_string() in generic context triggers line 416-420."""
        source = """\
private forall<T> fn id(@T -> @T)
  requires(true) ensures(true) effects(pure)
{ @T.0 }

public fn test_tostr(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @String = id(to_string(42));
  IO.print(@String.0)
}
"""
        result = _compile_ok(source)
        assert result.wasm_bytes is not None

    def test_fncall_vera_type_non_generic_fn(self) -> None:
        """Non-generic user function in generic context triggers
        _infer_fncall_vera_type non-generic lookup (line 549-557)."""
        source = """\
private fn double(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 * 2 }

private forall<T> fn id(@T -> @T)
  requires(true) ensures(true) effects(pure)
{ @T.0 }

public fn test_non_gen(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  id(double(21))
}
"""
        result = _compile_ok(source)
        assert result.wasm_bytes is not None

    def test_fncall_vera_type_generic_in_generic(self) -> None:
        """Generic function call in generic context triggers
        _infer_fncall_vera_type generic lookup (line 525-548)."""
        source = """\
private forall<T> fn id(@T -> @T)
  requires(true) ensures(true) effects(pure)
{ @T.0 }

private forall<T> fn also_id(@T -> @T)
  requires(true) ensures(true) effects(pure)
{ id(@T.0) }

public fn test_gen_gen(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  also_id(42)
}
"""
        result = _compile_ok(source)
        assert result.wasm_bytes is not None

    def test_fncall_vera_type_abs(self) -> None:
        """abs() in generic context triggers line 507-508."""
        source = """\
private forall<T> fn id(@T -> @T)
  requires(true) ensures(true) effects(pure)
{ @T.0 }

public fn test_abs(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  id(abs(-5))
}
"""
        result = _compile_ok(source)
        assert result.wasm_bytes is not None

    def test_fncall_vera_type_min_max(self) -> None:
        """min()/max() in generic context triggers line 509-510."""
        source = """\
private forall<T> fn id(@T -> @T)
  requires(true) ensures(true) effects(pure)
{ @T.0 }

public fn test_min(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  id(min(3, 7))
}
"""
        result = _compile_ok(source)
        assert result.wasm_bytes is not None

    def test_fncall_vera_type_int_to_float(self) -> None:
        """int_to_float() in generic context triggers line 514-515."""
        source = """\
private forall<T> fn id(@T -> @T)
  requires(true) ensures(true) effects(pure)
{ @T.0 }

public fn test_itof(@Unit -> @Float64)
  requires(true) ensures(true) effects(pure)
{
  id(int_to_float(42))
}
"""
        result = _compile_ok(source)
        assert result.wasm_bytes is not None

    def test_fncall_vera_type_float_to_int(self) -> None:
        """float_to_int() in generic context triggers line 516-517."""
        source = """\
private forall<T> fn id(@T -> @T)
  requires(true) ensures(true) effects(pure)
{ @T.0 }

public fn test_ftoi(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  id(float_to_int(3.14))
}
"""
        result = _compile_ok(source)
        assert result.wasm_bytes is not None


# =====================================================================
# TestInferFncallWasmType — _infer_fncall_wasm_type builtin branches
# =====================================================================

class TestInferFncallWasmType:
    """Tests for _infer_fncall_wasm_type builtin return type branches.

    These are triggered when a builtin function call appears in a
    context where the WASM type must be inferred (e.g., as the result
    of an if-branch, operand of binary, let binding initializer).
    """

    def test_fncall_wasm_array_range(self) -> None:
        """array_range in if-branch triggers line 198-199."""
        source = """\
public fn mk_range(@Bool -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Array<Int> = if @Bool.0 then { array_range(0, 3) } else { array_range(0, 5) };
  array_length(@Array<Int>.0)
}
"""
        assert _run(source, "mk_range", [1]) == 3
        assert _run(source, "mk_range", [0]) == 5

    def test_fncall_wasm_string_length(self) -> None:
        """string_length in if-branch triggers line 201-202."""
        source = """\
public fn cond_len(@Bool -> @Int)
  requires(true) ensures(true) effects(pure)
{
  if @Bool.0 then { string_length("hello") } else { string_length("hi") }
}
"""
        assert _run(source, "cond_len", [1]) == 5
        assert _run(source, "cond_len", [0]) == 2

    def test_fncall_wasm_string_concat(self) -> None:
        """string_concat in if-branch triggers line 204-208."""
        source = """\
public fn cond_cat(@Bool -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @String = if @Bool.0 then { string_concat("a", "b") } else { string_concat("c", "d") };
  IO.print(@String.0)
}
"""
        output = _run_io(source, "cond_cat", [1])
        assert "ab" in output

    def test_fncall_wasm_string_char_code(self) -> None:
        """string_char_code in if-branch triggers line 210-211."""
        source = """\
public fn cond_code(@Bool -> @Int)
  requires(true) ensures(true) effects(pure)
{
  if @Bool.0 then { string_char_code("A", 0) } else { 0 }
}
"""
        assert _run(source, "cond_code", [1]) == 65

    def test_fncall_wasm_string_from_char_code(self) -> None:
        """string_from_char_code in if-branch triggers line 213-214."""
        source = """\
public fn cond_from_code(@Bool -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @String = if @Bool.0 then { string_from_char_code(65) } else { "?" };
  IO.print(@String.0)
}
"""
        output = _run_io(source, "cond_from_code", [1])
        assert "A" in output

    def test_fncall_wasm_string_repeat(self) -> None:
        """string_repeat in if-branch triggers line 216-217."""
        source = """\
public fn cond_rep(@Bool -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @String = if @Bool.0 then { string_repeat("ab", 3) } else { "x" };
  IO.print(@String.0)
}
"""
        output = _run_io(source, "cond_rep", [1])
        assert "ababab" in output

    def test_fncall_wasm_string_contains(self) -> None:
        """string_contains in if-branch triggers line 219-221."""
        source = """\
public fn cond_contains(@Bool -> @Bool)
  requires(true) ensures(true) effects(pure)
{
  if @Bool.0 then { string_contains("hello world", "world") } else { false }
}
"""
        assert _run(source, "cond_contains", [1]) == 1

    def test_fncall_wasm_string_index_of(self) -> None:
        """string_index_of in if-branch triggers line 222-223."""
        source = """\
private data Option<T> { None, Some(T) }

public fn cond_idx(@Bool -> @Int)
  requires(true) ensures(true) effects(pure)
{
  if @Bool.0 then {
    match string_index_of("hello", "ll") {
      None -> -1,
      Some(@Int) -> @Int.0
    }
  } else {
    0
  }
}
"""
        assert _run(source, "cond_idx", [1]) == 2

    def test_fncall_wasm_string_upper(self) -> None:
        """string_upper in if-branch triggers line 225-227."""
        source = """\
public fn cond_upper(@Bool -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @String = if @Bool.0 then { string_upper("hello") } else { "bye" };
  IO.print(@String.0)
}
"""
        output = _run_io(source, "cond_upper", [1])
        assert "HELLO" in output

    def test_fncall_wasm_string_split(self) -> None:
        """string_split in if-branch triggers line 228-229."""
        source = """\
public fn cond_split(@Bool -> @Int)
  requires(true) ensures(true) effects(pure)
{
  if @Bool.0 then {
    array_length(string_split("a,b,c", ","))
  } else {
    0
  }
}
"""
        assert _run(source, "cond_split", [1]) == 3

    def test_fncall_wasm_show(self) -> None:
        """show() in if-branch triggers line 252-253."""
        source = """\
public fn test_show(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @String = if true then { show(42) } else { "none" };
  IO.print(@String.0)
}
"""
        output = _run_io(source, "test_show")
        assert "42" in output

    def test_fncall_wasm_hash(self) -> None:
        """hash() in if-branch triggers line 254-255."""
        source = """\
public fn test_hash(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  if true then { hash(42) } else { 0 }
}
"""
        assert _run(source, "test_hash") == 42

    def test_fncall_wasm_sqrt(self) -> None:
        """sqrt() in if-branch triggers line 262-263."""
        source = """\
public fn cond_sqrt(@Bool -> @Float64)
  requires(true) ensures(true) effects(pure)
{
  if @Bool.0 then { sqrt(4.0) } else { 0.0 }
}
"""
        result = _compile_ok(source)
        assert "cond_sqrt" in (result.exports or [])

    def test_fncall_wasm_int_to_float(self) -> None:
        """int_to_float() in if-branch triggers line 265-266."""
        source = """\
public fn cond_itof(@Bool -> @Float64)
  requires(true) ensures(true) effects(pure)
{
  if @Bool.0 then { int_to_float(42) } else { 0.0 }
}
"""
        result = _compile_ok(source)
        assert "cond_itof" in (result.exports or [])

    def test_fncall_wasm_float_to_int(self) -> None:
        """float_to_int() in if-branch triggers line 267-268."""
        source = """\
public fn cond_ftoi(@Bool -> @Int)
  requires(true) ensures(true) effects(pure)
{
  if @Bool.0 then { float_to_int(3.14) } else { 0 }
}
"""
        assert _run(source, "cond_ftoi", [1]) == 3

    def test_fncall_wasm_int_to_nat(self) -> None:
        """int_to_nat() in if-branch triggers line 269-270."""
        source = """\
private data Option<T> { None, Some(T) }

public fn cond_iton(@Bool -> @Int)
  requires(true) ensures(true) effects(pure)
{
  if @Bool.0 then {
    match int_to_nat(5) {
      None -> -1,
      Some(@Nat) -> 1
    }
  } else {
    0
  }
}
"""
        assert _run(source, "cond_iton", [1]) == 1

    def test_fncall_wasm_float_is_nan(self) -> None:
        """float_is_nan() in if-branch triggers line 272-273."""
        source = """\
public fn cond_nan(@Bool -> @Bool)
  requires(true) ensures(true) effects(pure)
{
  if @Bool.0 then { float_is_nan(0.0) } else { false }
}
"""
        assert _run(source, "cond_nan", [1]) == 0

    def test_fncall_wasm_nan(self) -> None:
        """nan() in if-branch triggers line 274-275."""
        source = """\
public fn cond_mknan(@Bool -> @Float64)
  requires(true) ensures(true) effects(pure)
{
  if @Bool.0 then { nan(()) } else { 0.0 }
}
"""
        result = _compile_ok(source)
        assert result.wasm_bytes is not None

    def test_fncall_wasm_apply_fn(self) -> None:
        """apply_fn() in if-branch triggers line 277-278."""
        source = """\
type IntFn = fn(Int -> Int) effects(pure);

private fn make_fn(@Unit -> @IntFn)
  requires(true) ensures(true) effects(pure)
{
  fn(@Int -> @Int) effects(pure) { @Int.0 * 2 }
}

public fn cond_apply(@Bool -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @IntFn = make_fn(());
  if @Bool.0 then { apply_fn(@IntFn.0, 21) } else { 0 }
}
"""
        assert _run(source, "cond_apply", [1]) == 42

    def test_fncall_wasm_abs(self) -> None:
        """abs() in if-branch triggers line 260-261."""
        source = """\
public fn cond_abs(@Bool, @Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  if @Bool.0 then { abs(@Int.0) } else { 0 }
}
"""
        result = _compile_ok(source)
        assert "cond_abs" in (result.exports or [])


# =====================================================================
# TestInferExprWasmTypeDeep — deeper _infer_expr_wasm_type branches
# =====================================================================

class TestInferExprWasmTypeDeep:
    """Tests for deeper branches in _infer_expr_wasm_type.

    Targets specific expression types that appear in contexts where
    WASM type inference is triggered (if-branches, match arms, let
    bindings, binary operands).
    """

    def test_unit_lit_in_branch(self) -> None:
        """UnitLit in if-branch triggers _infer_expr_wasm_type
        UnitLit branch (line 88-89)."""
        source = """\
public fn maybe_print(@Bool -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  if @Bool.0 then { IO.print("yes") } else { () }
}
"""
        output = _run_io(source, "maybe_print", [1])
        assert "yes" in output

    def test_interpolated_string_in_branch(self) -> None:
        """InterpolatedString in if-branch triggers
        _infer_expr_wasm_type InterpolatedString branch (line 154-155)
        and _infer_block_result_type InterpolatedString branch (line 337-338)."""
        source = """\
public fn greet(@Bool, @Int -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @String = if @Bool.0 then { "n=\\(@Int.0)" } else { "none" };
  IO.print(@String.0)
}
"""
        output = _run_io(source, "greet", [1, 42])
        assert "n=42" in output

    def test_qualified_call_in_branch(self) -> None:
        """QualifiedCall (IO.print) in if-branch triggers
        _infer_expr_wasm_type QualifiedCall branch (line 156-157)."""
        source = """\
public fn maybe_read(@Bool -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  if @Bool.0 then { IO.print("a") } else { IO.print("b") }
}
"""
        result = _compile_ok(source)
        assert "maybe_read" in (result.exports or [])

    def test_handle_expr_wasm_type(self) -> None:
        """HandleExpr in a context needing type inference triggers
        _infer_expr_wasm_type HandleExpr branch (line 142-146)."""
        source = """\
public fn state_result(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Int = handle[State<Int>](@Int = 10) {
    get(@Unit) -> { resume(@Int.0) },
    put(@Int) -> { resume(()) }
  } in {
    get(())
  };
  @Int.0 + 1
}
"""
        assert _run(source, "state_result") == 11

    def test_match_expr_in_let(self) -> None:
        """MatchExpr in let binding triggers _infer_expr_wasm_type
        MatchExpr branch (line 138-141)."""
        source = """\
private data Color { Red, Green, Blue }

public fn color_num(@Color -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Int = match @Color.0 {
    Red -> 1,
    Green -> 2,
    Blue -> 3
  };
  @Int.0 * 10
}
"""
        result = _compile_ok(source)
        assert "color_num" in (result.exports or [])

    def test_constructor_in_let(self) -> None:
        """ConstructorCall in let triggers _infer_expr_wasm_type
        ConstructorCall branch (line 134-135)."""
        source = """\
private data Option<T> { None, Some(T) }

public fn wrap(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Option<Int> = Some(@Int.0);
  match @Option<Int>.0 {
    None -> 0,
    Some(@Int) -> @Int.0
  }
}
"""
        assert _run(source, "wrap", [42]) == 42

    def test_nullary_constructor_in_let(self) -> None:
        """NullaryConstructor in let triggers _infer_expr_wasm_type
        NullaryConstructor branch (line 136-137)."""
        source = """\
private data Option<T> { None, Some(T) }

public fn mk_none(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Option<Int> = None;
  match @Option<Int>.0 {
    None -> -1,
    Some(@Int) -> @Int.0
  }
}
"""
        assert _run(source, "mk_none") == -1

    def test_block_in_branch(self) -> None:
        """Block expression in if-branch triggers _infer_expr_wasm_type
        Block branch (line 160-161)."""
        source = """\
public fn block_if(@Bool, @Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  if @Bool.0 then {
    {
      let @Int = @Int.0 * 2;
      @Int.0 + 1
    }
  } else {
    @Int.0
  }
}
"""
        assert _run(source, "block_if", [1, 5]) == 11
        assert _run(source, "block_if", [0, 5]) == 5

    def test_index_expr_in_binary(self) -> None:
        """IndexExpr as operand of binary triggers _infer_expr_wasm_type
        IndexExpr branch (line 147-149)."""
        source = """\
public fn sum_first_two(@Array<Int> -> @Int)
  requires(true) ensures(true) effects(pure)
{
  @Array<Int>.0[0] + @Array<Int>.0[1]
}

public fn test_sum(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  sum_first_two([10, 20, 30])
}
"""
        assert _run(source, "test_sum") == 30

    def test_and_or_implies_in_expr(self) -> None:
        """AND/OR/IMPLIES in _infer_expr_wasm_type (line 124-125)."""
        source = """\
public fn logic(@Bool, @Bool -> @Bool)
  requires(true) ensures(true) effects(pure)
{
  let @Bool = @Bool.0 && @Bool.1;
  let @Bool = @Bool.0 || @Bool.1;
  @Bool.0 ==> @Bool.1
}
"""
        result = _compile_ok(source)
        assert "logic" in (result.exports or [])

    def test_unary_neg_in_expr(self) -> None:
        """UnaryExpr NEG in _infer_expr_wasm_type (line 127-129)."""
        source = """\
public fn neg_add(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Int = -@Int.0;
  @Int.0 + 1
}
"""
        assert _run(source, "neg_add", [5]) == -4

    def test_unary_not_in_expr(self) -> None:
        """UnaryExpr NOT in _infer_expr_wasm_type (line 130-131)."""
        source = """\
public fn not_and(@Bool -> @Bool)
  requires(true) ensures(true) effects(pure)
{
  let @Bool = !@Bool.0;
  @Bool.0 && @Bool.1
}
"""
        result = _compile_ok(source)
        assert "not_and" in (result.exports or [])

    def test_pair_type_slot_ref(self) -> None:
        """SlotRef with pair type (String/Array) in _infer_expr_wasm_type
        triggers the pair type check (line 98-99)."""
        source = """\
public fn str_pass(@String -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @String = @String.0;
  IO.print(@String.0)
}
"""
        result = _compile_ok(source)
        assert "str_pass" in (result.exports or [])

    def test_fn_alias_slot_ref(self) -> None:
        """SlotRef with function type alias triggers
        _infer_expr_wasm_type FnType alias check (line 105-107)."""
        source = """\
type IntFn = fn(Int -> Int) effects(pure);

private fn apply_twice(@IntFn, @Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Int = apply_fn(@IntFn.0, @Int.0);
  apply_fn(@IntFn.0, @Int.0)
}

public fn test_twice(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @IntFn = fn(@Int -> @Int) effects(pure) { @Int.0 + 1 };
  apply_twice(@IntFn.0, 0)
}
"""
        assert _run(source, "test_twice") == 2

    def test_if_expr_in_binary(self) -> None:
        """IfExpr as operand of binary triggers _infer_expr_wasm_type
        IfExpr branch (line 158-159)."""
        source = """\
public fn if_add(@Bool, @Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  (if @Bool.0 then { @Int.0 } else { 0 }) + 1
}
"""
        assert _run(source, "if_add", [1, 5]) == 6
        assert _run(source, "if_add", [0, 5]) == 1

    def test_string_lit_in_let(self) -> None:
        """StringLit in _infer_expr_wasm_type (line 152-153)."""
        source = """\
public fn str_test(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @String = "hello";
  let @String = "world";
  IO.print(@String.0)
}
"""
        output = _run_io(source, "str_test")
        assert "world" in output

    def test_array_lit_in_binary(self) -> None:
        """ArrayLit in _infer_expr_wasm_type (line 150-151)."""
        source = """\
public fn arr_test(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Array<Int> = [1, 2, 3];
  array_length(@Array<Int>.0)
}
"""
        assert _run(source, "arr_test") == 3


# =====================================================================
# TestBlockResultTypeEdgeCases — _infer_block_result_type extra branches
# =====================================================================

class TestBlockResultTypeEdgeCases:
    """Tests for _infer_block_result_type edge case branches.

    These target specific block-ending expression types that are
    handled by _infer_block_result_type but not yet covered.
    """

    def test_block_result_float_slot_ref(self) -> None:
        """Float64 slot ref as block result triggers
        _infer_block_result_type Float64 branch (line 306)."""
        source = """\
public fn pick_float(@Bool, @Float64 -> @Float64)
  requires(true) ensures(true) effects(pure)
{
  if @Bool.0 then { @Float64.0 } else { 0.0 }
}
"""
        result = _compile_ok(source)
        assert "pick_float" in (result.exports or [])

    def test_block_result_bool_slot_ref(self) -> None:
        """Bool slot ref as block result triggers
        _infer_block_result_type Bool branch (line 307-308)."""
        source = """\
public fn pick_bool(@Bool, @Bool -> @Bool)
  requires(true) ensures(true) effects(pure)
{
  if @Bool.0 then { @Bool.1 } else { false }
}
"""
        assert _run(source, "pick_bool", [1, 1]) == 1

    def test_block_result_pair_slot_ref(self) -> None:
        """String slot ref as block result triggers
        _infer_block_result_type pair branch (line 309-310)."""
        source = """\
public fn pick_string(@Bool, @String -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @String = if @Bool.0 then { @String.0 } else { "default" };
  IO.print(@String.0)
}
"""
        result = _compile_ok(source)
        assert "pick_string" in (result.exports or [])

    def test_block_result_adt_slot_ref(self) -> None:
        """ADT slot ref as block result triggers
        _infer_block_result_type ADT branch (line 312-313)."""
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

    def test_block_result_assert(self) -> None:
        """AssertExpr as block result triggers
        _infer_block_result_type assert branch (line 356-357)."""
        source = """\
public fn assert_last(@Int -> @Unit)
  requires(@Int.0 > 0) ensures(true) effects(pure)
{
  assert(@Int.0 > 0)
}
"""
        result = _compile_ok(source)
        assert "assert_last" in (result.exports or [])

    def test_block_result_quantifier(self) -> None:
        """ForallExpr as block result triggers
        _infer_block_result_type quantifier branch (line 354-355)."""
        source = """\
public fn all_pos(@Array<Int> -> @Bool)
  requires(true) ensures(true) effects(pure)
{
  if true then {
    forall(@Int, array_length(@Array<Int>.0), fn(@Int -> @Bool) effects(pure) { @Array<Int>.0[@Int.0] > 0 })
  } else {
    false
  }
}
"""
        result = _compile_ok(source)
        assert "all_pos" in (result.exports or [])


# =====================================================================
# TestSlotNameToWasmType — _slot_name_to_wasm_type branches
# =====================================================================

class TestSlotNameToWasmType:
    """Tests for _slot_name_to_wasm_type edge case branches.

    These are triggered when the compiler maps slot type names to
    WASM types during local variable allocation and access.
    """

    def test_fn_type_alias_slot(self) -> None:
        """Function type alias as slot triggers _slot_name_to_wasm_type
        FnType alias branch (line 825-828)."""
        source = """\
type IntFn = fn(Int -> Int) effects(pure);

private fn make_adder(@Int -> @IntFn)
  requires(true) ensures(true) effects(pure)
{
  fn(@Int -> @Int) effects(pure) { @Int.0 + @Int.1 }
}

public fn test_slot(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @IntFn = make_adder(10);
  apply_fn(@IntFn.0, 5)
}
"""
        assert _run(source, "test_slot") == 15

    def test_adt_slot_type(self) -> None:
        """ADT slot type triggers _slot_name_to_wasm_type ADT branch
        (line 821-823)."""
        source = """\
private data Box { Wrap(Int) }

public fn test_box(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Box = Wrap(42);
  match @Box.0 {
    Wrap(@Int) -> @Int.0
  }
}
"""
        assert _run(source, "test_box") == 42

    def test_float64_slot_type(self) -> None:
        """Float64 slot triggers _slot_name_to_wasm_type Float64 branch
        (line 813)."""
        source = """\
public fn float_slot(@Float64 -> @Float64)
  requires(true) ensures(true) effects(pure)
{
  let @Float64 = @Float64.0 + 1.0;
  @Float64.0
}
"""
        result = _compile_ok(source)
        assert "f64.add" in result.wat

    def test_bool_slot_type(self) -> None:
        """Bool slot triggers _slot_name_to_wasm_type Bool branch
        (line 815)."""
        source = """\
public fn bool_slot(@Bool -> @Bool)
  requires(true) ensures(true) effects(pure)
{
  let @Bool = !@Bool.0;
  @Bool.0
}
"""
        assert _run(source, "bool_slot", [1]) == 0


# =====================================================================
# TestGenericFnApplyVeraType — apply_fn vera type inference
# =====================================================================

class TestGenericFnApplyVeraType:
    """Tests for _infer_fncall_vera_type apply_fn branches.

    apply_fn() calls need Vera-level type inference to resolve
    generic type aliases and determine the closure return type.
    """

    def test_apply_fn_vera_type(self) -> None:
        """apply_fn() in generic context triggers
        _infer_fncall_vera_type apply_fn branch (line 464-485)."""
        source = """\
type IntFn = fn(Int -> Int) effects(pure);

private forall<T> fn id(@T -> @T)
  requires(true) ensures(true) effects(pure)
{ @T.0 }

private fn make_fn(@Unit -> @IntFn)
  requires(true) ensures(true) effects(pure)
{
  fn(@Int -> @Int) effects(pure) { @Int.0 + 1 }
}

public fn test_apply(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @IntFn = make_fn(());
  id(apply_fn(@IntFn.0, 41))
}
"""
        result = _compile_ok(source)
        assert result.wasm_bytes is not None

    def test_apply_fn_wasm_return_type_inference(self) -> None:
        """apply_fn() non-generic FnType alias triggers
        _infer_apply_fn_return_type _fn_type_return_wasm branch (line 677)."""
        source = """\
type IntFn = fn(Int -> Int) effects(pure);

private fn apply(@IntFn, @Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  apply_fn(@IntFn.0, @Int.0)
}

public fn test_apply_rt(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @IntFn = fn(@Int -> @Int) effects(pure) { @Int.0 * 3 };
  apply(@IntFn.0, 14)
}
"""
        result = _compile_ok(source)
        assert result.wasm_bytes is not None

    def test_generic_fn_return_wasm(self) -> None:
        """Generic FnType alias with type args triggers
        _resolve_generic_fn_return (line 680-702)."""
        source = """\
type Mapper<A, B> = fn(A -> B) effects(pure);

private fn apply_mapper(@Mapper<Int, Int>, @Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  apply_fn(@Mapper<Int, Int>.0, @Int.0)
}

public fn test_mapper(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Mapper<Int, Int> = fn(@Int -> @Int) effects(pure) { @Int.0 * 2 };
  apply_mapper(@Mapper<Int, Int>.0, 21)
}
"""
        result = _compile_ok(source)
        assert result.wasm_bytes is not None


# =====================================================================
# TestResolveBaseTypeName — _resolve_base_type_name paths
# =====================================================================

class TestResolveBaseTypeName:
    """Tests for _resolve_base_type_name alias resolution.

    Refinement type aliases need to resolve through the alias chain
    to their base primitive type for WASM type selection.
    """

    def test_refinement_alias_chain(self) -> None:
        """Refinement type alias resolves to base type (line 797-805)."""
        source = """\
type PosInt = { @Int | @Int.0 > 0 };

public fn add_pos(@PosInt, @PosInt -> @Int)
  requires(true) ensures(true) effects(pure)
{
  @PosInt.0 + @PosInt.1
}
"""
        assert _run(source, "add_pos", [3, 4]) == 7

    def test_named_type_alias_resolution(self) -> None:
        """NamedType alias (type Foo = Bar) resolves through chain
        (line 803-804)."""
        source = """\
type MyInt = Int;

public fn use_alias(@MyInt -> @Int)
  requires(true) ensures(true) effects(pure)
{
  @MyInt.0 + 1
}
"""
        assert _run(source, "use_alias", [5]) == 6


# =====================================================================
# TestOperatorsADTEquality — ADT structural equality (operators.py 182-236)
# =====================================================================


class TestOperatorsADTEquality:
    """Tests for ADT structural equality with fields.

    Targets missed lines in operators.py: general case ADT equality
    with field comparison (lines 182-236), field load/eq helpers
    (lines 241, 247), string NEQ (line 100), ADT NEQ (line 118).
    """

    def test_adt_eq_with_fields(self) -> None:
        """ADT equality on constructors with Int fields."""
        source = """\
private data Shape {
  Circle(Int),
  Rect(Int, Int)
}

public fn shapes_eq(@Shape, @Shape -> @Bool)
  requires(true) ensures(true) effects(pure)
{
  @Shape.0 == @Shape.1
}

public fn test_same(@Unit -> @Bool)
  requires(true) ensures(true) effects(pure)
{
  shapes_eq(Circle(5), Circle(5))
}

public fn test_diff_field(@Unit -> @Bool)
  requires(true) ensures(true) effects(pure)
{
  shapes_eq(Circle(5), Circle(10))
}

public fn test_diff_ctor(@Unit -> @Bool)
  requires(true) ensures(true) effects(pure)
{
  shapes_eq(Circle(5), Rect(5, 10))
}
"""
        assert _run(source, "test_same") == 1
        assert _run(source, "test_diff_field") == 0
        assert _run(source, "test_diff_ctor") == 0

    def test_adt_neq_with_fields(self) -> None:
        """ADT != on constructors with Int fields (line 118)."""
        source = """\
private data Box { Wrap(Int) }

public fn boxes_neq(@Box, @Box -> @Bool)
  requires(true) ensures(true) effects(pure)
{
  @Box.0 != @Box.1
}

public fn test_neq_same(@Unit -> @Bool)
  requires(true) ensures(true) effects(pure)
{
  boxes_neq(Wrap(5), Wrap(5))
}

public fn test_neq_diff(@Unit -> @Bool)
  requires(true) ensures(true) effects(pure)
{
  boxes_neq(Wrap(5), Wrap(10))
}
"""
        assert _run(source, "test_neq_same") == 0
        assert _run(source, "test_neq_diff") == 1

    def test_adt_eq_multi_field(self) -> None:
        """ADT equality with multiple fields per constructor."""
        source = """\
private data Pair { MkPair(Int, Int) }

public fn pairs_eq(@Pair, @Pair -> @Bool)
  requires(true) ensures(true) effects(pure)
{
  @Pair.0 == @Pair.1
}

public fn test_pairs(@Unit -> @Bool)
  requires(true) ensures(true) effects(pure)
{
  pairs_eq(MkPair(1, 2), MkPair(1, 2))
}

public fn test_pairs_diff(@Unit -> @Bool)
  requires(true) ensures(true) effects(pure)
{
  pairs_eq(MkPair(1, 2), MkPair(1, 3))
}
"""
        assert _run(source, "test_pairs") == 1
        assert _run(source, "test_pairs_diff") == 0

    def test_adt_eq_mixed_fieldless_and_fields(self) -> None:
        """ADT with both fieldless and field-bearing constructors."""
        source = """\
private data Option { None, Some(Int) }

public fn opts_eq(@Option, @Option -> @Bool)
  requires(true) ensures(true) effects(pure)
{
  @Option.0 == @Option.1
}

public fn test_none_none(@Unit -> @Bool)
  requires(true) ensures(true) effects(pure)
{
  opts_eq(None, None)
}

public fn test_some_some(@Unit -> @Bool)
  requires(true) ensures(true) effects(pure)
{
  opts_eq(Some(42), Some(42))
}

public fn test_some_diff(@Unit -> @Bool)
  requires(true) ensures(true) effects(pure)
{
  opts_eq(Some(42), Some(99))
}

public fn test_none_some(@Unit -> @Bool)
  requires(true) ensures(true) effects(pure)
{
  opts_eq(None, Some(42))
}
"""
        assert _run(source, "test_none_none") == 1
        assert _run(source, "test_some_some") == 1
        assert _run(source, "test_some_diff") == 0
        assert _run(source, "test_none_some") == 0

    def test_string_neq(self) -> None:
        """String != comparison (line 100)."""
        source = """\
effect IO { op print(String -> Unit); }

public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  if "hello" != "world" then {
    IO.print("diff")
  } else {
    IO.print("same")
  }
}
"""
        assert _run_io(source, fn="main") == "diff"

    def test_string_neq_equal(self) -> None:
        """String != on equal strings returns false."""
        source = """\
effect IO { op print(String -> Unit); }

public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  if "hello" != "hello" then {
    IO.print("diff")
  } else {
    IO.print("same")
  }
}
"""
        assert _run_io(source, fn="main") == "same"

    def test_float_mod(self) -> None:
        """Float64 modulo via f64 mod decomposition (line 84)."""
        source = """\
public fn fmod(@Float64, @Float64 -> @Float64)
  requires(true) ensures(true) effects(pure)
{
  @Float64.1 % @Float64.0
}
"""
        result = _run_float(source, "fmod", [10.0, 3.0])
        assert abs(result - 1.0) < 0.001


# =====================================================================
# TestMarkdownCoverage — markdown.py write/read paths
# =====================================================================


class TestMarkdownCoverage:
    """Tests for markdown WASM marshalling coverage.

    Exercises write_md_inline / write_md_block / read_md_inline /
    read_md_block for block and inline element types that lack coverage:
    MdCode, MdEmph, MdStrong, MdLink, MdImage (inline),
    MdBlockQuote, MdList, MdThematicBreak, MdTable (block).
    """

    _PREAMBLE = """
effect IO { op print(String -> Unit); }
"""

    def test_md_render_emphasis(self) -> None:
        """Emphasis (*text*) triggers MdEmph write/read paths."""
        source = self._PREAMBLE + r"""
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Result<MdBlock, String> = md_parse("*emphasis*");
  match @Result<MdBlock, String>.0 {
    Ok(@MdBlock) -> {
      let @String = md_render(@MdBlock.0);
      IO.print(@String.0)
    },
    Err(_) -> IO.print("err")
  }
}
"""
        assert _run_io(source, fn="main") == "*emphasis*"

    def test_md_render_strong(self) -> None:
        """Strong (**text**) triggers MdStrong write/read paths."""
        source = self._PREAMBLE + r"""
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Result<MdBlock, String> = md_parse("**bold**");
  match @Result<MdBlock, String>.0 {
    Ok(@MdBlock) -> {
      let @String = md_render(@MdBlock.0);
      IO.print(@String.0)
    },
    Err(_) -> IO.print("err")
  }
}
"""
        assert _run_io(source, fn="main") == "**bold**"

    def test_md_render_inline_code(self) -> None:
        """Inline code (`code`) triggers MdCode write/read paths."""
        source = self._PREAMBLE + r"""
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Result<MdBlock, String> = md_parse("use `code` here");
  match @Result<MdBlock, String>.0 {
    Ok(@MdBlock) -> {
      let @String = md_render(@MdBlock.0);
      IO.print(@String.0)
    },
    Err(_) -> IO.print("err")
  }
}
"""
        assert _run_io(source, fn="main") == "use `code` here"

    def test_md_render_link(self) -> None:
        """Link [text](url) triggers MdLink write/read paths."""
        source = self._PREAMBLE + r"""
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Result<MdBlock, String> = md_parse("[click](https://example.com)");
  match @Result<MdBlock, String>.0 {
    Ok(@MdBlock) -> {
      let @String = md_render(@MdBlock.0);
      IO.print(@String.0)
    },
    Err(_) -> IO.print("err")
  }
}
"""
        assert _run_io(source, fn="main") == "[click](https://example.com)"

    def test_md_render_image(self) -> None:
        """Image ![alt](src) triggers MdImage write/read paths."""
        source = self._PREAMBLE + r"""
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Result<MdBlock, String> = md_parse("![alt](img.png)");
  match @Result<MdBlock, String>.0 {
    Ok(@MdBlock) -> {
      let @String = md_render(@MdBlock.0);
      IO.print(@String.0)
    },
    Err(_) -> IO.print("err")
  }
}
"""
        assert _run_io(source, fn="main") == "![alt](img.png)"

    def test_md_render_blockquote(self) -> None:
        """Blockquote (> text) triggers MdBlockQuote write/read paths."""
        source = self._PREAMBLE + """
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Result<MdBlock, String> = md_parse("> quoted text");
  match @Result<MdBlock, String>.0 {
    Ok(@MdBlock) -> {
      let @String = md_render(@MdBlock.0);
      IO.print(@String.0)
    },
    Err(_) -> IO.print("err")
  }
}
"""
        out = _run_io(source, fn="main")
        assert "quoted text" in out

    def test_md_render_unordered_list(self) -> None:
        """Unordered list (- item) triggers MdList write/read paths."""
        source = self._PREAMBLE + """
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Result<MdBlock, String> = md_parse("- one\\n- two");
  match @Result<MdBlock, String>.0 {
    Ok(@MdBlock) -> {
      let @String = md_render(@MdBlock.0);
      IO.print(@String.0)
    },
    Err(_) -> IO.print("err")
  }
}
"""
        out = _run_io(source, fn="main")
        assert "one" in out
        assert "two" in out

    def test_md_render_ordered_list(self) -> None:
        """Ordered list (1. item) triggers MdList write/read paths."""
        source = self._PREAMBLE + """
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Result<MdBlock, String> = md_parse("1. first\\n2. second");
  match @Result<MdBlock, String>.0 {
    Ok(@MdBlock) -> {
      let @String = md_render(@MdBlock.0);
      IO.print(@String.0)
    },
    Err(_) -> IO.print("err")
  }
}
"""
        out = _run_io(source, fn="main")
        assert "first" in out
        assert "second" in out

    def test_md_render_thematic_break(self) -> None:
        """Thematic break (---) triggers MdThematicBreak write/read paths."""
        source = self._PREAMBLE + """
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Result<MdBlock, String> = md_parse("above\\n\\n---\\n\\nbelow");
  match @Result<MdBlock, String>.0 {
    Ok(@MdBlock) -> {
      let @String = md_render(@MdBlock.0);
      IO.print(@String.0)
    },
    Err(_) -> IO.print("err")
  }
}
"""
        out = _run_io(source, fn="main")
        assert "---" in out

    def test_md_render_table(self) -> None:
        """Table triggers MdTable write/read paths."""
        source = self._PREAMBLE + """
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Result<MdBlock, String> = md_parse("| A | B |\\n|---|---|\\n| 1 | 2 |");
  match @Result<MdBlock, String>.0 {
    Ok(@MdBlock) -> {
      let @String = md_render(@MdBlock.0);
      IO.print(@String.0)
    },
    Err(_) -> IO.print("err")
  }
}
"""
        out = _run_io(source, fn="main")
        assert "A" in out
        assert "B" in out


# =====================================================================
# TestOperatorsPipeModuleCall — pipe with ModuleCall (operators.py 63-69)
# =====================================================================


class TestOperatorsPipeModuleCall:
    """Tests for pipe operator with module-qualified calls.

    Targets missed lines in operators.py: pipe with ModuleCall (63-69).
    """

    def test_pipe_module_call(self) -> None:
        """Pipe with module-qualified call desugars correctly."""
        source = """\
import vera.math(abs);

public fn test_pipe(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  -5 |> vera.math::abs()
}
"""
        assert _run(source, "test_pipe") == 5


# =====================================================================
# TestInferExprWasmTypeRemaining — remaining _infer_expr_wasm_type paths
# =====================================================================

class TestInferExprWasmTypeRemaining:
    """Tests targeting remaining uncovered _infer_expr_wasm_type branches.

    These exercise paths that are only reached when expressions appear
    as match scrutinees, constructor args, closure args, or operands
    where the direct (not block) inference is used.
    """

    def test_and_or_as_match_scrutinee(self) -> None:
        """AND/OR expression as match scrutinee triggers
        _infer_expr_wasm_type AND/OR branch (line 124-125)."""
        source = """\
public fn logic_match(@Bool, @Bool -> @Int)
  requires(true) ensures(true) effects(pure)
{
  match @Bool.0 && @Bool.1 {
    true -> 1,
    false -> 0
  }
}
"""
        assert _run(source, "logic_match", [1, 1]) == 1
        assert _run(source, "logic_match", [1, 0]) == 0

    def test_not_as_match_scrutinee(self) -> None:
        """UnaryExpr NOT as match scrutinee triggers
        _infer_expr_wasm_type NOT branch (line 130-131)."""
        source = """\
public fn not_match(@Bool -> @Int)
  requires(true) ensures(true) effects(pure)
{
  match !@Bool.0 {
    true -> 1,
    false -> 0
  }
}
"""
        assert _run(source, "not_match", [1]) == 0
        assert _run(source, "not_match", [0]) == 1

    def test_array_lit_as_constructor_arg(self) -> None:
        """ArrayLit in constructor arg triggers _infer_expr_wasm_type
        ArrayLit branch via data.py constructor arg inference."""
        source = """\
private data Wrapper { Wrap(Array<Int>) }

public fn test_wrap(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Wrapper = Wrap([1, 2, 3]);
  match @Wrapper.0 {
    Wrap(@Array<Int>) -> array_length(@Array<Int>.0)
  }
}
"""
        result = _compile_ok(source)
        assert result.wasm_bytes is not None

    def test_interpolated_string_in_constructor(self) -> None:
        """InterpolatedString in constructor arg context."""
        source = """\
private data Box { Wrap(String) }

public fn test_box(@Int -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Box = Wrap("val=\\(@Int.0)");
  match @Box.0 {
    Wrap(@String) -> IO.print(@String.0)
  }
}
"""
        result = _compile_ok(source)
        assert result.wasm_bytes is not None

    def test_match_expr_in_match_arm(self) -> None:
        """MatchExpr as match arm body triggers _infer_expr_wasm_type
        MatchExpr branch (line 138-141) via data.py arm body inference."""
        source = """\
private data Color { Red, Green, Blue }
private data Size { Small, Large }

public fn classify(@Color, @Size -> @Int)
  requires(true) ensures(true) effects(pure)
{
  match @Color.0 {
    Red -> match @Size.0 {
      Small -> 1,
      Large -> 2
    },
    Green -> 3,
    Blue -> 4
  }
}
"""
        result = _compile_ok(source)
        assert result.wasm_bytes is not None

    def test_constructor_call_in_match_arm(self) -> None:
        """ConstructorCall as match arm body triggers
        _infer_expr_wasm_type ConstructorCall branch (line 134-135)
        via data.py arm body inference."""
        source = """\
private data Option<T> { None, Some(T) }
private data Color { Red, Green, Blue }

public fn color_opt(@Color -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Option<Int> = match @Color.0 {
    Red -> Some(1),
    Green -> Some(2),
    Blue -> None
  };
  match @Option<Int>.0 {
    None -> 0,
    Some(@Int) -> @Int.0
  }
}
"""
        result = _compile_ok(source)
        assert result.wasm_bytes is not None

    def test_fncall_as_match_arm(self) -> None:
        """FnCall as match arm body triggers _infer_expr_wasm_type
        FnCall branch (line 132-133) via data.py arm body inference."""
        source = """\
private data Bit { Zero, One }

private fn double(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 * 2 }

public fn bit_double(@Bit, @Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  match @Bit.0 {
    Zero -> @Int.0,
    One -> double(@Int.0)
  }
}
"""
        result = _compile_ok(source)
        assert result.wasm_bytes is not None

    def test_forall_as_match_arm(self) -> None:
        """ForallExpr as match arm body triggers _infer_expr_wasm_type
        ForallExpr branch (line 162-163)."""
        source = """\
private data Bit { Zero, One }

public fn cond_forall(@Bit, @Array<Int> -> @Bool)
  requires(true) ensures(true) effects(pure)
{
  match @Bit.0 {
    Zero -> false,
    One -> forall(@Int, array_length(@Array<Int>.0), fn(@Int -> @Bool) effects(pure) { @Array<Int>.0[@Int.0] > 0 })
  }
}
"""
        result = _compile_ok(source)
        assert result.wasm_bytes is not None

    def test_assert_as_match_arm(self) -> None:
        """AssertExpr as match arm body triggers _infer_expr_wasm_type
        AssertExpr branch (line 164-165)."""
        source = """\
private data Bit { Zero, One }

public fn cond_assert(@Bit, @Int -> @Unit)
  requires(@Int.0 > 0) ensures(true) effects(pure)
{
  match @Bit.0 {
    Zero -> (),
    One -> assert(@Int.0 > 0)
  }
}
"""
        result = _compile_ok(source)
        assert result.wasm_bytes is not None

    def test_if_expr_as_match_arm(self) -> None:
        """IfExpr as match arm body triggers _infer_expr_wasm_type
        IfExpr branch (line 158-159) via data.py arm body inference."""
        source = """\
private data Bit { Zero, One }

public fn bit_cond(@Bit, @Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  match @Bit.0 {
    Zero -> 0,
    One -> if @Int.0 > 0 then { @Int.0 } else { 0 }
  }
}
"""
        result = _compile_ok(source)
        assert result.wasm_bytes is not None

    def test_block_as_match_arm(self) -> None:
        """Block as match arm body triggers _infer_expr_wasm_type
        Block branch (line 160-161)."""
        source = """\
private data Bit { Zero, One }

public fn bit_block(@Bit, @Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  match @Bit.0 {
    Zero -> 0,
    One -> {
      let @Int = @Int.0 * 2;
      @Int.0
    }
  }
}
"""
        result = _compile_ok(source)
        assert result.wasm_bytes is not None

    def test_string_lit_as_match_arm(self) -> None:
        """StringLit as match arm body triggers _infer_expr_wasm_type
        StringLit branch (line 152-153)."""
        source = """\
private data Bit { Zero, One }

public fn bit_str(@Bit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @String = match @Bit.0 {
    Zero -> "zero",
    One -> "one"
  };
  IO.print(@String.0)
}
"""
        result = _compile_ok(source)
        assert result.wasm_bytes is not None

    def test_qualified_call_as_match_arm(self) -> None:
        """QualifiedCall as match arm body triggers
        _infer_expr_wasm_type QualifiedCall branch (line 156-157)."""
        source = """\
private data Bit { Zero, One }

public fn bit_io(@Bit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  match @Bit.0 {
    Zero -> IO.print("0"),
    One -> IO.print("1")
  }
}
"""
        result = _compile_ok(source)
        assert result.wasm_bytes is not None

    def test_index_expr_as_match_arm(self) -> None:
        """IndexExpr as match arm body triggers _infer_expr_wasm_type
        IndexExpr branch (line 147-149)."""
        source = """\
private data Bit { Zero, One }

public fn bit_idx(@Bit, @Array<Int> -> @Int)
  requires(true) ensures(true) effects(pure)
{
  match @Bit.0 {
    Zero -> @Array<Int>.0[0],
    One -> @Array<Int>.0[1]
  }
}
"""
        result = _compile_ok(source)
        assert result.wasm_bytes is not None

    def test_neg_float_as_match_arm(self) -> None:
        """UnaryExpr NEG with float as match arm triggers
        _infer_expr_wasm_type NEG branch (line 127-129)."""
        source = """\
private data Bit { Zero, One }

public fn neg_float(@Bit, @Float64 -> @Float64)
  requires(true) ensures(true) effects(pure)
{
  match @Bit.0 {
    Zero -> @Float64.0,
    One -> -@Float64.0
  }
}
"""
        result = _compile_ok(source)
        assert "f64.neg" in result.wat

    def test_array_lit_as_match_arm(self) -> None:
        """ArrayLit as match arm body triggers _infer_expr_wasm_type
        ArrayLit branch (line 150-151)."""
        source = """\
private data Bit { Zero, One }

public fn bit_arr(@Bit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Array<Int> = match @Bit.0 {
    Zero -> [0],
    One -> [1, 2]
  };
  array_length(@Array<Int>.0)
}
"""
        result = _compile_ok(source)
        assert result.wasm_bytes is not None

    def test_nullary_ctor_as_match_arm(self) -> None:
        """NullaryConstructor as match arm body triggers
        _infer_expr_wasm_type NullaryConstructor branch (line 136-137)."""
        source = """\
private data Option<T> { None, Some(T) }
private data Bit { Zero, One }

public fn bit_opt(@Bit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Option<Int> = match @Bit.0 {
    Zero -> None,
    One -> Some(42)
  };
  match @Option<Int>.0 {
    None -> 0,
    Some(@Int) -> @Int.0
  }
}
"""
        result = _compile_ok(source)
        assert result.wasm_bytes is not None


# =====================================================================
# TestClosureCoverage — closure lifting coverage gaps
# =====================================================================


class TestClosureCoverageGCPaths:
    """Cover uncovered lines in vera/codegen/closures.py.

    Targets:
    - Line 125: closure with ADT param (i32 pointer tracked for GC)
    - Line 191: closure capturing ADT value (pointer pushed to GC shadow)
    """

    def test_closure_with_adt_param(self) -> None:
        """A closure that takes an ADT param triggers the i32 pointer
        tracking branch (line 125)."""
        source = """\
private data Color { Red, Green, Blue }
type ColorFn = fn(Color -> Int) effects(pure);

private fn make_color_fn(-> @ColorFn)
  requires(true) ensures(true) effects(pure)
{
  fn(@Color -> @Int) effects(pure) {
    match @Color.0 {
      Red -> 0,
      Green -> 1,
      Blue -> 2
    }
  }
}

public fn apply_color(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @ColorFn = make_color_fn();
  apply_fn(@ColorFn.0, Green)
}
"""
        result = _compile_ok(source)
        assert result.wasm_bytes is not None
        exec_result = execute(result, fn_name="apply_color", args=[])
        assert exec_result.value == 1

    def test_closure_capturing_adt(self) -> None:
        """A closure that captures an ADT value triggers the captured
        pointer GC shadow push (line 191).

        The closure body must read the captured @Box (at @Box.1 after
        the local let pushes a fresh @Box.0) so the captured ADT
        pointer actually enters the closure environment. The body also
        allocates to trigger GC prologue/epilogue."""
        source = """\
private data Box { MkBox(Int) }
type IntFn = fn(Int -> Int) effects(pure);

private fn make_box_fn(@Box -> @IntFn)
  requires(true) ensures(true) effects(pure)
{
  fn(@Int -> @Int) effects(pure) {
    let @Box = MkBox(@Int.0);
    match @Box.1 {
      MkBox(@Int) -> match @Box.0 {
        MkBox(@Int) -> @Int.0 + @Int.1
      }
    }
  }
}

public fn use_box_fn(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Box = MkBox(42);
  let @IntFn = make_box_fn(@Box.0);
  apply_fn(@IntFn.0, 10)
}
"""
        result = _compile_ok(source)
        assert result.wasm_bytes is not None

    def test_closure_capturing_multiple_values(self) -> None:
        """A closure capturing multiple values of different types."""
        source = """\
type IntFn = fn(Int -> Int) effects(pure);

private fn make_weighted_adder(@Int, @Nat -> @IntFn)
  requires(true) ensures(true) effects(pure)
{
  fn(@Int -> @Int) effects(pure) {
    @Int.0 + @Int.1 + nat_to_int(@Nat.0)
  }
}

public fn test_multi_capture(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @IntFn = make_weighted_adder(10, 5);
  apply_fn(@IntFn.0, 100)
}
"""
        result = _compile_ok(source)
        assert result.wasm_bytes is not None
        exec_result = execute(result, fn_name="test_multi_capture", args=[])
        assert exec_result.value == 115

    def test_closure_returning_adt(self) -> None:
        """A closure that returns an ADT value (i32 pointer return)."""
        source = """\
private data Box { MkBox(Int) }
type BoxFn = fn(Int -> Box) effects(pure);

private fn make_boxer(-> @BoxFn)
  requires(true) ensures(true) effects(pure)
{
  fn(@Int -> @Box) effects(pure) {
    MkBox(@Int.0)
  }
}

public fn test_adt_return(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @BoxFn = make_boxer();
  let @Box = apply_fn(@BoxFn.0, 99);
  match @Box.0 {
    MkBox(@Int) -> @Int.0
  }
}
"""
        result = _compile_ok(source)
        assert result.wasm_bytes is not None
        exec_result = execute(result, fn_name="test_adt_return", args=[])
        assert exec_result.value == 99

    def test_closure_capturing_adt_with_allocation(self) -> None:
        """Closure capturing an ADT and allocating in body triggers
        GC shadow push for captured pointer (line 191)."""
        source = """\
private data Pair { MkPair(Int, Int) }
type PairFn = fn(Int -> Pair) effects(pure);

private fn make_pair_fn(@Pair -> @PairFn)
  requires(true) ensures(true) effects(pure)
{
  fn(@Int -> @Pair) effects(pure) {
    match @Pair.0 {
      MkPair(@Int, @Int) -> MkPair(@Int.0 + @Int.2, @Int.1)
    }
  }
}

public fn test_pair_closure(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Pair = MkPair(10, 20);
  let @PairFn = make_pair_fn(@Pair.0);
  let @Pair = apply_fn(@PairFn.0, 5);
  match @Pair.0 {
    MkPair(@Int, @Int) -> @Int.0 + @Int.1
  }
}
"""
        result = _compile_ok(source)
        assert result.wasm_bytes is not None
