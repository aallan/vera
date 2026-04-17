"""Tests for vera.codegen — Monomorphization of generic (forall<T>) functions."""

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

public fn main(-> @Int)
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

public fn main(-> @Bool)
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

public fn test_int(-> @Int)
  requires(true) ensures(true) effects(pure)
{ identity(42) }

public fn test_bool(-> @Bool)
  requires(true) ensures(true) effects(pure)
{ identity(false) }
"""
        result = _compile_ok(source)
        # Private generic -> monomorphized variants not exported
        assert "identity$Int" not in result.exports
        assert "identity$Bool" not in result.exports
        # Public callers are exported
        assert "test_int" in result.exports
        assert "test_bool" in result.exports
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

public fn main(@Int -> @Int)
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

public fn main(-> @Int)
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

public fn main(-> @Bool)
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

public fn main(-> @Bool)
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

public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ identity(42) }
"""
        result = _compile_ok(source)
        assert "$identity$Int" in result.wat

    def test_generic_fn_mangled_in_exports(self) -> None:
        """Private generic's mangled names not exported; public caller is."""
        source = """\
private forall<T> fn identity(@T -> @T)
  requires(true) ensures(true) effects(pure)
{ @T.0 }

public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ identity(42) }
"""
        result = _compile_ok(source)
        # Private generic -> monomorphized variants not exported
        assert "identity$Int" not in result.exports
        assert "identity" not in result.exports
        # Public caller is exported
        assert "main" in result.exports

    def test_non_generic_fn_unaffected(self) -> None:
        """Non-generic functions compile normally alongside generic ones."""
        source = """\
private forall<T> fn identity(@T -> @T)
  requires(true) ensures(true) effects(pure)
{ @T.0 }

public fn double(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 + @Int.0 }

public fn main(-> @Int)
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

public fn main(-> @Int)
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

public fn main(-> @Int)
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

public fn main(@Bool -> @Int)
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

public fn main(-> @Int)
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

public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ 42 }
"""
        result = _compile_ok(source)
        assert "main" in result.exports
        # identity has no callers -> no monomorphized version -> not in exports
        assert "identity" not in result.exports

    def test_generics_example_file(self) -> None:
        """examples/generics.vera compiles without errors."""
        from pathlib import Path
        path = Path(__file__).parent.parent / "examples" / "generics.vera"
        source = path.read_text()
        result = _compile(source)
        assert result.ok

    def test_list_ops_example_file(self) -> None:
        """examples/list_ops.vera compiles and runs correctly (#154)."""
        from pathlib import Path
        path = Path(__file__).parent.parent / "examples" / "list_ops.vera"
        source = path.read_text()
        result = _compile_ok(source)
        exec_result = execute(result, fn_name="test_list")
        assert exec_result.value == 60


# =====================================================================
# C6j: Ability constraint satisfaction and operation codegen
# =====================================================================


class TestAbilityConstraints:
    """Tests for ability constraint checking and eq() operation rewriting."""

    def test_eq_int(self) -> None:
        """forall<T where Eq<T>> with Int — equal values return true."""
        source = """\
private forall<T where Eq<T>> fn are_equal(@T, @T -> @Bool)
  requires(true) ensures(true) effects(pure)
{ eq(@T.0, @T.1) }

public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  if are_equal(42, 42) then { 1 } else { 0 }
}
"""
        assert _run(source, fn="main") == 1

    def test_eq_int_false(self) -> None:
        """forall<T where Eq<T>> with Int — unequal values return false."""
        source = """\
private forall<T where Eq<T>> fn are_equal(@T, @T -> @Bool)
  requires(true) ensures(true) effects(pure)
{ eq(@T.0, @T.1) }

public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  if are_equal(1, 2) then { 1 } else { 0 }
}
"""
        assert _run(source, fn="main") == 0

    def test_eq_bool(self) -> None:
        """forall<T where Eq<T>> with Bool."""
        source = """\
private forall<T where Eq<T>> fn are_equal(@T, @T -> @Bool)
  requires(true) ensures(true) effects(pure)
{ eq(@T.0, @T.1) }

public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  if are_equal(true, true) then { 1 } else { 0 }
}
"""
        assert _run(source, fn="main") == 1

    def test_eq_in_if(self) -> None:
        """eq result used directly as if condition."""
        source = """\
private forall<T where Eq<T>> fn are_equal(@T, @T -> @Bool)
  requires(true) ensures(true) effects(pure)
{ eq(@T.0, @T.1) }

public fn main(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  if are_equal(@Int.0, 10) then { 100 } else { 200 }
}
"""
        assert _run(source, fn="main", args=[10]) == 100
        assert _run(source, fn="main", args=[5]) == 200

    def test_eq_constraint_multiple_calls(self) -> None:
        """Same constrained fn called with Int and Bool."""
        source = """\
private forall<T where Eq<T>> fn are_equal(@T, @T -> @Bool)
  requires(true) ensures(true) effects(pure)
{ eq(@T.0, @T.1) }

public fn test_int(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  if are_equal(5, 5) then { 1 } else { 0 }
}

public fn test_bool(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  if are_equal(false, false) then { 1 } else { 0 }
}
"""
        result = _compile_ok(source)
        exec_int = execute(result, fn_name="test_int")
        assert exec_int.value == 1
        exec_bool = execute(result, fn_name="test_bool")
        assert exec_bool.value == 1

    def test_eq_non_generic_direct_call(self) -> None:
        """eq(1, 1) in a non-generic function — rewritten by Pass 1.6."""
        source = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  if eq(1, 1) then { 1 } else { 0 }
}
"""
        assert _run(source, fn="main") == 1

    def test_eq_nested_in_expression(self) -> None:
        """eq in let bindings combined with boolean and."""
        source = """\
private forall<T where Eq<T>> fn are_equal(@T, @T -> @Bool)
  requires(true) ensures(true) effects(pure)
{ eq(@T.0, @T.1) }

public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Bool = are_equal(3, 3);
  let @Bool = are_equal(7, 7);
  if @Bool.0 && @Bool.1 then { 1 } else { 0 }
}
"""
        assert _run(source, fn="main") == 1

    def test_eq_simple_enum(self) -> None:
        """Simple enum ADT satisfies Eq via auto-derivation."""
        source = """\
private data Color { Red, Green, Blue }

private forall<T where Eq<T>> fn are_equal(@T, @T -> @Bool)
  requires(true) ensures(true) effects(pure)
{ eq(@T.0, @T.1) }

public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  if are_equal(Red, Blue) then { 1 } else { 0 }
}
"""
        assert _run(source, fn="main") == 0

    def test_eq_simple_enum_equal(self) -> None:
        """Simple enum Eq returns true for same constructor."""
        source = """\
private data Color { Red, Green, Blue }

private forall<T where Eq<T>> fn are_equal(@T, @T -> @Bool)
  requires(true) ensures(true) effects(pure)
{ eq(@T.0, @T.1) }

public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  if are_equal(Red, Red) then { 1 } else { 0 }
}
"""
        assert _run(source, fn="main") == 1

    # ----------------------------------------------------------------
    # compare (Ord)
    # ----------------------------------------------------------------

    def test_compare_int_less(self) -> None:
        """compare(1, 2) → Less, matched to return 1."""
        source = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  match compare(1, 2) {
    Less -> 1,
    Equal -> 2,
    Greater -> 3
  }
}
"""
        assert _run(source, fn="main") == 1

    def test_compare_int_equal(self) -> None:
        """compare(5, 5) → Equal, matched to return 2."""
        source = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  match compare(5, 5) {
    Less -> 1,
    Equal -> 2,
    Greater -> 3
  }
}
"""
        assert _run(source, fn="main") == 2

    def test_compare_int_greater(self) -> None:
        """compare(9, 3) → Greater, matched to return 3."""
        source = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  match compare(9, 3) {
    Less -> 1,
    Equal -> 2,
    Greater -> 3
  }
}
"""
        assert _run(source, fn="main") == 3

    def test_compare_constrained_generic(self) -> None:
        """compare in constrained generic function."""
        source = """\
private forall<T where Ord<T>> fn cmp_result(@T, @T -> @Int)
  requires(true) ensures(true) effects(pure)
{
  match compare(@T.1, @T.0) {
    Less -> 0 - 1,
    Equal -> 0,
    Greater -> 1
  }
}

public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  cmp_result(3, 7)
}
"""
        # cmp_result(3, 7): @T.1 = 3 (first param), @T.0 = 7 (second)
        # compare(3, 7): 3 < 7 → Less → 0 - 1 = -1
        assert _run(source, fn="main") == -1

    # ----------------------------------------------------------------
    # show (Show)
    # ----------------------------------------------------------------

    def test_show_int(self) -> None:
        """show(42) produces the string \"42\"."""
        source = """\
public fn main(-> @Bool)
  requires(true) ensures(true) effects(pure)
{
  eq(show(42), "42")
}
"""
        assert _run(source, fn="main") == 1

    def test_show_bool(self) -> None:
        """show(true) produces the string \"true\"."""
        source = """\
public fn main(-> @Bool)
  requires(true) ensures(true) effects(pure)
{
  eq(show(true), "true")
}
"""
        assert _run(source, fn="main") == 1

    def test_show_string_identity(self) -> None:
        """show on a String is the identity."""
        source = """\
public fn main(-> @Bool)
  requires(true) ensures(true) effects(pure)
{
  eq(show("hello"), "hello")
}
"""
        assert _run(source, fn="main") == 1

    # ----------------------------------------------------------------
    # hash (Hash)
    # ----------------------------------------------------------------

    def test_hash_int_identity(self) -> None:
        """hash(42) == 42 (identity for Int)."""
        source = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  hash(42)
}
"""
        assert _run(source, fn="main") == 42

    def test_hash_bool(self) -> None:
        """hash(true) == 1, hash(false) == 0."""
        source = """\
public fn test_true(-> @Int)
  requires(true) ensures(true) effects(pure)
{ hash(true) }

public fn test_false(-> @Int)
  requires(true) ensures(true) effects(pure)
{ hash(false) }
"""
        assert _run(source, fn="test_true") == 1
        assert _run(source, fn="test_false") == 0

    def test_hash_string_consistent(self) -> None:
        """hash of the same string is consistent and non-zero."""
        source = """\
public fn main(-> @Bool)
  requires(true) ensures(true) effects(pure)
{
  eq(hash("hello"), hash("hello"))
}
"""
        assert _run(source, fn="main") == 1

    # ----------------------------------------------------------------
    # Unsatisfied constraint errors
    # ----------------------------------------------------------------

    def test_unsatisfied_ord_adt(self) -> None:
        """ADT type with Ord constraint → E613."""
        source = """\
private data Color { Red, Green, Blue }

private forall<T where Ord<T>> fn cmp(@T, @T -> @Ordering)
  requires(true) ensures(true) effects(pure)
{ compare(@T.1, @T.0) }

public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  match cmp(Red, Blue) {
    Less -> 1,
    Equal -> 2,
    Greater -> 3
  }
}
"""
        result = _compile(source)
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert any(d.error_code == "E613" for d in errors), (
            f"Expected E613, got: {[d.error_code for d in errors]}"
        )


# =====================================================================
# Array operations: array_slice, array_map, array_filter, array_fold
# =====================================================================


class TestArrayOperations:
    """Tests for array_slice, array_map, array_filter, and array_fold."""

    # ----------------------------------------------------------------
    # array_slice
    # ----------------------------------------------------------------

    def test_array_slice_basic(self) -> None:
        """Slice [10,20,30,40,50] from index 1 to 4, expect length 3."""
        source = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  array_length(array_slice([10, 20, 30, 40, 50], 1, 4))
}
"""
        assert _run(source, fn="main") == 3

    def test_array_slice_empty(self) -> None:
        """Slice with start >= end returns empty array."""
        source = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  array_length(array_slice([1, 2, 3], 2, 2))
}
"""
        assert _run(source, fn="main") == 0

    def test_array_slice_clamped(self) -> None:
        """Out-of-range indices are clamped to array bounds."""
        source = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  array_length(array_slice([1, 2, 3], 0, 100))
}
"""
        assert _run(source, fn="main") == 3

    # ----------------------------------------------------------------
    # array_map
    # ----------------------------------------------------------------

    def test_array_map_int(self) -> None:
        """Map *10 over [1,2,3], check first element is 10."""
        source = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Array<Int> = array_map([1, 2, 3], fn(@Int -> @Int) effects(pure) { @Int.0 * 10 });
  @Array<Int>.0[0]
}
"""
        assert _run(source, fn="main") == 10

    def test_array_map_identity(self) -> None:
        """Map identity function, result matches input length."""
        source = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Array<Int> = array_map([5, 10, 15], fn(@Int -> @Int) effects(pure) { @Int.0 });
  @Array<Int>.0[1]
}
"""
        assert _run(source, fn="main") == 10

    # ----------------------------------------------------------------
    # array_filter
    # ----------------------------------------------------------------

    def test_array_filter_basic(self) -> None:
        """Filter [1,2,3,4,5,6] where > 3, expect length 3."""
        source = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  array_length(array_filter([1, 2, 3, 4, 5, 6], fn(@Int -> @Bool) effects(pure) { @Int.0 > 3 }))
}
"""
        assert _run(source, fn="main") == 3

    def test_array_filter_none(self) -> None:
        """Filter where always false returns empty array."""
        source = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  array_length(array_filter([1, 2, 3], fn(@Int -> @Bool) effects(pure) { @Int.0 > 100 }))
}
"""
        assert _run(source, fn="main") == 0

    def test_array_filter_all(self) -> None:
        """Filter where always true returns same length."""
        source = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  array_length(array_filter([1, 2, 3, 4], fn(@Int -> @Bool) effects(pure) { @Int.0 > 0 }))
}
"""
        assert _run(source, fn="main") == 4

    # ----------------------------------------------------------------
    # array_fold
    # ----------------------------------------------------------------

    def test_array_fold_sum(self) -> None:
        """Fold + over [1,2,3,4] with init 0, expect 10."""
        source = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  array_fold([1, 2, 3, 4], 0, fn(@Int, @Int -> @Int) effects(pure) { @Int.1 + @Int.0 })
}
"""
        assert _run(source, fn="main") == 10

    def test_array_fold_product(self) -> None:
        """Fold * over [1,2,3,4] with init 1, expect 24."""
        source = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  array_fold([1, 2, 3, 4], 1, fn(@Int, @Int -> @Int) effects(pure) { @Int.1 * @Int.0 })
}
"""
        assert _run(source, fn="main") == 24

    # ----------------------------------------------------------------
    # Chained operations
    # ----------------------------------------------------------------

    def test_array_map_filter_chain(self) -> None:
        """Map *2 then filter > 5: [1,2,3,4,5] -> [2,4,6,8,10] -> [6,8,10]."""
        source = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Array<Int> = array_map([1, 2, 3, 4, 5], fn(@Int -> @Int) effects(pure) { @Int.0 * 2 });
  array_length(array_filter(@Array<Int>.0, fn(@Int -> @Bool) effects(pure) { @Int.0 > 5 }))
}
"""
        assert _run(source, fn="main") == 3

    # ----------------------------------------------------------------
    # Type-check tests (compile without errors)
    # ----------------------------------------------------------------

    def test_array_slice_type_check(self) -> None:
        """array_slice type-checks successfully."""
        source = """\
public fn main(-> @Array<Int>)
  requires(true) ensures(true) effects(pure)
{
  array_slice([1, 2, 3], 0, 2)
}
"""
        _compile_ok(source)

    def test_array_map_type_check(self) -> None:
        """array_map type-checks successfully."""
        source = """\
public fn main(-> @Array<Int>)
  requires(true) ensures(true) effects(pure)
{
  array_map([1, 2, 3], fn(@Int -> @Int) effects(pure) { @Int.0 + 1 })
}
"""
        _compile_ok(source)

    def test_array_filter_type_check(self) -> None:
        """array_filter type-checks successfully."""
        source = """\
public fn main(-> @Array<Int>)
  requires(true) ensures(true) effects(pure)
{
  array_filter([1, 2, 3], fn(@Int -> @Bool) effects(pure) { @Int.0 > 1 })
}
"""
        _compile_ok(source)

    def test_array_fold_type_check(self) -> None:
        """array_fold type-checks successfully."""
        source = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  array_fold([1, 2, 3], 0, fn(@Int, @Int -> @Int) effects(pure) { @Int.1 + @Int.0 })
}
"""
        _compile_ok(source)

    # ----------------------------------------------------------------
    # array_map — regression tests for the iterative implementation
    # (#480).  These exercise paths the existing tests above don't:
    # large inputs (stress the loop, not the recursion), closures
    # that capture outer variables, A != B with pair output, and
    # scalar Int → scalar Bool type change.
    # ----------------------------------------------------------------

    def test_array_map_large_input_no_stack_overflow(self) -> None:
        """8,000-element map without blowing the shadow stack.

        Regression guard: under the old recursive prelude implementation
        this would allocate 8,000 stack frames and hit the 16K shadow
        stack ceiling (post-#464).  The iterative implementation uses a
        single WAT ``loop`` with O(1) stack depth regardless of input
        size.

        Size note: the GC's object-header size field is currently 16-bit
        (max 65535 bytes) — see #484.  Output allocations must stay
        under that limit or the sweep corrupts the payload.  8,000 Int
        elements = 64,000 bytes — just under the ceiling.  Once #484
        lands this test can grow to 100K+.
        """
        source = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Array<Int> = array_range(0, 8000);
  let @Array<Int> = array_map(@Array<Int>.0, fn(@Int -> @Int) effects(pure) { @Int.0 * 2 });
  @Array<Int>.0[7999]
}
"""
        # Last element: 7999 * 2 = 15998
        assert _run(source, fn="main") == 15998

    def test_array_map_type_change_int_to_bool(self) -> None:
        """Map Int → Bool — exercises the distinct-A-and-B codegen path.

        All the existing tests keep the element type (Int → Int).  This
        one converts to Bool, which has a different WASM type (i32) and
        different element width (1 byte vs 8) from Int.  The store ops
        must pick up the B-sized layout, not reuse A's.
        """
        source = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Array<Bool> = array_map([0, 1, 2, 3], fn(@Int -> @Bool) effects(pure) { @Int.0 > 1 });
  -- [false, false, true, true] → sum of 1-for-each-true = 0+0+1+1 = 2
  if @Array<Bool>.0[0] then { 1 } else { 0 } +
  if @Array<Bool>.0[1] then { 1 } else { 0 } +
  if @Array<Bool>.0[2] then { 1 } else { 0 } +
  if @Array<Bool>.0[3] then { 1 } else { 0 }
}
"""
        assert _run(source, fn="main") == 2

    def test_array_map_closure_captures_outer_variable(self) -> None:
        """Closure passed to array_map references a captured outer value.

        Ensures the iterative loop body correctly sets up the closure
        environment — the free-variable walker must lift the captured
        binding into the closure struct, and the inside-the-loop
        ``call_indirect`` must pass the env pointer so captures
        resolve.
        """
        source = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Int = 100;
  let @Array<Int> = array_map([1, 2, 3], fn(@Int -> @Int) effects(pure) { @Int.0 + @Int.1 });
  @Array<Int>.0[2]
}
"""
        # Outer @Int.0 = 100 (captured); element 2 + captured 100 = 102
        assert _run(source, fn="main") == 103

    def test_array_map_pair_element_output(self) -> None:
        """Map Int → String — output is a pair-typed element (i32_pair).

        This exercises the pair-output path in the iterative
        translator: the store sequence must lay down ptr at offset 0
        and len at offset 4, keyed off an 8-byte stride.
        """
        source = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Array<String> = array_map([1, 2, 3], fn(@Int -> @String) effects(pure) { to_string(@Int.0) });
  string_length(@Array<String>.0[2])
}
"""
        # "3" has length 1
        assert _run(source, fn="main") == 1

    def test_array_map_empty_input(self) -> None:
        """Empty input → empty output; loop init/term exercised at n=0.

        Exercises the zero-length boundary: the loop's ``idx >= arr_len``
        guard must fire on the very first iteration so the body never
        runs, the closure is never invoked, and the allocated output
        array has length 0.
        """
        source = """\
public fn main(-> @Nat)
  requires(true) ensures(true) effects(pure)
{
  let @Array<Int> = array_range(0, 0);
  let @Array<Int> = array_map(@Array<Int>.0, fn(@Int -> @Int) effects(pure) { @Int.0 * 2 });
  array_length(@Array<Int>.0)
}
"""
        assert _run(source, fn="main") == 0
