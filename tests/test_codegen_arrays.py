"""Tests for vera.codegen — arrays (Byte type, array literals/bounds/length/range/concat, compound arrays, array utilities).

Split from tests/test_codegen.py (#419). Shared helpers live in tests/codegen_helpers.py.
"""
from __future__ import annotations

from tests.codegen_helpers import (
    _compile_ok,
    _run,
    _run_io,
    _run_trap,
)


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
