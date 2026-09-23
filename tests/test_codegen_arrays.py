"""Tests for vera.codegen — arrays (Byte type, array literals/bounds/length/range/concat, compound arrays, array utilities).

Split from tests/test_codegen.py (#419). Shared helpers live in tests/codegen_helpers.py.
"""
from __future__ import annotations

from tests.codegen_helpers import (
    _compile_ok,
    _run,
    _run_float,
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
        assert "call $rt.alloc" in result.wat

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
# Indexing directly on a builtin call result (#1048)
# =====================================================================


class TestIndexBuiltinCallResult:
    """Indexing directly on a builtin call result — `array_concat(...)[i]`
    — must infer the element type and compile, not drop the enclosing
    function via [E602] (#1048).

    Pre-fix, `_infer_index_element_type_expr`'s FnCall arm resolved only
    user-function returns (via `_fn_ret_type_exprs`); a builtin call had
    no entry there, element-type inference returned None, and the whole
    function was skipped.  The let-bound form (the control below) always
    worked — it resolves through the SlotRef arm, not the FnCall arm.
    """

    def test_index_array_concat_result_int(self) -> None:
        """Direct index on array_concat result — Int element (arg-forward
        resolution).  Pre-fix this dropped `g` via [E602] (#1048)."""
        src = """
public fn g(-> @Int) requires(true) ensures(true) effects(pure) {
  array_concat([10, 20], [30, 40])[2]
}
"""
        assert _run(src, fn="g") == 30

    def test_index_array_range_result_int(self) -> None:
        """Direct index on array_range result — resolves via the
        `_BUILTIN_PARAMETERIZED_RETURNS` table (Array<Int>), a different
        sub-path from array_concat's arg-forwarding (#1048)."""
        src = """
public fn g(-> @Int) requires(true) ensures(true) effects(pure) {
  array_range(10, 20)[3]
}
"""
        assert _run(src, fn="g") == 13

    def test_index_array_slice_result_int(self) -> None:
        """Direct index on array_slice result — 3-arg arg-forward builtin
        (#1048)."""
        src = """
public fn g(-> @Int) requires(true) ensures(true) effects(pure) {
  array_slice([10, 20, 30, 40, 50], 1, 4)[1]
}
"""
        assert _run(src, fn="g") == 30

    def test_index_array_concat_result_string(self) -> None:
        """Direct index on array_concat of Array<String>, then
        `string_length` — proves PAIR (pointer+length) elements resolve
        through the new arm, not only scalar Int (#1048)."""
        src = """
public fn g(-> @Int) requires(true) ensures(true) effects(pure) {
  string_length(array_concat(["ab", "cd"], ["efg"])[2])
}
"""
        assert _run(src, fn="g") == 3

    def test_index_builtin_call_no_e602_drop(self) -> None:
        """Structural: the direct-index-on-builtin-call function must be
        emitted, i.e. NO [E602] "function skipped" diagnostic (#1048)."""
        src = """
public fn g(-> @Int) requires(true) ensures(true) effects(pure) {
  array_concat([10, 20], [30, 40])[2]
}
"""
        result = _compile_ok(src)
        assert not any(d.error_code == "E602" for d in result.diagnostics), \
            "array_concat(...)[i] should not drop the function via E602"

    def test_index_builtin_call_let_bound_control(self) -> None:
        """Control: the let-bound form resolves through the SlotRef arm and
        stays green independently of the FnCall-arm fix (#1048)."""
        src = """
public fn g(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Array<Int> = array_concat([10, 20], [30, 40]);
  @Array<Int>.0[2]
}
"""
        assert _run(src, fn="g") == 30


class TestIndexTypevarBuiltinCallResult:
    """Indexing directly on a *type-variable-element* Array-returning builtin
    — `array_reverse([...])[0]`, `map_keys(m)[0]`, `array_map(xs, f)[0]` — must
    infer the element type from the call's ARGUMENTS and compile, not drop the
    enclosing function via [E602] (#1051).

    The #1048 fix resolved builtins whose return NamedType comes from the shared
    consultor tables (arg-forwarding for array_concat/.../array_filter, plus the
    `_BUILTIN_PARAMETERIZED_RETURNS` concrete-Array builtins).  These eight are
    absent from those tables because their element type depends on the CALL's
    arguments, not a fixed signature:

      * argument-forwarding   — array_reverse / array_sort_by (arg0's type
        verbatim), array_flatten (arg0's type with one Array<> unwrapped);
      * container-arg-derived — map_keys (K) / map_values (V) from Map<K, V>;
        set_to_array (T) from Set<T>;
      * closure-return-derived — array_map / array_mapi element = the closure
        argument's declared return type.

    The let-bound form (the controls below) always worked — it resolves through
    the SlotRef arm off the `let @Array<...>` annotation, not the FnCall arm.
    """

    # ---- Class 1: argument-forwarding -------------------------------------

    def test_index_array_reverse_int(self) -> None:
        """array_reverse([10, 20, 30])[0] -> 30 (arg0's type verbatim)."""
        src = """
public fn g(-> @Int) requires(true) ensures(true) effects(pure) {
  array_reverse([10, 20, 30])[0]
}
"""
        assert _run(src, fn="g") == 30

    def test_index_array_reverse_string(self) -> None:
        """Array<String> variant — pair (ptr, len) elements resolve through the
        derived Array<String> type, read back via string_length.  reverse of
        ["a", "bb", "ccc"] -> ["ccc", "bb", "a"]; [0] = "ccc" (length 3)."""
        src = """
public fn g(-> @Int) requires(true) ensures(true) effects(pure) {
  string_length(array_reverse(["a", "bb", "ccc"])[0])
}
"""
        assert _run(src, fn="g") == 3

    def test_index_array_sort_by_int(self) -> None:
        """array_sort_by([30, 10, 20], asc)[0] -> 10 (arg0's type verbatim)."""
        src = """
public fn g(-> @Int) requires(true) ensures(true) effects(pure) {
  array_sort_by([30, 10, 20], fn(@Int, @Int -> @Ordering) effects(pure) {
    if @Int.1 < @Int.0 then { Less } else {
      if @Int.1 > @Int.0 then { Greater } else { Equal }
    }
  })[0]
}
"""
        assert _run(src, fn="g") == 10

    def test_index_array_flatten_int(self) -> None:
        """array_flatten(Array<Array<Int>>)[2] -> 30 (arg0's Array<Array<Int>>
        with one Array<> layer unwrapped to Array<Int>).  The nested array is
        let-bound so the flatten ARGUMENT resolves through the SlotRef arm; the
        flatten RESULT is what is indexed directly (the #1051 case).  (The inline
        `[[..], [..]]` literal as a direct call argument is #1052 — see
        TestFlattenInlineNestedLiteral.)"""
        src = """
public fn g(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Array<Array<Int>> = [[10, 20], [30, 40]];
  array_flatten(@Array<Array<Int>>.0)[2]
}
"""
        assert _run(src, fn="g") == 30

    def test_index_array_reverse_of_concat(self) -> None:
        """Class 1 with a builtin-call argument: array_reverse's arg0 is itself
        a (consultor-resolvable) array_concat, so the derived return type comes
        from resolving that nested call.  concat -> [10, 20, 30, 40]; reverse ->
        [40, 30, 20, 10]; [0] = 40."""
        src = """
public fn g(-> @Int) requires(true) ensures(true) effects(pure) {
  array_reverse(array_concat([10, 20], [30, 40]))[0]
}
"""
        assert _run(src, fn="g") == 40

    def test_index_array_reverse_nested_chained(self) -> None:
        """Chained indexing on array_reverse of a nested array (class 1).
        reverse returns Array<Array<Int>> (arg0's type verbatim), so the outer
        [0] has element type Array<Int> (a pair) and the chained [1] unwraps to
        Int.  reverse of [[10,11,12],[20,21,22],[30,31,32]] ->
        [[30,31,32],[20,21,22],[10,11,12]]; [0][1] = 31."""
        src = """
public fn g(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Array<Array<Int>> = [[10, 11, 12], [20, 21, 22], [30, 31, 32]];
  array_reverse(@Array<Array<Int>>.0)[0][1]
}
"""
        assert _run(src, fn="g") == 31

    # ---- #1094: a NESTED type-variable-element builtin as the inner call,
    # the outer builtin's result indexed DIRECTLY (no let binding) ----------
    # `array_reverse(array_reverse(x))[0]` etc.  The inner call is one of the
    # eight type-variable-element builtins, so the shared consultor cannot
    # report its return type; class 1's forwarding arm and array_flatten's
    # unwrap arm now resolve a FnCall argument through
    # `_builtin_call_ret_named_type` (consultor first, then this same
    # per-class derivation), so the inner call's element type is recovered.
    # The let-bound spelling of each already worked (call-emission path,
    # #1053) and is pinned in TestNestedTypevarBuiltinArg.

    def test_index_reverse_of_reverse_int(self) -> None:
        """array_reverse(array_reverse([10, 20, 30]))[0] -> 10.  reverse twice
        is identity, so [0] is the head of the original.  Inner array_reverse
        is itself a type-variable-element builtin (arg0-forwarding), resolved
        by recursing through `_builtin_call_ret_named_type`."""
        src = """
public fn g(-> @Int) requires(true) ensures(true) effects(pure) {
  array_reverse(array_reverse([10, 20, 30]))[0]
}
"""
        assert _run(src, fn="g") == 10

    def test_index_reverse_of_reverse_int_mid(self) -> None:
        """... [2] -> 30 — a non-head index proves a real 3-element array is
        materialised, not a constant-folded head."""
        src = """
public fn g(-> @Int) requires(true) ensures(true) effects(pure) {
  array_reverse(array_reverse([10, 20, 30]))[2]
}
"""
        assert _run(src, fn="g") == 30

    def test_index_reverse_of_reverse_string(self) -> None:
        """Element-TYPE proof: String elements are (ptr, len) pairs, read back
        via string_length.  reverse twice is identity; [0] = "a" (length 1).
        If the derived element type were scalar-shaped the pair load would be
        wrong, so the value 1 pins the String element type through the nested
        resolution."""
        src = """
public fn g(-> @Int) requires(true) ensures(true) effects(pure) {
  string_length(array_reverse(array_reverse(["a", "bb", "ccc"]))[0])
}
"""
        assert _run(src, fn="g") == 1

    def test_index_sort_by_of_reverse_int(self) -> None:
        """array_sort_by(array_reverse([30, 10, 20]), asc)[0] -> 10.  Outer is
        class 1 (array_sort_by, arg0-forwarding); inner array_reverse is a
        type-variable-element builtin.  Sorting makes the result independent of
        the reverse, but the nested call must still resolve to compile."""
        src = """
public fn g(-> @Int) requires(true) ensures(true) effects(pure) {
  array_sort_by(array_reverse([30, 10, 20]), fn(@Int, @Int -> @Ordering) effects(pure) {
    if @Int.1 < @Int.0 then { Less } else {
      if @Int.1 > @Int.0 then { Greater } else { Equal }
    }
  })[0]
}
"""
        assert _run(src, fn="g") == 10

    def test_index_reverse_of_map_values_int(self) -> None:
        """array_reverse(map_values(m))[0] -> 77.  The inner map_values is a
        type-variable-element (container-arg-derived) builtin; the outer
        array_reverse forwards its Array<Int> return.  Single-entry map keeps
        the reversed value deterministic without relying on map order."""
        src = """
public fn g(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Map<String, Int> = map_insert(map_new(), "k", 77);
  array_reverse(map_values(@Map<String, Int>.0))[0]
}
"""
        assert _run(src, fn="g") == 77

    def test_index_sort_by_of_map_values_int(self) -> None:
        """array_sort_by(map_values(m), asc)[0] -> 10 — the headline #1094 case.
        Three-entry map {a:30, b:10, c:20}; sorting the values ascending is
        order-independent, so [0] is deterministically the minimum (10)
        regardless of map iteration order."""
        src = """
public fn g(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Map<String, Int> = map_insert(map_insert(map_insert(map_new(), "a", 30), "b", 10), "c", 20);
  array_sort_by(map_values(@Map<String, Int>.0), fn(@Int, @Int -> @Ordering) effects(pure) {
    if @Int.1 < @Int.0 then { Less } else {
      if @Int.1 > @Int.0 then { Greater } else { Equal }
    }
  })[0]
}
"""
        assert _run(src, fn="g") == 10

    def test_index_flatten_of_reverse_int(self) -> None:
        """array_flatten(array_reverse([[10, 20], [30, 40]]))[0] -> 30.  The
        array_flatten unwrap arm resolves its FnCall argument (inner
        array_reverse) through the same recursion.  reverse -> [[30,40],
        [10,20]]; flatten -> [30, 40, 10, 20]; [0] = 30 (30, not 10, proves the
        reverse actually happened across the flatten boundary)."""
        src = """
public fn g(-> @Int) requires(true) ensures(true) effects(pure) {
  array_flatten(array_reverse([[10, 20], [30, 40]]))[0]
}
"""
        assert _run(src, fn="g") == 30

    def test_index_nested_typevar_inner_no_e602_drop(self) -> None:
        """Structural: directly indexing a nested type-variable-element builtin
        result must NOT drop the enclosing function via [E602].  Pins the
        warning's absence so a regression (or the mutation-validation revert)
        shows the loud skip returning."""
        src = """
public fn g(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Map<String, Int> = map_insert(map_insert(map_new(), "a", 30), "b", 10);
  array_sort_by(map_values(@Map<String, Int>.0), fn(@Int, @Int -> @Ordering) effects(pure) {
    if @Int.1 < @Int.0 then { Less } else {
      if @Int.1 > @Int.0 then { Greater } else { Equal }
    }
  })[0]
}
"""
        result = _compile_ok(src)
        assert "g" in result.exports, \
            "nested type-var-element inner call, directly indexed, must compile"
        assert not any(d.error_code == "E602" for d in result.diagnostics), \
            "directly indexing a nested type-var builtin must not E602-drop"

    def test_index_reverse_of_concat_pin(self) -> None:
        """Pin: array_reverse's inner arg is a consultor-resolvable array_concat,
        which resolved before #1094 too (via `_named_type_from_arg_info`).  Must
        stay green — the fix routes FnCall args through
        `_builtin_call_ret_named_type`, which tries the consultor first.
        concat -> [10, 20, 30, 40]; reverse -> [40, 30, 20, 10]; [0] = 40."""
        src = """
public fn g(-> @Int) requires(true) ensures(true) effects(pure) {
  array_reverse(array_concat([10, 20], [30, 40]))[0]
}
"""
        assert _run(src, fn="g") == 40

    def test_index_map_over_map_values_pin(self) -> None:
        """Pin: array_map(map_values(m), f)[0] resolves via class 3 (closure
        return), which never reads arg0, so it worked before #1094.  Must stay
        green.  map_values -> [5]; mapped |x| x + 100 -> [105]; [0] = 105."""
        src = """
public fn g(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Map<String, Int> = map_insert(map_new(), "k", 5);
  array_map(map_values(@Map<String, Int>.0), fn(@Int -> @Int) effects(pure) {
    @Int.0 + 100
  })[0]
}
"""
        assert _run(src, fn="g") == 105

    # ---- Class 2: container-arg-derived -----------------------------------

    def test_index_map_keys_string(self) -> None:
        """map_keys(Map<String, Int>)[0] -> the String key (element type K).
        Single-entry map so keys[0] is deterministic; read back via
        string_length ("abcde" -> 5) to prove the pair element type."""
        src = """
public fn g(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Map<String, Int> = map_insert(map_new(), "abcde", 99);
  string_length(map_keys(@Map<String, Int>.0)[0])
}
"""
        assert _run(src, fn="g") == 5

    def test_index_map_values_int(self) -> None:
        """map_values(Map<String, Int>)[0] -> the Int value (element type V)."""
        src = """
public fn g(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Map<String, Int> = map_insert(map_new(), "k", 77);
  map_values(@Map<String, Int>.0)[0]
}
"""
        assert _run(src, fn="g") == 77

    def test_index_set_to_array_int(self) -> None:
        """set_to_array(Set<Int>)[0] -> the Int element (element type T)."""
        src = """
public fn g(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Set<Int> = set_add(set_new(), 88);
  set_to_array(@Set<Int>.0)[0]
}
"""
        assert _run(src, fn="g") == 88

    def test_index_map_keys_inline_map_arg_stays_loud_skip(self) -> None:
        """Honest boundary (#1051): when the Map argument is built INLINE by a
        non-consultor builtin (`map_insert`) instead of let-bound, the shared
        consultor cannot recover its `Map<K, V>` type, so the class-2 derivation
        yields None and the enclosing function keeps the LOUD [E602] skip rather
        than guessing an element type or silently mis-compiling.  (The common
        let-bound `@Map<K, V>` argument resolves — see
        test_index_map_keys_string.)"""
        src = """
public fn g(-> @Int) requires(true) ensures(true) effects(pure) {
  string_length(map_keys(map_insert(map_new(), "abcde", 99))[0])
}
"""
        result = _compile_ok(src)
        assert "g" not in result.exports, \
            "inline-built Map arg is unresolvable — must drop, not compile wrong"
        assert any(d.error_code == "E602" for d in result.diagnostics), \
            "the unresolvable argument shape must keep the loud E602 skip"

    # ---- #1055: alias-spelled arguments canonicalize -----------------------
    # An alias argument (`type M = Map<String, Int>; @M.0`) reached the
    # derivations as its bare alias name with NO type args, so the class
    # arms never saw the container shape and the index E602-dropped where
    # the direct spelling compiled.  `_named_type_from_arg_info` now
    # canonicalizes a bare alias name to its target's full compound spelling
    # (the #1037 walk) before parsing.  (The array builtins with aliased
    # arguments — `array_flatten(@Grid.0)` / `array_reverse(@Row.0)` —
    # additionally needed the builtin's CALL emission to canonicalize; that
    # alias extension is part of the #1053 work, pinned in
    # TestAliasSpelledArgCallEmission, with the Map/Set emission tag side in
    # TestContainerArgEmissionTag.)

    def test_index_map_values_aliased_map_arg(self) -> None:
        """map_values(@M.0)[0] via `type M = Map<String, Int>`.

        RED on base (E602 drop)."""
        src = """\
type M = Map<String, Int>;

public fn g(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @M = map_insert(map_new(), "k", 77);
  map_values(@M.0)[0]
}
"""
        assert _run(src, fn="g") == 77

    def test_index_set_to_array_aliased_set_arg(self) -> None:
        """set_to_array(@S.0)[0] via `type S = Set<Int>`.

        RED on base (E602 drop)."""
        src = """\
type S = Set<Int>;

public fn g(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @S = set_add(set_new(), 88);
  set_to_array(@S.0)[0]
}
"""
        assert _run(src, fn="g") == 88

    # ---- Class 3: closure-return-derived ----------------------------------

    def test_index_array_map_int(self) -> None:
        """array_map([1, 2, 3], |x| x + 100)[1] -> 102.  The closure returns a
        value DIFFERENT from its input element; the _string variant proves the
        element TYPE (not just value) comes from the closure return."""
        src = """
public fn g(-> @Int) requires(true) ensures(true) effects(pure) {
  array_map([1, 2, 3], fn(@Int -> @Int) effects(pure) { @Int.0 + 100 })[1]
}
"""
        assert _run(src, fn="g") == 102

    def test_index_array_map_string(self) -> None:
        """Int array mapped to String elements — proves the element type comes
        from the closure's RETURN (String), not the input element (Int).  If
        inference took the input's Int, the pair-typed String load would be
        mistranslated.  map -> ["1000", "2000", "3000"]; [2] = "3000" (len 4)."""
        src = """
public fn g(-> @Int) requires(true) ensures(true) effects(pure) {
  string_length(
    array_map([1, 2, 3], fn(@Int -> @String) effects(pure) {
      int_to_string(@Int.0 * 1000)
    })[2]
  )
}
"""
        assert _run(src, fn="g") == 4

    def test_index_array_mapi_int(self) -> None:
        """array_mapi([10, 20, 30], |x, i| x + i)[2] -> 32 (30 + 2)."""
        src = """
public fn g(-> @Int) requires(true) ensures(true) effects(pure) {
  array_mapi([10, 20, 30], fn(@Int, @Nat -> @Int) effects(pure) {
    @Int.0 + nat_to_int(@Nat.0)
  })[2]
}
"""
        assert _run(src, fn="g") == 32

    def test_index_array_mapi_string(self) -> None:
        """array_mapi mapped to String elements — element type from the closure
        return (String), not the input (Int).  mapi -> ["100", "201", "302"];
        [2] = "302" (len 3)."""
        src = """
public fn g(-> @Int) requires(true) ensures(true) effects(pure) {
  string_length(
    array_mapi([1, 2, 3], fn(@Int, @Nat -> @String) effects(pure) {
      int_to_string(@Int.0 * 100 + nat_to_int(@Nat.0))
    })[2]
  )
}
"""
        assert _run(src, fn="g") == 3

    # ---- Structural: no [E602] drop, one per mechanism class --------------

    def test_index_class1_no_e602_drop(self) -> None:
        """array_reverse(...)[i] must not drop the function via [E602] (#1051)."""
        src = """
public fn g(-> @Int) requires(true) ensures(true) effects(pure) {
  array_reverse([10, 20, 30])[0]
}
"""
        result = _compile_ok(src)
        assert not any(d.error_code == "E602" for d in result.diagnostics), \
            "array_reverse(...)[i] should not drop the function via E602"

    def test_index_class2_no_e602_drop(self) -> None:
        """map_values(m)[i] must not drop the function via [E602] (#1051)."""
        src = """
public fn g(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Map<String, Int> = map_insert(map_new(), "k", 77);
  map_values(@Map<String, Int>.0)[0]
}
"""
        result = _compile_ok(src)
        assert not any(d.error_code == "E602" for d in result.diagnostics), \
            "map_values(m)[i] should not drop the function via E602"

    def test_index_class3_no_e602_drop(self) -> None:
        """array_map(xs, f)[i] must not drop the function via [E602] (#1051)."""
        src = """
public fn g(-> @Int) requires(true) ensures(true) effects(pure) {
  array_map([1, 2, 3], fn(@Int -> @Int) effects(pure) { @Int.0 + 100 })[1]
}
"""
        result = _compile_ok(src)
        assert not any(d.error_code == "E602" for d in result.diagnostics), \
            "array_map(xs, f)[i] should not drop the function via E602"

    # ---- Controls: let-bound form works independently of the FnCall fix ---

    def test_index_array_reverse_let_bound_control(self) -> None:
        """Class 1 control: let-bound reverse result resolves via the SlotRef
        arm and stays green independently of the FnCall-arm fix."""
        src = """
public fn g(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Array<Int> = array_reverse([10, 20, 30]);
  @Array<Int>.0[0]
}
"""
        assert _run(src, fn="g") == 30

    def test_index_map_values_let_bound_control(self) -> None:
        """Class 2 control: let-bound map_values result resolves via the SlotRef
        arm."""
        src = """
public fn g(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Map<String, Int> = map_insert(map_new(), "k", 77);
  let @Array<Int> = map_values(@Map<String, Int>.0);
  @Array<Int>.0[0]
}
"""
        assert _run(src, fn="g") == 77

    def test_index_array_map_let_bound_control(self) -> None:
        """Class 3 control: let-bound array_map result resolves via the SlotRef
        arm."""
        src = """
public fn g(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Array<Int> = array_map([1, 2, 3], fn(@Int -> @Int) effects(pure) { @Int.0 + 100 });
  @Array<Int>.0[1]
}
"""
        assert _run(src, fn="g") == 102


class TestFlattenInlineNestedLiteral:
    """array_flatten of an INLINE nested array literal as a direct call argument
    — `array_flatten([[10, 20], [30, 40]])` — must recover the inner element
    type T from the literal and compile, not drop the enclosing function via
    [E602] (#1052).

    Pre-fix, `_translate_array_flatten` recovered T only from a `SlotRef`
    `@Array<Array<T>>` argument; an inline `[[..], [..]]` literal fell through to
    the loud skip.  T is now taken from the inner literal's element type — the
    same `_infer_array_element_type` recovery a nested literal in a `let`
    position already uses.  The let-bound-argument control (flatten of a SlotRef)
    always worked and is pinned below.
    """

    def test_flatten_inline_nested_int_literal(self) -> None:
        """array_flatten([[10, 20], [30, 40]])[0] -> 10.  Value 10 (not 0) so a
        mis-inferred element type cannot coincide with a zero default."""
        src = """
public fn g(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Array<Int> = array_flatten([[10, 20], [30, 40]]);
  @Array<Int>.0[0]
}
"""
        assert _run(src, fn="g") == 10

    def test_flatten_inline_nested_int_literal_cross_inner(self) -> None:
        """... [2] -> 30 — the first element of the SECOND inner array, proving
        both inners flattened contiguously in order (not just inner 0 read)."""
        src = """
public fn g(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Array<Int> = array_flatten([[10, 20], [30, 40]]);
  @Array<Int>.0[2]
}
"""
        assert _run(src, fn="g") == 30

    def test_flatten_inline_nested_string_literal(self) -> None:
        """Array<String> inner variant — pair (ptr, len) elements resolve through
        the recovered element type.  flatten([["ab","cd"],["ef","gh"]]) ->
        ["ab","cd","ef","gh"]; [2] = "ef" (string_length 2)."""
        src = """
public fn g(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Array<String> = array_flatten([["ab", "cd"], ["ef", "gh"]]);
  string_length(@Array<String>.0[2])
}
"""
        assert _run(src, fn="g") == 2

    def test_flatten_empty_inline_literal_stays_loud_skip(self) -> None:
        """Honest boundary (#1052): an EMPTY inline literal (`array_flatten([])`)
        carries no element-type information — T is genuinely unrecoverable from
        the argument — so the enclosing function keeps the LOUD [E602] skip
        rather than guessing T or silently mis-compiling.  (A non-empty inline
        literal resolves — see the tests above.)"""
        src = """
public fn g(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Array<Int> = array_flatten([]);
  array_length(@Array<Int>.0)
}
"""
        result = _compile_ok(src)
        assert "g" not in result.exports, \
            "empty inline literal is unresolvable — must drop, not compile wrong"
        assert any(d.error_code == "E602" for d in result.diagnostics), \
            "the unresolvable empty-literal shape must keep the loud E602 skip"

    def test_flatten_inline_literal_no_e602_drop(self) -> None:
        """Structural: the inline-literal flatten must not drop the fn via
        [E602] (#1052)."""
        src = """
public fn g(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Array<Int> = array_flatten([[10, 20], [30, 40]]);
  @Array<Int>.0[0]
}
"""
        result = _compile_ok(src)
        assert not any(d.error_code == "E602" for d in result.diagnostics), \
            "array_flatten of an inline nested literal should not drop via E602"

    def test_flatten_letbound_arg_control(self) -> None:
        """Control: flatten of a let-bound `@Array<Array<Int>>` SlotRef argument
        resolves via the SlotRef arm and stays green independently of the
        ArrayLit-arm fix."""
        src = """
public fn g(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Array<Array<Int>> = [[10, 20], [30, 40]];
  let @Array<Int> = array_flatten(@Array<Array<Int>>.0);
  @Array<Int>.0[0]
}
"""
        assert _run(src, fn="g") == 10


class TestNestedTypevarBuiltinArg:
    """A type-variable-element Array builtin nested as ANOTHER builtin's call
    argument — `array_reverse(array_flatten(x))` — must derive the inner call's
    element type on the call-emission inference path and compile, not drop via
    [E602] (#1053).

    This is the call-emission sibling of #1051 (which fixed the *index* path).
    The outer combinator's element-type probe (`_array_elem_triad_or_skip` ->
    `_infer_concat_elem_type`) previously dropped the inner `<Int>` layer of a
    `SlotRef` `@Array<Array<Int>>` (returned bare "Array"), so an inner
    `array_flatten` could not be unwrapped and the outer call kept the loud skip.
    Inference now falls back to the shared #1051 `_builtin_call_ret_named_type`
    derivation.  The converse nesting — a builtin call as `array_flatten`'s own
    argument (`array_flatten(array_map(...))`) — resolves T the same way in
    `_translate_array_flatten`.

    Consultor-resolvable inner calls (`array_reverse(array_concat(a, b))`) and
    typevar-in-typevar (`array_reverse(array_reverse(x))`) already worked and are
    pinned as passing controls, alongside the let-bound single-call controls.
    """

    # ---- The fixed shapes -------------------------------------------------

    def test_reverse_of_flatten(self) -> None:
        """array_reverse(array_flatten([[10,20],[30,40]]))[0] -> 40.
        flatten -> [10,20,30,40]; reverse -> [40,30,20,10]; [0] = 40."""
        src = """
public fn g(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Array<Array<Int>> = [[10, 20], [30, 40]];
  let @Array<Int> = array_reverse(array_flatten(@Array<Array<Int>>.0));
  @Array<Int>.0[0]
}
"""
        assert _run(src, fn="g") == 40

    def test_reverse_of_flatten_mid(self) -> None:
        """... [1] -> 30 — proves the reversed order across the flatten boundary
        (not just the head)."""
        src = """
public fn g(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Array<Array<Int>> = [[10, 20], [30, 40]];
  let @Array<Int> = array_reverse(array_flatten(@Array<Array<Int>>.0));
  @Array<Int>.0[1]
}
"""
        assert _run(src, fn="g") == 30

    def test_sort_by_of_flatten(self) -> None:
        """One more nesting pair: array_sort_by(array_flatten(x), asc)[0] -> 10.
        flatten([[30,10],[40,20]]) -> [30,10,40,20]; sorted asc -> [10,20,30,40];
        [0] = 10."""
        src = """
public fn g(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Array<Array<Int>> = [[30, 10], [40, 20]];
  let @Array<Int> = array_sort_by(
    array_flatten(@Array<Array<Int>>.0),
    fn(@Int, @Int -> @Ordering) effects(pure) {
      if @Int.1 < @Int.0 then { Less } else {
        if @Int.1 > @Int.0 then { Greater } else { Equal }
      }
    }
  );
  @Array<Int>.0[0]
}
"""
        assert _run(src, fn="g") == 10

    def test_flatten_of_map_converse(self) -> None:
        """Converse nesting — a typevar builtin (array_map) as array_flatten's own
        argument: array_flatten(array_map([1,2,3], |x| [x, x+100])).
        map -> [[1,101],[2,102],[3,103]]; flatten -> [1,101,2,102,3,103];
        [3] = 102."""
        src = """
public fn g(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Array<Int> = array_flatten(
    array_map([1, 2, 3], fn(@Int -> @Array<Int>) effects(pure) {
      [@Int.0, @Int.0 + 100]
    })
  );
  @Array<Int>.0[3]
}
"""
        assert _run(src, fn="g") == 102

    def test_nested_typevar_arg_no_e602_drop(self) -> None:
        """Structural: reverse(flatten(...)) must not drop the fn via [E602]."""
        src = """
public fn g(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Array<Array<Int>> = [[10, 20], [30, 40]];
  let @Array<Int> = array_reverse(array_flatten(@Array<Array<Int>>.0));
  @Array<Int>.0[0]
}
"""
        result = _compile_ok(src)
        assert not any(d.error_code == "E602" for d in result.diagnostics), \
            "reverse(flatten(...)) should not drop the function via E602"

    # ---- Pins: shapes that already resolved (must stay green) -------------

    def test_reverse_of_concat_consultor_pin(self) -> None:
        """Consultor-inside-typevar pin: array_reverse's inner arg is a
        consultor-resolvable array_concat, so it resolved before #1053 too.
        concat -> [10,20,30,40]; reverse -> [40,30,20,10]; [0] = 40."""
        src = """
public fn g(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Array<Int> = array_reverse(array_concat([10, 20], [30, 40]));
  @Array<Int>.0[0]
}
"""
        assert _run(src, fn="g") == 40

    def test_reverse_of_reverse_typevar_pin(self) -> None:
        """Typevar-in-typevar pin: array_reverse(array_reverse([10,20,30])) — the
        inner array_reverse forwards its ArrayLit-arg element type, so this
        resolved before #1053 too.  reverse twice = identity; [0] = 10."""
        src = """
public fn g(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Array<Int> = array_reverse(array_reverse([10, 20, 30]));
  @Array<Int>.0[0]
}
"""
        assert _run(src, fn="g") == 10

    def test_block_wrapped_nested_reverse_direct_index(self) -> None:
        """A Block-wrapped nested builtin argument resolves via its tail
        expression on both the emission-side element inference and the
        index-side deep resolution (PR #1096 review).  reverse twice =
        identity; [0] = 10."""
        src = """
public fn g(-> @Int) requires(true) ensures(true) effects(pure) {
  array_reverse({ array_reverse([10, 20]) })[0]
}
"""
        assert _run(src, fn="g") == 10

    def test_reverse_single_letbound_control(self) -> None:
        """Control: a single let-bound array_reverse resolves via the SlotRef arm
        and stays green independently of the nested-arg fix.  [0] = 30."""
        src = """
public fn g(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Array<Int> = array_reverse([10, 20, 30]);
  @Array<Int>.0[0]
}
"""
        assert _run(src, fn="g") == 30

    def test_flatten_single_letbound_control(self) -> None:
        """Control: a single let-bound array_flatten of a SlotRef resolves via the
        SlotRef arm.  [0] = 10."""
        src = """
public fn g(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Array<Array<Int>> = [[10, 20], [30, 40]];
  let @Array<Int> = array_flatten(@Array<Array<Int>>.0);
  @Array<Int>.0[0]
}
"""
        assert _run(src, fn="g") == 10


class TestAliasSpelledArgCallEmission:
    """An alias-spelled array argument at a builtin's CALL emission —
    `type Grid = Array<Array<Int>>; array_flatten(@Grid.0)` /
    `type Row = Array<Int>; array_reverse(@Row.0)` — must canonicalize the
    alias to its target's compound spelling and compile, not drop via [E602]
    (#1053 alias extension; the call-emission dual of #1055's index-side fix).

    #1055 taught the shared `_named_type_from_arg_info` rebuilder to
    canonicalize a bare alias slot name (the #1037 walk), which fixed the
    INDEX-side derivations; the array builtins' own emission probes
    (`_infer_concat_elem_type`'s SlotRef arm, `_translate_array_flatten`'s
    T-recovery) still saw the bare alias name and dropped — flatten at its
    input-shape gate, reverse/sort_by at the element-type triad.  Both now
    fall back to the same canonicalizing rebuilder.  Direct spellings are
    pinned by the sibling classes' controls.
    """

    def test_flatten_aliased_grid_arg(self) -> None:
        """array_flatten(@Grid.0) via `type Grid = Array<Array<Int>>`,
        let-bound result.  [0] = 10."""
        src = """
type Grid = Array<Array<Int>>;

public fn g(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Grid = [[10, 20], [30, 40]];
  let @Array<Int> = array_flatten(@Grid.0);
  @Array<Int>.0[0]
}
"""
        assert _run(src, fn="g") == 10

    def test_flatten_aliased_grid_arg_indexed(self) -> None:
        """array_flatten(@Grid.0)[2] -> 30 — the first element of the SECOND
        inner array, proving contiguous flattening through the alias (and the
        index side resolving the same call, post-#1055)."""
        src = """
type Grid = Array<Array<Int>>;

public fn g(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Grid = [[10, 20], [30, 40]];
  array_flatten(@Grid.0)[2]
}
"""
        assert _run(src, fn="g") == 30

    def test_reverse_aliased_row_arg(self) -> None:
        """array_reverse(@Row.0)[0] via `type Row = Array<Int>` -> 30."""
        src = """
type Row = Array<Int>;

public fn g(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Row = [10, 20, 30];
  array_reverse(@Row.0)[0]
}
"""
        assert _run(src, fn="g") == 30

    def test_reverse_aliased_string_row_arg(self) -> None:
        """Array<String> alias variant — pair (ptr, len) elements resolve
        through the canonicalized element type.  reverse of ["a","bb","ccc"]
        -> ["ccc","bb","a"]; [0] = "ccc" (length 3)."""
        src = """
type Names = Array<String>;

public fn g(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Names = ["a", "bb", "ccc"];
  string_length(array_reverse(@Names.0)[0])
}
"""
        assert _run(src, fn="g") == 3

    def test_sort_by_aliased_row_arg(self) -> None:
        """array_sort_by(@Row.0, asc)[0] via the alias -> 10 (the triad is
        shared by every array combinator, so sort_by rides the same fix)."""
        src = """
type Row = Array<Int>;

public fn g(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Row = [30, 10, 20];
  array_sort_by(@Row.0, fn(@Int, @Int -> @Ordering) effects(pure) {
    if @Int.1 < @Int.0 then { Less } else {
      if @Int.1 > @Int.0 then { Greater } else { Equal }
    }
  })[0]
}
"""
        assert _run(src, fn="g") == 10


class TestContainerArgEmissionTag:
    """Aliased or user-fn Map/Set arguments at the container builtins' CALL
    emission must resolve K/V/T for the host-import tag — not silently fall
    to the `"b"` (i32) tag and return WRONG VALUES (#1053 container
    extension).

    The emission-side inference helpers (`_infer_map_key_from_map_arg`,
    `_infer_map_value_from_map_arg`, `_infer_set_elem_from_set_arg`) only
    understood direct `@Map<K, V>` / `@Set<T>` slots and map-builtin chains;
    an alias-spelled slot or a user-fn call argument returned None, and
    `_map_wasm_tag(None)` deliberately falls through to `"b"` (the
    empty-collection escape hatch).  The mis-tagged import then decoded a
    stored i64 value as i32 (silent truncation) or a String key's ptr field
    as a scalar (garbage), and the host wrote a 4-byte-stride array the
    guest reads at 8-byte stride — check-green, verify-green, WRONG value
    (not even an [E602] drop).  All three helpers now consult the shared
    canonicalizing rebuilder first.  Values are chosen > 2^32 so a
    truncating mis-tag CANNOT pass by fresh-heap luck.
    """

    # ---- Aliased container arguments ---------------------------------------

    def test_map_values_aliased_arg_emission_big_value(self) -> None:
        """map_values(@M.0) emission via `type M = Map<String, Int>` with a
        value above 2^32 (8589934597 = 2^33 + 5).  The mis-tagged `$vb`
        import truncated it to 5."""
        src = """
type M = Map<String, Int>;

public fn g(-> @Int) requires(true) ensures(true) effects(pure) {
  let @M = map_insert(map_new(), "k", 8589934597);
  let @Array<Int> = map_values(@M.0);
  @Array<Int>.0[0]
}
"""
        assert _run(src, fn="g") == 8589934597

    def test_map_keys_aliased_arg_emission_string(self) -> None:
        """map_keys(@M.0) emission via the alias — String keys under the
        mis-tagged `$kb` import came back as garbage (length 0)."""
        src = """
type M = Map<String, Int>;

public fn g(-> @Int) requires(true) ensures(true) effects(pure) {
  let @M = map_insert(map_new(), "abcde", 99);
  let @Array<String> = map_keys(@M.0);
  string_length(@Array<String>.0[0])
}
"""
        assert _run(src, fn="g") == 5

    def test_map_get_aliased_arg_emission_big_value(self) -> None:
        """map_get(@M.0, k) shares `_infer_map_value_from_map_arg` for the
        Option<V> host construction — the aliased arg mis-tagged it the same
        way."""
        src = """
type M = Map<String, Int>;

public fn g(-> @Int) requires(true) ensures(true) effects(pure) {
  let @M = map_insert(map_new(), "k", 8589934597);
  option_unwrap_or(map_get(@M.0, "k"), 0)
}
"""
        assert _run(src, fn="g") == 8589934597

    def test_set_to_array_aliased_arg_emission_big_value(self) -> None:
        """set_to_array(@S.0) emission via `type S = Set<Int>` with an element
        above 2^32 (8589934600 = 2^33 + 8) — the mis-tagged `$eb` import
        truncated it to 8."""
        src = """
type S = Set<Int>;

public fn g(-> @Int) requires(true) ensures(true) effects(pure) {
  let @S = set_add(set_new(), 8589934600);
  let @Array<Int> = set_to_array(@S.0);
  @Array<Int>.0[0]
}
"""
        assert _run(src, fn="g") == 8589934600

    # ---- User-fn container arguments ---------------------------------------

    def test_map_keys_user_fn_arg_emission(self) -> None:
        """map_keys(mkm()) — a user fn returning Map<String, Int> as the
        argument.  The emission had no user-fn arm; String keys came back as
        garbage (length 0) under the `$kb` mis-tag."""
        src = """
fn mkm(-> @Map<String, Int>) requires(true) ensures(true) effects(pure) {
  map_insert(map_new(), "abcde", 99)
}

public fn g(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Array<String> = map_keys(mkm());
  string_length(@Array<String>.0[0])
}
"""
        assert _run(src, fn="g") == 5

    def test_map_keys_user_fn_with_arg_emission(self) -> None:
        """Same shape with a PARAMETERIZED user fn (`mkm2(1)`) — the key
        helper's blind args[0] recursion used to swallow this shape before
        any declared-return consultation."""
        src = """
fn mkm2(@Int -> @Map<String, Int>) requires(true) ensures(true) effects(pure) {
  map_insert(map_new(), "abcde", @Int.0)
}

public fn g(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Array<String> = map_keys(mkm2(1));
  string_length(@Array<String>.0[0])
}
"""
        assert _run(src, fn="g") == 5

    def test_map_values_user_fn_arg_emission_big_value(self) -> None:
        """map_values(mkm()) with a value above 2^32 — truncated to 7 under
        the mis-tag."""
        src = """
fn mkm(-> @Map<String, Int>) requires(true) ensures(true) effects(pure) {
  map_insert(map_new(), "k", 8589934599)
}

public fn g(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Array<Int> = map_values(mkm());
  @Array<Int>.0[0]
}
"""
        assert _run(src, fn="g") == 8589934599

    def test_set_to_array_user_fn_arg_emission_big_value(self) -> None:
        """set_to_array(mks()) — user fn returning Set<Int>, element above
        2^32."""
        src = """
fn mks(-> @Set<Int>) requires(true) ensures(true) effects(pure) {
  set_add(set_new(), 8589934600)
}

public fn g(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Array<Int> = set_to_array(mks());
  @Array<Int>.0[0]
}
"""
        assert _run(src, fn="g") == 8589934600

    # ---- Bare-alias user-fn returns (#1071) ---------------------------------

    def test_map_values_bare_alias_return_big_value(self) -> None:
        """map_values(mkm()) where mkm's declared return is the BARE alias
        `@M` (`type M = Map<String, Int>`) — the consultor's user-fn arm
        only reported parameterized returns, so the bare alias exited
        unresolved and the value truncated to 7 under the `$vb` mis-tag
        (#1071; pre-existing on main)."""
        src = """
type M = Map<String, Int>;

fn mkm(-> @M) requires(true) ensures(true) effects(pure) {
  map_insert(map_new(), "abcde", 8589934599)
}

public fn g(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Array<Int> = map_values(mkm());
  @Array<Int>.0[0]
}
"""
        assert _run(src, fn="g") == 8589934599

    def test_map_keys_bare_alias_return_string(self) -> None:
        """map_keys(mkm()) with the bare-alias return — String keys came
        back garbled (length 0) under the `$kb` mis-tag (#1071)."""
        src = """
type M = Map<String, Int>;

fn mkm(-> @M) requires(true) ensures(true) effects(pure) {
  map_insert(map_new(), "abcde", 99)
}

public fn g(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Array<String> = map_keys(mkm());
  string_length(@Array<String>.0[0])
}
"""
        assert _run(src, fn="g") == 5

    def test_map_get_bare_alias_return_big_value(self) -> None:
        """map_get(mkm(), k) with the bare-alias return — the Option<V>
        construction mis-tagged the same way (#1071)."""
        src = """
type M = Map<String, Int>;

fn mkm(-> @M) requires(true) ensures(true) effects(pure) {
  map_insert(map_new(), "abcde", 8589934599)
}

public fn g(-> @Int) requires(true) ensures(true) effects(pure) {
  option_unwrap_or(map_get(mkm(), "abcde"), 0)
}
"""
        assert _run(src, fn="g") == 8589934599

    def test_set_to_array_bare_alias_return_big_value(self) -> None:
        """set_to_array(mks()) where mks returns the bare alias `@S`
        (`type S = Set<Int>`) — truncated to 8 pre-fix (#1071)."""
        src = """
type S = Set<Int>;

fn mks(-> @S) requires(true) ensures(true) effects(pure) {
  set_add(set_new(), 8589934600)
}

public fn g(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Array<Int> = set_to_array(mks());
  @Array<Int>.0[0]
}
"""
        assert _run(src, fn="g") == 8589934600

    def test_map_values_block_wrapped_arg_big_value(self) -> None:
        """A Block-wrapped container argument (`map_values({ @M.0 })`)
        unwraps to its tail expression for the tag inference — truncated to
        5 pre-fix (#1071)."""
        src = """
type M = Map<String, Int>;

public fn g(-> @Int) requires(true) ensures(true) effects(pure) {
  let @M = map_insert(map_new(), "k", 8589934597);
  let @Array<Int> = map_values({ @M.0 });
  @Array<Int>.0[0]
}
"""
        assert _run(src, fn="g") == 8589934597

    # ---- Controls -----------------------------------------------------------

    def test_map_values_direct_arg_big_value_control(self) -> None:
        """Direct `@Map<String, Int>.0` spelling with the same big value —
        correctly tagged `$vi` before and after the fix."""
        src = """
public fn g(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Map<String, Int> = map_insert(map_new(), "k", 8589934597);
  let @Array<Int> = map_values(@Map<String, Int>.0);
  @Array<Int>.0[0]
}
"""
        assert _run(src, fn="g") == 8589934597

    def test_map_keys_empty_map_still_compiles(self) -> None:
        """The genuinely-unknown empty-collection shape keeps its permissive
        `"b"` fall-through: map_keys(map_new()) compiles and returns an empty
        array (no element value ever flows through the import)."""
        src = """
public fn g(-> @Int) requires(true) ensures(true) effects(pure) {
  array_length(map_keys(map_new()))
}
"""
        assert _run(src, fn="g") == 0


class TestUserFnArrayArg:
    """A user fn returning Array<T> as a type-variable builtin's argument
    (#1053 user-fn extension).

    `array_reverse(mk())` / `array_sort_by(mk(), cmp)` resolve through the
    #1053 emission fallback's `_builtin_call_ret_named_type` chain — the
    shared rebuilder reads a registered non-generic user fn's declared
    return type — so the flat-return shapes are pinned GREEN here (they
    rode the #1053 fix; no further change).  A NESTED return
    (`mkn() -> Array<Array<Int>>`) reached the rebuilder as
    `("Array", (None,))` — the consultor's user-fn arm deliberately blanks
    nested type-arg positions to stay in clone-name-discovery lockstep — so
    `array_flatten(mkn())` dropped at its input-shape gate; the rebuilder
    now recovers the declared return TypeExpr directly (full nesting, off
    the consultor) and flatten unwraps it.
    """

    def test_reverse_user_fn_arg(self) -> None:
        """array_reverse(mk())[0] -> 30 (pin: resolved by the #1053 fallback)."""
        src = """
fn mk(-> @Array<Int>) requires(true) ensures(true) effects(pure) {
  [10, 20, 30]
}

public fn g(-> @Int) requires(true) ensures(true) effects(pure) {
  array_reverse(mk())[0]
}
"""
        assert _run(src, fn="g") == 30

    def test_reverse_user_fn_arg_letbound(self) -> None:
        """Let-bound variant of the same pin."""
        src = """
fn mk(-> @Array<Int>) requires(true) ensures(true) effects(pure) {
  [10, 20, 30]
}

public fn g(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Array<Int> = array_reverse(mk());
  @Array<Int>.0[0]
}
"""
        assert _run(src, fn="g") == 30

    def test_sort_by_user_fn_arg(self) -> None:
        """array_sort_by(mk(), asc)[0] -> 10 (pin)."""
        src = """
fn mk(-> @Array<Int>) requires(true) ensures(true) effects(pure) {
  [30, 10, 20]
}

public fn g(-> @Int) requires(true) ensures(true) effects(pure) {
  array_sort_by(mk(), fn(@Int, @Int -> @Ordering) effects(pure) {
    if @Int.1 < @Int.0 then { Less } else {
      if @Int.1 > @Int.0 then { Greater } else { Equal }
    }
  })[0]
}
"""
        assert _run(src, fn="g") == 10

    def test_flatten_user_fn_nested_return(self) -> None:
        """array_flatten(mkn()) — user fn returning Array<Array<Int>>.
        Dropped at the input-shape gate before the nested-return recovery."""
        src = """
fn mkn(-> @Array<Array<Int>>) requires(true) ensures(true) effects(pure) {
  [[10, 20], [30, 40]]
}

public fn g(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Array<Int> = array_flatten(mkn());
  @Array<Int>.0[0]
}
"""
        assert _run(src, fn="g") == 10

    def test_flatten_user_fn_nested_return_indexed(self) -> None:
        """array_flatten(mkn())[2] -> 30 — the indexed form exercises the
        index-side derivation through the same nested-return recovery."""
        src = """
fn mkn(-> @Array<Array<Int>>) requires(true) ensures(true) effects(pure) {
  [[10, 20], [30, 40]]
}

public fn g(-> @Int) requires(true) ensures(true) effects(pure) {
  array_flatten(mkn())[2]
}
"""
        assert _run(src, fn="g") == 30


class TestNestedAliasElemClassification:
    """An ALIAS-SPELLED inner element name (`type Row = Array<Int>` as the
    element of an outer array) must be canonicalized before the element
    size/pair classification at the array builtins' emission — not classified
    as a 4-byte scalar where the real element is an 8-byte (ptr, len) pair
    (#1067).

    `_infer_concat_elem_type` (and flatten's own T-recovery) returned the
    bare alias name ("Row"); `_element_mem_size("Row")` fell to the 4-byte
    ADT default, so `array_reverse(@Grid.0)` (via `type Grid = Array<Row>`)
    copied half of each pair — check-green, verify-green, garbage values
    (`[0][0]` returned 4626322722586886145, `array_length([0])` returned
    81948) — and `array_concat` / depth-2 `array_flatten` read past their
    allocations (unreachable traps).  Element names now canonicalize to the
    target's compound spelling at the single inference exit (plus flatten's
    gate and T-recovery), classifying as pairs.  The direct spellings
    `@Array<Row>` / `@Array<Array<Row>>` mis-classified identically through
    the pre-#1053 direct arm — latent on `main`, where these shapes still
    E602-dropped for unrelated reasons; this branch's derivations made them
    reachable, so both spellings are pinned here.
    """

    def test_reverse_aliased_grid_nested_read(self) -> None:
        """array_reverse(@Grid.0)[0][0] -> 30 (was garbage)."""
        src = """
type Row = Array<Int>;
type Grid = Array<Row>;

public fn g(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Grid = [[10, 20], [30, 40]];
  array_reverse(@Grid.0)[0][0]
}
"""
        assert _run(src, fn="g") == 30

    def test_reverse_aliased_grid_inner_length(self) -> None:
        """array_length(array_reverse(@Grid.0)[0]) -> 2 (was garbage)."""
        src = """
type Row = Array<Int>;
type Grid = Array<Row>;

public fn g(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Grid = [[10, 20], [30, 40]];
  array_length(array_reverse(@Grid.0)[0])
}
"""
        assert _run(src, fn="g") == 2

    def test_reverse_direct_array_of_row_twin(self) -> None:
        """Direct-spelling twin: array_reverse(@Array<Row>.0)[0][0] -> 30 —
        the pre-existing direct SlotRef arm returned the same bare "Row"."""
        src = """
type Row = Array<Int>;

public fn g(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Array<Row> = [[10, 20], [30, 40]];
  array_reverse(@Array<Row>.0)[0][0]
}
"""
        assert _run(src, fn="g") == 30

    def test_concat_aliased_grid_args(self) -> None:
        """array_concat(@Grid.0, @Grid.0)[2][0] -> 10 (read past its
        allocation pre-fix: the 4-byte stride halved the copied bytes)."""
        src = """
type Row = Array<Int>;
type Grid = Array<Row>;

public fn g(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Grid = [[10, 20], [30, 40]];
  array_concat(@Grid.0, @Grid.0)[2][0]
}
"""
        assert _run(src, fn="g") == 10

    def test_flatten_direct_depth2_array_of_row(self) -> None:
        """Depth-2 direct spelling: array_flatten(@Array<Array<Row>>.0)
        yields Array<Row> — pair elements, [1][0] -> 30 (unreachable trap
        pre-fix: T recovered as bare "Row", 4-byte stride read past the
        allocation)."""
        src = """
type Row = Array<Int>;

public fn g(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Array<Array<Row>> = [[[10, 20]], [[30, 40]]];
  array_flatten(@Array<Array<Row>>.0)[1][0]
}
"""
        assert _run(src, fn="g") == 30

    def test_flatten_aliased_grid_outer(self) -> None:
        """array_flatten(@Grid.0)[2] via `Grid = Array<Row>` -> 30 — the
        input-shape gate and T-recovery both see through the alias chain
        (E602-dropped pre-fix)."""
        src = """
type Row = Array<Int>;
type Grid = Array<Row>;

public fn g(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Grid = [[10, 20], [30, 40]];
  array_flatten(@Grid.0)[2]
}
"""
        assert _run(src, fn="g") == 30

    def test_flatten_aliased_row_middle(self) -> None:
        """array_flatten(@Array<Row>.0)[2] — the alias in the MIDDLE layer
        only — -> 30 (E602-dropped pre-fix)."""
        src = """
type Row = Array<Int>;

public fn g(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Array<Row> = [[10, 20], [30, 40]];
  array_flatten(@Array<Row>.0)[2]
}
"""
        assert _run(src, fn="g") == 30

    def test_sort_by_aliased_grid_row_comparator(self) -> None:
        """array_sort_by(@Grid.0, cmp) with a `@Row`-typed comparator sorts
        by inner length — [0][0] -> 30 for the singleton-first ordering.
        Trapped with a wasm backtrace pre-fix (element stride garbage fed the
        comparator)."""
        src = """
type Row = Array<Int>;
type Grid = Array<Row>;

public fn g(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Grid = [[30], [10, 20]];
  array_sort_by(@Grid.0, fn(@Row, @Row -> @Ordering) effects(pure) {
    if array_length(@Row.1) < array_length(@Row.0) then { Less } else {
      if array_length(@Row.1) > array_length(@Row.0) then { Greater } else { Equal }
    }
  })[0][0]
}
"""
        assert _run(src, fn="g") == 30


class TestGenericAliasContainerArg:
    """A GENERIC alias of a container as a user fn's declared return
    (`type MyMap<V> = Map<String, V>; fn mk(-> @MyMap<Int>)`) must
    substitute the alias's type args through its target before any
    derivation consumes them (#1068).

    The class-2 container derivation consumed `("MyMap", ("Int",))`'s type
    args with no container-name check, deriving element `Int` where the
    truth is `String` — `map_keys(mk())[0]` handed a VALIDATION-FAILING
    module to the runner while `vera compile` exited 0.  The shared
    rebuilder now substitutes a generic alias's args through its target
    (`substitute_type_vars`) and canonicalizes; the class-2 arm additionally
    verifies the resolved container IS `Map`/`Set` before reading K/V/T off
    it, so an unresolvable shape stays a loud skip rather than an invalid
    module.
    """

    def test_map_keys_generic_alias_return(self) -> None:
        """string_length(map_keys(mk())[0]) -> 5 via `MyMap<Int>` (invalid
        WASM pre-fix: K derived as Int, module failed validation at run)."""
        src = """
type MyMap<V> = Map<String, V>;

fn mk(-> @MyMap<Int>) requires(true) ensures(true) effects(pure) {
  map_insert(map_new(), "abcde", 99)
}

public fn g(-> @Int) requires(true) ensures(true) effects(pure) {
  string_length(map_keys(mk())[0])
}
"""
        assert _run(src, fn="g") == 5

    def test_map_values_generic_alias_return_big_value(self) -> None:
        """map_values(mk())[0] -> the 2^33+5 value via `MyMap<Int>`
        (E602-dropped pre-fix; the tag and element type both resolve through
        the substituted Map<String, Int>)."""
        src = """
type MyMap<V> = Map<String, V>;

fn mk(-> @MyMap<Int>) requires(true) ensures(true) effects(pure) {
  map_insert(map_new(), "k", 8589934597)
}

public fn g(-> @Int) requires(true) ensures(true) effects(pure) {
  map_values(mk())[0]
}
"""
        assert _run(src, fn="g") == 8589934597


class TestContainerZeroSizeBackstop1075:
    """#1075 codegen backstop: the ANNOTATION-FREE zero-size container
    spelling (`map_values(map_insert(map_new(), "k", ()))`) never passes
    through type resolution — its `Map<String, Unit>` type exists only in
    inference — so the E135 check gate (TestContainerZeroSizeRejected1075
    in test_checker_types.py) cannot fire.  Pre-fix it compiled exit-0 to
    INVALID WASM ("expected i32 but nothing on stack": the Unit value
    pushes no operand where the host import expects an i32).
    `_map_wasm_tag` now returns None for a zero-size type name, so the
    emission takes the loud-skip path — correct-or-loud, never an invalid
    module.
    """

    def test_inline_unit_map_value_loud_skip(self) -> None:
        """The inference-only Map spelling drops loudly via [E602]."""
        src = """
public fn g(-> @Int) requires(true) ensures(true) effects(pure) {
  array_length(map_values(map_insert(map_new(), "k", ())))
}
"""
        result = _compile_ok(src)
        assert "g" not in result.exports, \
            "inline zero-size Map value must drop, not emit invalid WASM"
        assert any(d.error_code == "E602" for d in result.diagnostics), \
            "the zero-size backstop must keep the loud E602 skip"

    def test_inline_unit_set_elem_loud_skip(self) -> None:
        """The inference-only Set spelling drops loudly via [E602]."""
        src = """
public fn g(-> @Int) requires(true) ensures(true) effects(pure) {
  array_length(set_to_array(set_add(set_new(), ())))
}
"""
        result = _compile_ok(src)
        assert "g" not in result.exports, \
            "inline zero-size Set element must drop, not emit invalid WASM"
        assert any(d.error_code == "E602" for d in result.diagnostics), \
            "the zero-size backstop must keep the loud E602 skip"

    def test_empty_map_keys_still_compiles_control(self) -> None:
        """The genuinely element-type-free empty-collection shape keeps its
        permissive fall-through — the backstop keys on a KNOWN zero-size
        name, not on None."""
        src = """
public fn g(-> @Int) requires(true) ensures(true) effects(pure) {
  array_length(map_keys(map_new()))
}
"""
        assert _run(src, fn="g") == 0

    # ---- Recursive erasure (PR #1083 adversarial review) -------------------
    # The first backstop compared the inferred name against two LITERAL
    # strings ("Unit", "Future<Unit>") while the checker gate uses recursive
    # erasure — any indirection defeated it and compiled exit-0 to invalid
    # WASM.  The tag refusal now keys on the same recursive oracle the
    # checker and the zero-size declaration guards use
    # (`_slot_name_erases_to_unit`), and container ENTRY types resolve
    # rebuilder-first so a parameterized user-fn return arrives as its full
    # spelling instead of the #911 bare head ("Future").

    def test_nested_future_map_value_loud_skip(self) -> None:
        """async(async(())) — Future<Future<Unit>> — as a map value (p2)."""
        src = """
public fn g(-> @Int) requires(true) ensures(true) effects(<Async>) {
  map_size(map_insert(map_new(), "k", async(async(()))))
}
"""
        result = _compile_ok(src)
        assert "g" not in result.exports, \
            "nested-Future zero-size map value must drop, not emit invalid WASM"
        assert any(d.error_code == "E602" for d in result.diagnostics)

    def test_nested_future_set_elem_loud_skip(self) -> None:
        """async(async(())) as a set element (p5)."""
        src = """
public fn g(-> @Int) requires(true) ensures(true) effects(<Async>) {
  set_size(set_add(set_new(), async(async(()))))
}
"""
        result = _compile_ok(src)
        assert "g" not in result.exports, \
            "nested-Future zero-size set element must drop, not emit invalid WASM"
        assert any(d.error_code == "E602" for d in result.diagnostics)

    def test_alias_future_unit_return_map_value_loud_skip(self) -> None:
        """A user fn returning `@FU` (`type FU = Future<Unit>`) as a map
        value (p10) — the alias name canonicalizes through the oracle."""
        src = """
type FU = Future<Unit>;

private fn mkfu(@Unit -> @FU)
  requires(true) ensures(true) effects(<Async>)
{ async(()) }

public fn g(-> @Int) requires(true) ensures(true) effects(<Async>) {
  map_size(map_insert(map_new(), "k", mkfu(())))
}
"""
        result = _compile_ok(src)
        assert "g" not in result.exports, \
            "alias-hidden Future<Unit> map value must drop, not emit invalid WASM"
        assert any(d.error_code == "E602" for d in result.diagnostics)

    def test_future_unit_return_map_value_loud_skip(self) -> None:
        """A user fn returning `@Future<Unit>` directly as a map value (p11)
        — the parameterized return must reach the tag as its FULL spelling
        (the rebuilder-first entry typing), not the bare "Future" head."""
        src = """
private fn mk(@Unit -> @Future<Unit>)
  requires(true) ensures(true) effects(<Async>)
{ async(()) }

public fn g(-> @Int) requires(true) ensures(true) effects(<Async>) {
  map_size(map_insert(map_new(), "k", mk(())))
}
"""
        result = _compile_ok(src)
        assert "g" not in result.exports, \
            "Future<Unit>-returning map value must drop, not emit invalid WASM"
        assert any(d.error_code == "E602" for d in result.diagnostics)

    def test_async_task_alias_map_value_loud_skip(self) -> None:
        """The natural shape (p12): a map of `async(IO.print(...))` tasks
        behind `type Task = Future<Unit>`."""
        src = """
type Task = Future<Unit>;

private fn spawn(@String -> @Task)
  requires(true) ensures(true) effects(<Async, IO>)
{ async(IO.print(@String.0)) }

public fn g(-> @Int) requires(true) ensures(true) effects(<Async, IO>) {
  map_size(map_insert(map_new(), "k", spawn("hi")))
}
"""
        result = _compile_ok(src)
        assert "g" not in result.exports, \
            "Task-alias async map value must drop, not emit invalid WASM"
        assert any(d.error_code == "E602" for d in result.diagnostics)

    def test_unit_return_map_value_loud_skip_pin(self) -> None:
        """p13 pin: a pure fn returning bare `@Unit` as a map value keeps
        dropping loudly (already caught pre-review; must not regress)."""
        src = """
private fn nop(@Int -> @Unit)
  requires(true) ensures(true) effects(pure)
{ () }

public fn g(-> @Int) requires(true) ensures(true) effects(pure) {
  map_size(map_insert(map_new(), "k", nop(1)))
}
"""
        result = _compile_ok(src)
        assert "g" not in result.exports
        assert any(d.error_code == "E602" for d in result.diagnostics)

    def test_alias_array_return_map_value_loud_skip(self) -> None:
        """The Array dual through the same entry resolver: a user fn
        returning `@Names` (`type Names = Array<String>`) as a map value
        reaches the tag as `Array<String>` and takes the existing
        Array-reject loud skip — the raw alias name previously fell through
        to the "b" tag (one i32 slot for a two-slot pair)."""
        src = """
type Names = Array<String>;

private fn mkn(@Unit -> @Names)
  requires(true) ensures(true) effects(pure)
{ ["a", "b"] }

public fn g(-> @Int) requires(true) ensures(true) effects(pure) {
  map_size(map_insert(map_new(), "k", mkn(())))
}
"""
        result = _compile_ok(src)
        assert "g" not in result.exports, \
            "alias-of-Array map value must drop, not mis-tag as a scalar"
        assert any(d.error_code == "E602" for d in result.diagnostics)


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


class TestFutureElementArrays1045:
    """#1045: `Array<Future<T>>` element representation.

    `Future<T>` is representation-transparent (#841), so an array whose
    element type is `Future<T>` must size/load/store its elements at the
    payload T's width.  Pre-fix the five module-level element helpers in
    `vera/wasm/helpers.py` name-matched only "String" / "Array" / the
    scalar dict with no Future strip, so `Array<Future<Int>>` sized each
    element as a 4-byte i32 and stored the i64 payload with `i32.store`
    (trap "expected i32, found i64"), while `Array<Future<String>>` (a
    pair payload) was treated as a single i32 and left the len half on
    the stack ("values remaining on stack").  The fix strips `Future<…>`
    at the top of each helper via a shared `_strip_future`.
    """

    def test_array_future_int_length(self) -> None:
        """`array_length(Array<Future<Int>>)` — length only.

        RED before the fix: laying out the i64 payloads through the i32
        element path trapped at WASM validation ("expected i32, found
        i64") before the length could be read.
        """
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(<Async>) {
  let @Future<Int> = async(10);
  let @Future<Int> = async(20);
  let @Array<Future<Int>> = [@Future<Int>.1, @Future<Int>.0];
  array_length(@Array<Future<Int>>.0)
}
"""
        assert _run(src, "f") == 2

    def test_array_future_int_element_readback(self) -> None:
        """Index an `Array<Future<Int>>` element and await it.

        The distinguishing value 4242 cannot coincide with the i32
        default path's wrong result.  RED before the fix: the same
        i32/i64 store mismatch traps at validation.
        """
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(<Async>) {
  let @Future<Int> = async(4242);
  let @Future<Int> = async(1717);
  let @Array<Future<Int>> = [@Future<Int>.1, @Future<Int>.0];
  await(@Array<Future<Int>>.0[0])
}
"""
        assert _run(src, "f") == 4242

    def test_array_future_string_length(self) -> None:
        """`array_length(Array<Future<String>>)` — length only.

        RED before the fix: the pair payload was treated as one i32, so
        the array-literal store left values on the stack ("values
        remaining on stack at end of block").
        """
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(<Async>) {
  let @Future<String> = async("hello");
  let @Future<String> = async("worldwide");
  let @Array<Future<String>> = [@Future<String>.1, @Future<String>.0];
  array_length(@Array<Future<String>>.0)
}
"""
        assert _run(src, "f") == 2

    def test_array_future_string_element_readback(self) -> None:
        """Index an `Array<Future<String>>` element, await, measure it.

        Element [1] is "worldwide" (length 9), distinct from element [0]
        "hello" (length 5) and from the 0/1 wrong-value defaults.  RED
        before the fix: the "values remaining on stack" trap.
        """
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(<Async>) {
  let @Future<String> = async("hello");
  let @Future<String> = async("worldwide");
  let @Array<Future<String>> = [@Future<String>.1, @Future<String>.0];
  string_length(await(@Array<Future<String>>.0[1]))
}
"""
        assert _run(src, "f") == 9

    def test_array_plain_string_control(self) -> None:
        """Control: a plain `Array<String>` (no Future) already worked and
        must stay green — pins that the #1045 strip does not regress the
        bare-pair element path.  Two-element array, element [1] length 9."""
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Array<String> = ["hello", "worldwide"];
  string_length(@Array<String>.0[1])
}
"""
        assert _run(src, "f") == 9


class TestFutureCombinatorArrays1057:
    """#1057: array combinators over `Array<Future<T>>` returned garbage.

    `Future<T>` is representation-transparent (#841): its array-element
    width is its payload T's.  The combinators inferred the element type
    through `_infer_concat_elem_type` (or, for `array_append` /
    `array_flatten`, sibling AST walks), all of which returned the bare
    head `"Future"` — the type argument dropped.  `_element_mem_size`
    then could not `_strip_future` a bare `"Future"`, so it collapsed to
    the 4-byte i32 default and the copy loops ran a 4-byte stride over
    8-byte (i64 payload) or two-word (String payload) elements: silent
    wrong values (e.g. concat over `Array<Future<Int>>` returned
    9448928052300 for an expected 1122), a 400-vs-402 half-read for the
    String payload, and an "expected i32, found i64" validation trap for
    `array_append` (whose element local was still typed i32).  All
    check+verify-green.  The fix preserves the full `Future<…>` spelling
    at each inference site and strips the wrapper before choosing the
    append element local's WASM type.

    Every value below is chosen so a packed-half / wrong-stride misread
    cannot coincide with the correct answer.
    """

    def test_array_future_int_concat(self) -> None:
        """`array_concat(Array<Future<Int>>, …)` copies i64 payloads.

        RED before the fix: 4-byte stride over the 8-byte i64 elements
        returned 9448928052300, not 1122 (11*100 + 22)."""
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(<Async>) {
  let @Future<Int> = async(11);
  let @Future<Int> = async(22);
  let @Array<Future<Int>> = [@Future<Int>.1];
  let @Array<Future<Int>> = [@Future<Int>.0];
  let @Array<Future<Int>> = array_concat(@Array<Future<Int>>.1, @Array<Future<Int>>.0);
  await(@Array<Future<Int>>.0[0]) * 100 + await(@Array<Future<Int>>.0[1])
}
"""
        assert _run(src, "f") == 1122

    def test_array_future_int_slice(self) -> None:
        """`array_slice(Array<Future<Int>>, 1, 3)` keeps elements [44, 55].

        RED before the fix: 18897856102400, not 4455 (44*100 + 55)."""
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(<Async>) {
  let @Future<Int> = async(33);
  let @Future<Int> = async(44);
  let @Future<Int> = async(55);
  let @Array<Future<Int>> = [@Future<Int>.2, @Future<Int>.1, @Future<Int>.0];
  let @Array<Future<Int>> = array_slice(@Array<Future<Int>>.0, 1, 3);
  await(@Array<Future<Int>>.0[0]) * 100 + await(@Array<Future<Int>>.0[1])
}
"""
        assert _run(src, "f") == 4455

    def test_array_future_int_append(self) -> None:
        """`array_append(Array<Future<Int>>, Future<Int>)` appends an i64.

        RED before the fix: the appended element local was typed i32
        while the pushed payload was i64 — a "expected i32, found i64"
        WASM validation trap (not a wrong value)."""
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(<Async>) {
  let @Future<Int> = async(11);
  let @Future<Int> = async(22);
  let @Array<Future<Int>> = [@Future<Int>.1];
  let @Array<Future<Int>> = array_append(@Array<Future<Int>>.0, @Future<Int>.0);
  await(@Array<Future<Int>>.0[0]) * 100 + await(@Array<Future<Int>>.0[1])
}
"""
        assert _run(src, "f") == 1122

    def test_array_future_int_reverse(self) -> None:
        """`array_reverse(Array<Future<Int>>)` swaps [11, 22] to [22, 11].

        Non-palindromic values so a reverse that copied at the wrong
        stride cannot coincide.  RED before the fix: 4724464025600, not
        2211 (22*100 + 11)."""
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(<Async>) {
  let @Future<Int> = async(11);
  let @Future<Int> = async(22);
  let @Array<Future<Int>> = [@Future<Int>.1, @Future<Int>.0];
  let @Array<Future<Int>> = array_reverse(@Array<Future<Int>>.0);
  await(@Array<Future<Int>>.0[0]) * 100 + await(@Array<Future<Int>>.0[1])
}
"""
        assert _run(src, "f") == 2211

    def test_array_future_int_filter_keepall(self) -> None:
        """`array_filter(Array<Future<Int>>, |_| true)` keeps both i64s.

        The predicate is `pure` (an awaiting predicate is a checker
        error — you cannot compare an un-awaited Future), so a keep-all
        filter is the expressible form that still exercises the copy
        loop.  RED before the fix: the wrong-stride copy trapped at
        runtime."""
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(<Async>) {
  let @Future<Int> = async(11);
  let @Future<Int> = async(22);
  let @Array<Future<Int>> = [@Future<Int>.1, @Future<Int>.0];
  let @Array<Future<Int>> = array_filter(
    @Array<Future<Int>>.0,
    fn(@Future<Int> -> @Bool) effects(pure) { true }
  );
  await(@Array<Future<Int>>.0[0]) * 100 + await(@Array<Future<Int>>.0[1])
}
"""
        assert _run(src, "f") == 1122

    def test_array_future_int_flatten(self) -> None:
        """`array_flatten(Array<Array<Future<Int>>>)` copies inner i64s.

        `array_flatten` recovers the inner element type by an AST walk
        (not `_infer_concat_elem_type`), which independently dropped the
        `Future` arg.  RED before the fix: 9448928052300, not 1122."""
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(<Async>) {
  let @Future<Int> = async(11);
  let @Future<Int> = async(22);
  let @Array<Future<Int>> = [@Future<Int>.1];
  let @Array<Future<Int>> = [@Future<Int>.0];
  let @Array<Array<Future<Int>>> = [@Array<Future<Int>>.1, @Array<Future<Int>>.0];
  let @Array<Future<Int>> = array_flatten(@Array<Array<Future<Int>>>.0);
  await(@Array<Future<Int>>.0[0]) * 100 + await(@Array<Future<Int>>.0[1])
}
"""
        assert _run(src, "f") == 1122

    def test_array_future_string_concat(self) -> None:
        """`array_concat(Array<Future<String>>, …)` copies pair payloads.

        A `Future<String>` element is a two-word (ptr, len) pair like its
        payload.  RED before the fix: treated as a single i32, the concat
        mangled the pair and `string_length` read back 400, not 402
        (len 4 * 100 + len 2)."""
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(<Async>) {
  let @Future<String> = async("aaaa");
  let @Future<String> = async("bb");
  let @Array<Future<String>> = [@Future<String>.1];
  let @Array<Future<String>> = [@Future<String>.0];
  let @Array<Future<String>> = array_concat(@Array<Future<String>>.1, @Array<Future<String>>.0);
  string_length(await(@Array<Future<String>>.0[0])) * 100
    + string_length(await(@Array<Future<String>>.0[1]))
}
"""
        assert _run(src, "f") == 402

    def test_array_plain_int_concat_control(self) -> None:
        """Control: `array_concat` over a plain `Array<Int>` (no Future)
        already worked and must stay green — pins that the #1057
        full-spelling change does not regress the bare-i64 element
        path.  11*100 + 22 = 1122."""
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Array<Int> = [11];
  let @Array<Int> = [22];
  let @Array<Int> = array_concat(@Array<Int>.1, @Array<Int>.0);
  @Array<Int>.0[0] * 100 + @Array<Int>.0[1]
}
"""
        assert _run(src, "f") == 1122


class TestAliasFutureArrayElement1058:
    """#1058: an aliased `Future<T>` array-literal element trapped.

    `type FI = Future<Int>; let @Array<FI> = [async(1)]` was check-green
    then trapped "expected i32, found i64".  `_translate_array_lit`
    resolved the element name with the name-only `_resolve_base_type_name`
    (dropping the alias's args, `FI` -> bare `"Future"`), so the i64
    payload was stored with `i32.store`.  The fix canonicalizes the alias
    to its full compound spelling (`Future<Int>`) via
    `_canonicalize_alias_slot_name` before the resolve, mirroring the
    `_is_pair_type_name` order (#1046).
    """

    def test_alias_future_int_array_element(self) -> None:
        """`type FI = Future<Int>; let @Array<FI> = [@FI.1, @FI.0]`.

        RED before the fix: storing the i64 payload through the bare-
        `"Future"` i32 path trapped at WASM validation ("expected i32,
        found i64").  `@FI.1`=7, `@FI.0`=8, so 7*10 + 8 = 78."""
        src = """
type FI = Future<Int>;
public fn f(-> @Int) requires(true) ensures(true) effects(<Async>) {
  let @FI = async(7);
  let @FI = async(8);
  let @Array<FI> = [@FI.1, @FI.0];
  await(@Array<FI>.0[0]) * 10 + await(@Array<FI>.0[1])
}
"""
        assert _run(src, "f") == 78

    def test_alias_future_string_array_element(self) -> None:
        """An aliased pair-payload `Future<String>` array element.

        `type FS = Future<String>`: the canonicalized `Future<String>`
        must be recognized as a two-word pair.  RED before the fix: bare
        `"Future"` sized it as one i32 and the literal store left the len
        half on the stack ("values remaining on stack").  Element [1] is
        "worldwide" (length 9)."""
        src = """
type FS = Future<String>;
public fn f(-> @Int) requires(true) ensures(true) effects(<Async>) {
  let @FS = async("hello");
  let @FS = async("worldwide");
  let @Array<FS> = [@FS.1, @FS.0];
  string_length(await(@Array<FS>.0[1]))
}
"""
        assert _run(src, "f") == 9

    def test_alias_to_array_element_control(self) -> None:
        """Control: an aliased *Array* element (`type Row = Array<Int>`)
        already worked (bare "Array" is still recognized as a pair) and
        must stay green — pins that adding the canonicalize step does not
        regress the non-Future alias path.  11*100 + 22 = 1122."""
        src = """
type Row = Array<Int>;
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Row = [11, 22];
  let @Array<Row> = [@Row.0];
  @Array<Row>.0[0][0] * 100 + @Array<Row>.0[0][1]
}
"""
        assert _run(src, "f") == 1122

    def test_direct_future_int_array_element_control(self) -> None:
        """Control: the direct `Future<Int>` spelling (no alias) already
        worked (#1045) and must stay green — pins that #1058's
        canonicalize step leaves the non-alias path unchanged.
        `@Future<Int>.1`=7, `@Future<Int>.0`=8, so 7*10 + 8 = 78."""
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(<Async>) {
  let @Future<Int> = async(7);
  let @Future<Int> = async(8);
  let @Array<Future<Int>> = [@Future<Int>.1, @Future<Int>.0];
  await(@Array<Future<Int>>.0[0]) * 10 + await(@Array<Future<Int>>.0[1])
}
"""
        assert _run(src, "f") == 78


class TestAliasElementCombinators1062:
    """#1062: array combinators over alias-spelled element types.

    The alias-spelled sibling of #1057, one layer down: once #1058 made
    `Array<FI>` (`type FI = Future<Int>`) literals buildable, the
    combinators received the ALIAS name as the element type — bare,
    unresolved — from three sites (`_infer_concat_elem_type` for
    concat/slice/reverse/filter, the `array_append` element inference,
    and the `array_flatten` inner-type walk).  The module-level element
    helpers have no alias table, so the raw name fell to the 4-byte i32
    default: silent-wrong values for Future-aliases (e.g. concat
    returned 9448928052300 for an expected 1122), an "expected i32,
    found i64" validation trap for append, and — reachable even before
    #1058 — a wrong element for a scalar alias like `type Flag = Bool`
    (whose 1-byte elements were copied at a 4-byte stride).  Each site
    now canonicalizes a bare alias name to its target's full compound
    spelling (then resolves refinements), mirroring the #1058
    literal-store fix; the index-read path was already alias-clean via
    `_alias_array_element`'s canonical element (#559).
    """

    def test_alias_future_int_concat(self) -> None:
        """`array_concat` over `Array<FI>`, `type FI = Future<Int>`.

        RED before the fix: bare "FI" fell to the 4-byte default and the
        concat returned 9448928052300, not 1122 (11*100 + 22)."""
        src = """
type FI = Future<Int>;
public fn f(-> @Int) requires(true) ensures(true) effects(<Async>) {
  let @FI = async(11);
  let @FI = async(22);
  let @Array<FI> = [@FI.1];
  let @Array<FI> = [@FI.0];
  let @Array<FI> = array_concat(@Array<FI>.1, @Array<FI>.0);
  await(@Array<FI>.0[0]) * 100 + await(@Array<FI>.0[1])
}
"""
        assert _run(src, "f") == 1122

    def test_alias_future_string_concat(self) -> None:
        """`array_concat` over `Array<FS>`, `type FS = Future<String>`.

        The canonicalized `Future<String>` element is a two-word pair.
        RED before the fix: treated as one i32, the concat mangled the
        pair and read back 400, not 402 (len 4 * 100 + len 2)."""
        src = """
type FS = Future<String>;
public fn f(-> @Int) requires(true) ensures(true) effects(<Async>) {
  let @FS = async("aaaa");
  let @FS = async("bb");
  let @Array<FS> = [@FS.1];
  let @Array<FS> = [@FS.0];
  let @Array<FS> = array_concat(@Array<FS>.1, @Array<FS>.0);
  string_length(await(@Array<FS>.0[0])) * 100
    + string_length(await(@Array<FS>.0[1]))
}
"""
        assert _run(src, "f") == 402

    def test_alias_future_int_reverse(self) -> None:
        """`array_reverse` over `Array<FI>` swaps [11, 22] to [22, 11].

        RED before the fix: 4724464025600, not 2211 (22*100 + 11)."""
        src = """
type FI = Future<Int>;
public fn f(-> @Int) requires(true) ensures(true) effects(<Async>) {
  let @FI = async(11);
  let @FI = async(22);
  let @Array<FI> = [@FI.1, @FI.0];
  let @Array<FI> = array_reverse(@Array<FI>.0);
  await(@Array<FI>.0[0]) * 100 + await(@Array<FI>.0[1])
}
"""
        assert _run(src, "f") == 2211

    def test_alias_future_int_append(self) -> None:
        """`array_append(Array<FI>, @FI.0)` appends through the alias.

        The element inference returns the bare alias name for `@FI.0`,
        so the element local was typed i32 while the pushed payload was
        i64.  RED before the fix: "expected i32, found i64" WASM
        validation trap."""
        src = """
type FI = Future<Int>;
public fn f(-> @Int) requires(true) ensures(true) effects(<Async>) {
  let @FI = async(11);
  let @FI = async(22);
  let @Array<FI> = [@FI.1];
  let @Array<FI> = array_append(@Array<FI>.0, @FI.0);
  await(@Array<FI>.0[0]) * 100 + await(@Array<FI>.0[1])
}
"""
        assert _run(src, "f") == 1122

    def test_alias_future_int_flatten(self) -> None:
        """`array_flatten(Array<Array<FI>>)` copies aliased inner i64s.

        The flatten inner-type AST walk returned the bare alias name.
        RED before the fix: 9448928052300, not 1122."""
        src = """
type FI = Future<Int>;
public fn f(-> @Int) requires(true) ensures(true) effects(<Async>) {
  let @FI = async(11);
  let @FI = async(22);
  let @Array<FI> = [@FI.1];
  let @Array<FI> = [@FI.0];
  let @Array<Array<FI>> = [@Array<FI>.1, @Array<FI>.0];
  let @Array<FI> = array_flatten(@Array<Array<FI>>.0);
  await(@Array<FI>.0[0]) * 100 + await(@Array<FI>.0[1])
}
"""
        assert _run(src, "f") == 1122

    def test_alias_scalar_bool_concat(self) -> None:
        """`array_concat` over `Array<Flag>`, `type Flag = Bool`.

        Pins that the canonicalizer (not a Future special case) is what
        fixes alias-spelled elements: a scalar alias's 1-byte elements
        were copied at the 4-byte default stride.  Unlike the Future
        cases this was reachable-and-wrong before #1058 (the literal
        never trapped — its elements are Bool literals).  [true, false]
        ++ [true] reads back 100+20+1.  RED before the fix: 122
        (element [2] misread as false)."""
        src = """
type Flag = Bool;
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Array<Flag> = [true, false];
  let @Array<Flag> = [true];
  let @Array<Flag> = array_concat(@Array<Flag>.1, @Array<Flag>.0);
  let @Int = if @Array<Flag>.0[0] then { 100 } else { 200 };
  let @Int = if @Array<Flag>.0[1] then { 10 } else { 20 };
  let @Int = if @Array<Flag>.0[2] then { 1 } else { 2 };
  @Int.2 + @Int.1 + @Int.0
}
"""
        assert _run(src, "f") == 121

    def test_alias_array_collection_control(self) -> None:
        """Control: an alias naming the COLLECTION (`type Row =
        Array<Int>`, concat of `@Row` slots) was green before #1064 by
        coincidence — the element probe returned None and concat's
        8-byte fallback happened to match Int — and must stay green now
        that the #1064 collection arm resolves it to a principled
        `Int`/8: same value, correct by construction.  11*100 + 22 =
        1122."""
        src = """
type Row = Array<Int>;
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Row = [11];
  let @Row = [22];
  let @Row = array_concat(@Row.1, @Row.0);
  @Row.0[0] * 100 + @Row.0[1]
}
"""
        assert _run(src, "f") == 1122


class TestAliasCollectionCombinators1064:
    """#1064: combinators over alias-NAMED collections.

    `type Flags = Array<Bool>; array_concat(@Flags.1, @Flags.0)` — the
    collection slot's own name misses the `Array` match in the element
    probe (`_infer_concat_elem_type`), distinct from the alias-spelled
    ELEMENT case (#1062).  The probe returned None, and each consumer
    fell back: concat to an 8-byte default stride — coincidentally
    correct for Int / String / pair elements (which is why the shape
    survived), silently wrong for 1-byte Bool / Byte elements — and
    slice / the map-family to a loud E602 skip.  A literal whose
    elements are alias-typed slots (`array_concat([@Flags.0], …)`) hit
    the sibling literal-branch hole: the bare alias name sized the
    two-word pair elements at 4 bytes and indexing the result trapped
    `unreachable`.  Pre-existing on main (reachable without any of the
    #1057/#1058/#1062 enablers — aliased-collection literals never
    trapped).  The probe now canonicalizes the collection name to its
    target's full spelling, extracts the element spelling, and
    canonicalizes a bare element name in turn; the literal branch
    canonicalizes bare inferred names the same way.
    """

    def test_alias_bool_collection_concat(self) -> None:
        """Concat of `@Flags` slots, 1-byte Bool elements.

        [true, false] ++ [true] reads back 100+20+1 = 121.  RED before
        the fix: 122 — the 8-byte default stride misread element [2]
        as false."""
        src = """
type Flags = Array<Bool>;
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Flags = [true, false];
  let @Flags = [true];
  let @Flags = array_concat(@Flags.1, @Flags.0);
  let @Int = if @Flags.0[0] then { 100 } else { 200 };
  let @Int = if @Flags.0[1] then { 10 } else { 20 };
  let @Int = if @Flags.0[2] then { 1 } else { 2 };
  @Int.2 + @Int.1 + @Int.0
}
"""
        assert _run(src, "f") == 121

    def test_alias_byte_collection_concat(self) -> None:
        """Concat of `@Bytes` slots, 1-byte Byte elements.

        Byte values enter via host args (Vera has no Byte literal;
        `int_to_byte` returns `Option<Byte>`).  Args [3, 5, 7] build
        [3, 5] ++ [7] and read back 3*100 + 5*10 + 7 = 357.  RED
        before the fix: 350 — element [2] misread as 0."""
        src = """
type Bytes = Array<Byte>;
public fn f(@Byte, @Byte, @Byte -> @Int) requires(true) ensures(true) effects(pure) {
  let @Bytes = [@Byte.2, @Byte.1];
  let @Bytes = [@Byte.0];
  let @Bytes = array_concat(@Bytes.1, @Bytes.0);
  byte_to_int(@Bytes.0[0]) * 100 + byte_to_int(@Bytes.0[1]) * 10
    + byte_to_int(@Bytes.0[2])
}
"""
        assert _run(src, "f", args=[3, 5, 7]) == 357

    def test_alias_bool_collection_slice(self) -> None:
        """`array_slice` over an alias-named collection.

        slice(1, 3) of [true, false, true] keeps [false, true] →
        20 + 1 = 21.  RED before the fix: the None element type was a
        loud CodegenSkip — the enclosing function was dropped and the
        run failed with no exported function (a skip-to-working unlock,
        not a silent-wrong)."""
        src = """
type Flags = Array<Bool>;
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Flags = [true, false, true];
  let @Flags = array_slice(@Flags.0, 1, 3);
  let @Int = if @Flags.0[0] then { 10 } else { 20 };
  let @Int = if @Flags.0[1] then { 1 } else { 2 };
  @Int.1 + @Int.0
}
"""
        assert _run(src, "f") == 21

    def test_alias_collection_of_aliased_rows_concat(self) -> None:
        """`type Grid = Array<Row>; type Row = Array<Int>` — the
        collection arm's INNER element canonicalize is load-bearing.

        The target spelling of `Grid` keeps `Row` opaque
        (`"Array<Row>"`), so the extracted element is itself a bare
        alias: without the second canonicalize it would fall to the
        4-byte default and REGRESS this previously-green program (its
        pair elements matched the old 8-byte None-fallback by
        coincidence).  Green before and after — same value, correct by
        construction after.  Row [11, 22] lands at index [1] of the
        concat; [1][0]*100 + [1][1] = 1122."""
        src = """
type Row = Array<Int>;
type Grid = Array<Row>;
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Row = [11, 22];
  let @Grid = [@Row.0];
  let @Grid = [@Row.0];
  let @Grid = array_concat(@Grid.1, @Grid.0);
  @Grid.0[1][0] * 100 + @Grid.0[1][1]
}
"""
        assert _run(src, "f") == 1122

    def test_array_lit_of_aliased_collection_concat(self) -> None:
        """Literal-branch variant: `array_concat([@Flags.1], [@Flags.0])`.

        The literal's element infers to the bare alias name "Flags",
        which sized the two-word `Array<Bool>` pair elements at 4
        bytes.  RED before the fix: check-green, then the mangled pair
        trapped `unreachable` when indexed.  Element [1][0] is true →
        1."""
        src = """
type Flags = Array<Bool>;
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Flags = [true, false];
  let @Flags = [true];
  let @Array<Array<Bool>> = array_concat([@Flags.1], [@Flags.0]);
  let @Int = if @Array<Array<Bool>>.0[1][0] then { 1 } else { 2 };
  @Int.0
}
"""
        assert _run(src, "f") == 1


class TestFutureAliasPayloadElement1074:
    """#1074: an array element spelled `Future<Alias>` was mis-sized.

    The alias-INSIDE-`Future<…>` sibling of #1062, one layer deeper.
    #1058/#1062 canonicalize an alias whose target IS a `Future<…>`
    (`type FI = Future<Int>`), and #1045/#1057 preserve the full
    `Future<T>` spelling for a direct payload — but neither reaches an
    alias sitting inside the wrapper's type argument
    (`Array<Future<FlagA>>`, `type FlagA = Bool`; or hidden one hop
    further, `type FF = Future<FlagA>; Array<FF>`).  The element-size /
    store-op deciders `_strip_future` the wrapper and hand the bare,
    unresolved alias (`FlagA`) to a name-keyed size dict with no alias
    table, so it fell to the 4-byte i32 default:

      * Bool/Byte payloads → **silent wrong values**: 1-byte-packed data
        read at a 4-byte stride (check+verify+compile all green).
      * Int/Nat/Float64/String payloads → a **WASM-validation trap**
        (`expected i32, found i64` / "values remaining on stack") at
        instantiation, behind an exit-0 compile.

    Pre-existing, not a regression: before this branch's combinator
    commits the Future branch returned bare `"Future"`, whose element
    size is the SAME 4-byte i32 — the identical wrong stride.  The
    branch fixed the non-alias (`Future<Int>` -> 8/i64) and
    alias-of-Future (`type FI = Future<Int>`) payloads; the
    alias-inside-`Future` variant was never within the canonicalizer's
    reach and had no fixture.  Found by the adversarial delta review of
    PR #1041's combinator commits; the fix ships on the same branch.

    The fix extends `_canonicalize_alias_slot_name` to recurse into the
    transparent `Future<…>` payload (`Future<FlagA>` -> `Future<Bool>`)
    and routes the four element-type deciders (`_infer_concat_elem_type`,
    `_translate_array_lit`, the `array_flatten` inner walk, and
    `_infer_index_element_type`) through it uniformly.
    """

    # -- Bool payload: silent wrong values --------------------------------

    def test_future_alias_bool_index_read(self) -> None:
        """Index-read through `Array<Future<FlagA>>`, `type FlagA = Bool`.

        Built at the correct 1-byte stride as `Array<Future<Bool>>`, then
        rebound to the alias spelling and indexed — so the ONLY buggy
        site is the index-read element decider.  [false, true]: [0] ->
        200, [1] -> 10, sum 210.  RED before the fix: 120 (both elements
        misread at the 4-byte stride)."""
        src = """
type FlagA = Bool;
public fn f(-> @Int) requires(true) ensures(true) effects(<Async>) {
  let @Future<Bool> = async(false);
  let @Future<Bool> = async(true);
  let @Array<Future<Bool>> = [@Future<Bool>.1, @Future<Bool>.0];
  let @Array<Future<FlagA>> = @Array<Future<Bool>>.0;
  let @Int = if await(@Array<Future<FlagA>>.0[0]) then { 100 } else { 200 };
  let @Int = if await(@Array<Future<FlagA>>.0[1]) then { 10 } else { 20 };
  @Int.1 + @Int.0
}
"""
        assert _run(src, "f") == 210

    def test_future_alias_bool_concat(self) -> None:
        """`array_concat` over `Array<Future<FlagA>>`, `type FlagA = Bool`.

        [false, true] ++ itself reads back 2000+100+20+1 = 2121.  RED
        before the fix: 1111 (the 4-byte copy stride over 1-byte elements
        misread every element as true)."""
        src = """
type FlagA = Bool;
public fn f(-> @Int) requires(true) ensures(true) effects(<Async>) {
  let @Future<Bool> = async(false);
  let @Future<Bool> = async(true);
  let @Array<Future<Bool>> = [@Future<Bool>.1, @Future<Bool>.0];
  let @Array<Future<FlagA>> = @Array<Future<Bool>>.0;
  let @Array<Future<FlagA>> = array_concat(@Array<Future<FlagA>>.0, @Array<Future<FlagA>>.0);
  let @Int = if await(@Array<Future<FlagA>>.0[0]) then { 1000 } else { 2000 };
  let @Int = if await(@Array<Future<FlagA>>.0[1]) then { 100 } else { 200 };
  let @Int = if await(@Array<Future<FlagA>>.0[2]) then { 10 } else { 20 };
  let @Int = if await(@Array<Future<FlagA>>.0[3]) then { 1 } else { 2 };
  @Int.3 + @Int.2 + @Int.1 + @Int.0
}
"""
        assert _run(src, "f") == 2121

    def test_future_alias_bool_append(self) -> None:
        """`array_append` over `Array<Future<FlagA>>`, `type FlagA = Bool`.

        [false, true] then append true reads back 200+10+1 = 211.  RED
        before the fix: 111 (every element misread as true)."""
        src = """
type FlagA = Bool;
public fn f(-> @Int) requires(true) ensures(true) effects(<Async>) {
  let @Future<Bool> = async(false);
  let @Future<Bool> = async(true);
  let @Array<Future<Bool>> = [@Future<Bool>.1, @Future<Bool>.0];
  let @Array<Future<FlagA>> = @Array<Future<Bool>>.0;
  let @Future<FlagA> = async(true);
  let @Array<Future<FlagA>> = array_append(@Array<Future<FlagA>>.0, @Future<FlagA>.0);
  let @Int = if await(@Array<Future<FlagA>>.0[0]) then { 100 } else { 200 };
  let @Int = if await(@Array<Future<FlagA>>.0[1]) then { 10 } else { 20 };
  let @Int = if await(@Array<Future<FlagA>>.0[2]) then { 1 } else { 2 };
  @Int.2 + @Int.1 + @Int.0
}
"""
        assert _run(src, "f") == 211

    def test_hidden_alias_future_bool_index(self) -> None:
        """Hidden spelling `type FF = Future<FlagA>; type FlagA = Bool`.

        The alias is one hop further out — `Array<FF>` where `FF` itself
        aliases `Future<FlagA>`.  Canonicalizing `FF` lands on
        `Future<FlagA>`, whose `FlagA` payload must then resolve to
        `Bool`.  [false, true]: [0] -> 200, [1] -> 10, sum 210.  RED
        before the fix: 120."""
        src = """
type FlagA = Bool;
type FF = Future<FlagA>;
public fn f(-> @Int) requires(true) ensures(true) effects(<Async>) {
  let @Future<Bool> = async(false);
  let @Future<Bool> = async(true);
  let @Array<Future<Bool>> = [@Future<Bool>.1, @Future<Bool>.0];
  let @Array<FF> = @Array<Future<Bool>>.0;
  let @Int = if await(@Array<FF>.0[0]) then { 100 } else { 200 };
  let @Int = if await(@Array<FF>.0[1]) then { 10 } else { 20 };
  @Int.1 + @Int.0
}
"""
        assert _run(src, "f") == 210

    # -- Scalar / pair payload: WASM-validation trap before the fix -------

    def test_future_alias_int_literal_store(self) -> None:
        """Literal `Array<Future<Big>>` store, `type Big = Int`, value >2^32.

        The literal-store element decider sized the i64 payload at 4
        bytes and emitted `i32.store`.  RED before the fix: an "expected
        i32, found i64" WASM-validation trap at instantiation, on a
        check+verify+compile-green program.  5000000001 - 22 =
        4999999979."""
        src = """
type Big = Int;
public fn f(-> @Int) requires(true) ensures(true) effects(<Async>) {
  let @Future<Big> = async(5000000001);
  let @Future<Big> = async(22);
  let @Array<Future<Big>> = [@Future<Big>.1, @Future<Big>.0];
  await(@Array<Future<Big>>.0[0]) - await(@Array<Future<Big>>.0[1])
}
"""
        assert _run(src, "f") == 4999999979

    def test_future_alias_int_concat(self) -> None:
        """`array_concat` over `Array<Future<Big>>`, `type Big = Int`.

        RED before the fix: the i64 payload sized at 4 bytes trapped at
        WASM validation.  5000000001 - 22 = 4999999979."""
        src = """
type Big = Int;
public fn f(-> @Int) requires(true) ensures(true) effects(<Async>) {
  let @Future<Big> = async(5000000001);
  let @Future<Big> = async(22);
  let @Array<Future<Big>> = [@Future<Big>.1];
  let @Array<Future<Big>> = [@Future<Big>.0];
  let @Array<Future<Big>> = array_concat(@Array<Future<Big>>.1, @Array<Future<Big>>.0);
  await(@Array<Future<Big>>.0[0]) - await(@Array<Future<Big>>.0[1])
}
"""
        assert _run(src, "f") == 4999999979

    def test_future_alias_int_rebind_concat(self) -> None:
        """Build direct `Future<Int>`, rebind to `Future<Big>`, concat.

        Isolates the concat element decider: the array is built at the
        correct 8-byte stride, then rebound to the alias spelling before
        concat.  RED before the fix: WASM-validation trap.  5000000001 -
        22 = 4999999979."""
        src = """
type Big = Int;
public fn f(-> @Int) requires(true) ensures(true) effects(<Async>) {
  let @Future<Int> = async(5000000001);
  let @Future<Int> = async(22);
  let @Array<Future<Int>> = [@Future<Int>.1, @Future<Int>.0];
  let @Array<Future<Big>> = @Array<Future<Int>>.0;
  let @Array<Future<Big>> = array_concat(@Array<Future<Big>>.0, @Array<Future<Big>>.0);
  await(@Array<Future<Big>>.0[0]) - await(@Array<Future<Big>>.0[1])
}
"""
        assert _run(src, "f") == 4999999979

    def test_hidden_alias_future_int_index(self) -> None:
        """Hidden spelling `type BigF = Future<Big>; type Big = Int`.

        `Array<BigF>` — `BigF` canonicalizes to `Future<Big>`, whose
        `Big` payload must then resolve to `Int`.  RED before the fix:
        WASM-validation trap.  5000000001 - 22 = 4999999979."""
        src = """
type Big = Int;
type BigF = Future<Big>;
public fn f(-> @Int) requires(true) ensures(true) effects(<Async>) {
  let @BigF = async(5000000001);
  let @BigF = async(22);
  let @Array<BigF> = [@BigF.1, @BigF.0];
  await(@Array<BigF>.0[0]) - await(@Array<BigF>.0[1])
}
"""
        assert _run(src, "f") == 4999999979

    def test_future_alias_string_concat(self) -> None:
        """`array_concat` over `Array<Future<StrA>>`, `type StrA = String`.

        The canonicalized `Future<String>` element is a two-word pair.
        RED before the fix: sized as one i32, the concat left the len
        half on the stack ("values remaining on stack" validation trap).
        "aaaa"(4) ++ "bb"(2), doubled → [4]*100 + [2] = 402."""
        src = """
type StrA = String;
public fn f(-> @Int) requires(true) ensures(true) effects(<Async>) {
  let @Future<String> = async("aaaa");
  let @Future<String> = async("bb");
  let @Array<Future<String>> = [@Future<String>.1, @Future<String>.0];
  let @Array<Future<StrA>> = @Array<Future<String>>.0;
  let @Array<Future<StrA>> = array_concat(@Array<Future<StrA>>.0, @Array<Future<StrA>>.0);
  string_length(await(@Array<Future<StrA>>.0[0])) * 100
    + string_length(await(@Array<Future<StrA>>.0[1]))
}
"""
        assert _run(src, "f") == 402

    def test_future_alias_int_flatten(self) -> None:
        """`array_flatten(Array<Array<Future<Big>>>)`, `type Big = Int`.

        The inner arrays are built at the correct 8-byte stride as
        `Array<Future<Int>>`; only the flatten inner-type walk sees the
        `Big` alias.  The flatten result is read back through the direct
        `Future<Int>` spelling, so this isolates the flatten site.  RED
        before the fix: 95194313217 (the 4-byte copy mangled the i64
        payloads), not 4999999979."""
        src = """
type Big = Int;
public fn f(-> @Int) requires(true) ensures(true) effects(<Async>) {
  let @Future<Int> = async(5000000001);
  let @Future<Int> = async(22);
  let @Array<Future<Int>> = [@Future<Int>.1];
  let @Array<Future<Int>> = [@Future<Int>.0];
  let @Array<Array<Future<Big>>> = [@Array<Future<Int>>.1, @Array<Future<Int>>.0];
  let @Array<Future<Big>> = array_flatten(@Array<Array<Future<Big>>>.0);
  let @Array<Future<Int>> = @Array<Future<Big>>.0;
  await(@Array<Future<Int>>.0[0]) - await(@Array<Future<Int>>.0[1])
}
"""
        assert _run(src, "f") == 4999999979

    # -- Differential twins: the direct spelling is green before AND after

    def test_direct_future_bool_concat_control(self) -> None:
        """Control twin of `test_future_alias_bool_concat`: the direct
        `Future<Bool>` spelling (no alias) already worked (#1057) and
        must stay green — pins that the #1074 payload canonicalize leaves
        the non-alias path unchanged.  2000+100+20+1 = 2121."""
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(<Async>) {
  let @Future<Bool> = async(false);
  let @Future<Bool> = async(true);
  let @Array<Future<Bool>> = [@Future<Bool>.1, @Future<Bool>.0];
  let @Array<Future<Bool>> = array_concat(@Array<Future<Bool>>.0, @Array<Future<Bool>>.0);
  let @Int = if await(@Array<Future<Bool>>.0[0]) then { 1000 } else { 2000 };
  let @Int = if await(@Array<Future<Bool>>.0[1]) then { 100 } else { 200 };
  let @Int = if await(@Array<Future<Bool>>.0[2]) then { 10 } else { 20 };
  let @Int = if await(@Array<Future<Bool>>.0[3]) then { 1 } else { 2 };
  @Int.3 + @Int.2 + @Int.1 + @Int.0
}
"""
        assert _run(src, "f") == 2121

    def test_direct_future_int_flatten_control(self) -> None:
        """Control twin of `test_future_alias_int_flatten`: the direct
        `Future<Int>` spelling already worked and must stay green —
        pins that the flatten-site canonicalize leaves the non-alias
        path unchanged.  5000000001 - 22 = 4999999979."""
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(<Async>) {
  let @Future<Int> = async(5000000001);
  let @Future<Int> = async(22);
  let @Array<Future<Int>> = [@Future<Int>.1];
  let @Array<Future<Int>> = [@Future<Int>.0];
  let @Array<Array<Future<Int>>> = [@Array<Future<Int>>.1, @Array<Future<Int>>.0];
  let @Array<Future<Int>> = array_flatten(@Array<Array<Future<Int>>>.0);
  await(@Array<Future<Int>>.0[0]) - await(@Array<Future<Int>>.0[1])
}
"""
        assert _run(src, "f") == 4999999979


class TestFutureCollectionAliasElements1082:
    """#1082: a COLLECTION alias hiding an `Array<Future<Alias>>`
    (`type FlagA = Bool; type Rows = Array<Future<FlagA>>`) mis-sizes
    the elements through the array combinators — the #1074 residual arm.

    `_infer_concat_elem_type`'s collection-alias arm (#1064) resolves
    the collection name to its target's full spelling and extracts the
    element — but a COMPOUND element (`Future<FlagA>`) was returned
    VERBATIM, skipping the payload canonicalization the sibling
    bare-element branch performs (`type Rows = Array<FF>` with
    `type FF = Future<FlagA>` worked — the element is the bare name
    `FF` there).  `_strip_future("Future<FlagA>")` hands the size dict
    the unresolved alias `FlagA`, which falls to the 4-byte default:
    silent wrong values for 1-byte Bool payloads (concat 2122 / reverse
    2222 instead of 2121 / 1212) and for i64 payloads (concat of two
    distinct >2^32 futures returned 0 — both reads landed on the same
    element; reverse returned reinterpreted garbage).  All
    check+verify-green.  Slice/filter/index shapes over the same alias
    read correctly only by heap-layout coincidence (the packed data
    happens to sit inside the first wrong-stride window), so the fix is
    what makes them deterministic.

    The fix canonicalizes the compound element before returning —
    `Future<FlagA>` -> `Future<Bool>` via the #1074-extended
    `_canonicalize_alias_slot_name` payload walk — exactly like the
    `Array`-headed SlotRef arm's `Future` branch.
    """

    def test_rows_alias_bool_concat(self) -> None:
        """`array_concat` over `@Rows`, `type Rows = Array<Future<FlagA>>`.

        [false, true] ++ itself reads 2000+100+20+1 = 2121.  RED before
        the fix: 2122 (the second copy's 4-byte stride left element 3
        misread as false)."""
        src = """
type FlagA = Bool;
type Rows = Array<Future<FlagA>>;

public fn f(-> @Int) requires(true) ensures(true) effects(<Async>) {
  let @Future<Bool> = async(false);
  let @Future<Bool> = async(true);
  let @Array<Future<Bool>> = [@Future<Bool>.1, @Future<Bool>.0];
  let @Rows = @Array<Future<Bool>>.0;
  let @Rows = array_concat(@Rows.0, @Rows.0);
  let @Int = if await(@Rows.0[0]) then { 1000 } else { 2000 };
  let @Int = if await(@Rows.0[1]) then { 100 } else { 200 };
  let @Int = if await(@Rows.0[2]) then { 10 } else { 20 };
  let @Int = if await(@Rows.0[3]) then { 1 } else { 2 };
  @Int.3 + @Int.2 + @Int.1 + @Int.0
}
"""
        assert _run(src, "f") == 2121

    def test_rows_alias_bool_reverse(self) -> None:
        """`array_reverse` over the same `Rows` alias.

        [false, true, false, true] reversed reads [true, false, true,
        false]: 1000+200+10+2 = 1212.  RED before the fix: 2222 (every
        element misread as false — the 4-byte-stride swap scattered the
        1-byte-packed payloads)."""
        src = """
type FlagA = Bool;
type Rows = Array<Future<FlagA>>;

public fn f(-> @Int) requires(true) ensures(true) effects(<Async>) {
  let @Future<Bool> = async(false);
  let @Future<Bool> = async(true);
  let @Array<Future<Bool>> = [@Future<Bool>.1, @Future<Bool>.0, @Future<Bool>.1, @Future<Bool>.0];
  let @Rows = @Array<Future<Bool>>.0;
  let @Rows = array_reverse(@Rows.0);
  let @Int = if await(@Rows.0[0]) then { 1000 } else { 2000 };
  let @Int = if await(@Rows.0[1]) then { 100 } else { 200 };
  let @Int = if await(@Rows.0[2]) then { 10 } else { 20 };
  let @Int = if await(@Rows.0[3]) then { 1 } else { 2 };
  @Int.3 + @Int.2 + @Int.1 + @Int.0
}
"""
        assert _run(src, "f") == 1212

    def test_rows_alias_int_concat(self) -> None:
        """i64 twin: `type Rows = Array<Future<Big>>`, `type Big = Int`.

        RED before the fix: 0 — the 4-byte copy stride made reads [0]
        and [1] land on the same first i64, so their difference
        vanished.  5000000001 - 22 = 4999999979."""
        src = """
type Big = Int;
type Rows = Array<Future<Big>>;

public fn f(-> @Int) requires(true) ensures(true) effects(<Async>) {
  let @Future<Int> = async(5000000001);
  let @Future<Int> = async(22);
  let @Array<Future<Int>> = [@Future<Int>.1, @Future<Int>.0];
  let @Rows = @Array<Future<Int>>.0;
  let @Rows = array_concat(@Rows.0, @Rows.0);
  await(@Rows.0[0]) - await(@Rows.0[1])
}
"""
        assert _run(src, "f") == 4999999979

    def test_rows_alias_int_reverse(self) -> None:
        """i64 reverse twin.  [5000000001, 22] reversed reads
        [22, 5000000001]: 22 - 5000000001 = -4999999979.  RED before
        the fix: 3028092410585415681 (byte-scrambled i64s)."""
        src = """
type Big = Int;
type Rows = Array<Future<Big>>;

public fn f(-> @Int) requires(true) ensures(true) effects(<Async>) {
  let @Future<Int> = async(5000000001);
  let @Future<Int> = async(22);
  let @Array<Future<Int>> = [@Future<Int>.1, @Future<Int>.0];
  let @Rows = @Array<Future<Int>>.0;
  let @Rows = array_reverse(@Rows.0);
  await(@Rows.0[0]) - await(@Rows.0[1])
}
"""
        assert _run(src, "f") == -4999999979

    def test_rows_alias_bool_slice_deterministic(self) -> None:
        """`array_slice` over the same `Rows` alias.

        [false, true, false, true] sliced (1, 3) reads [true, false]:
        100 + 20 = 120.  Coincidence-green before the fix (the wrong
        4-byte stride happened to read plausible bytes on this heap
        layout) — pinned so the now-deterministic 1-byte stride stays."""
        src = """
type FlagA = Bool;
type Rows = Array<Future<FlagA>>;

public fn f(-> @Int) requires(true) ensures(true) effects(<Async>) {
  let @Future<Bool> = async(false);
  let @Future<Bool> = async(true);
  let @Array<Future<Bool>> = [@Future<Bool>.1, @Future<Bool>.0, @Future<Bool>.1, @Future<Bool>.0];
  let @Rows = @Array<Future<Bool>>.0;
  let @Rows = array_slice(@Rows.0, 1, 3);
  let @Int = if await(@Rows.0[0]) then { 100 } else { 200 };
  let @Int = if await(@Rows.0[1]) then { 10 } else { 20 };
  @Int.1 + @Int.0
}
"""
        assert _run(src, "f") == 120

    def test_rows_hidden_ff_concat_control(self) -> None:
        """Control: the BARE-element spelling of the same nest —
        `type FF = Future<FlagA>; type Rows = Array<FF>` — already
        worked (the bare-element branch canonicalizes `FF` ->
        `Future<Bool>`) and must stay green.  2000+100+20+1 = 2121."""
        src = """
type FlagA = Bool;
type FF = Future<FlagA>;
type Rows = Array<FF>;

public fn f(-> @Int) requires(true) ensures(true) effects(<Async>) {
  let @Future<Bool> = async(false);
  let @Future<Bool> = async(true);
  let @Array<Future<Bool>> = [@Future<Bool>.1, @Future<Bool>.0];
  let @Rows = @Array<Future<Bool>>.0;
  let @Rows = array_concat(@Rows.0, @Rows.0);
  let @Int = if await(@Rows.0[0]) then { 1000 } else { 2000 };
  let @Int = if await(@Rows.0[1]) then { 100 } else { 200 };
  let @Int = if await(@Rows.0[2]) then { 10 } else { 20 };
  let @Int = if await(@Rows.0[3]) then { 1 } else { 2 };
  @Int.3 + @Int.2 + @Int.1 + @Int.0
}
"""
        assert _run(src, "f") == 2121


class TestFutureBoolMapStrideDesync1081:
    """#1081: `array_map` over `Array<Future<Bool>>` (DIRECT spelling)
    silently misread EVERY element — a read/write stride desync that
    regressed on main with #1041.

    #1041's element-READ stripping sizes `Future<Bool>` index reads at
    the payload's 1-byte stride, but `array_map`'s element WRITE path
    still inferred the bare head `"Future"` (#1079's mechanism) and
    stored at the 4-byte default — the previously-consistent 4/4
    round-trip became 1/4.  Pre-#1041 this program returned 2121
    (correct); on the #1041 merge it returned 2222 — every element
    misread as false ([1] onward read the zero high bytes of the first
    i32 store; [0] happened to be false here too).  Closed by the same
    #1079 write-side fix (`_infer_closure_return_vera_type` rendering
    the full `Future<Bool>` spelling, 1-byte store stride); this test
    pins the base-correct 2121 pattern from the adversarial review of
    the merge.
    """

    def test_map_future_bool_identity_2121(self) -> None:
        """Identity map over [false, true, false, true]: 2000 + 100 +
        20 + 1 = 2121.  RED on the #1041 merge: 2222."""
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(<Async>) {
  let @Future<Bool> = async(false);
  let @Future<Bool> = async(true);
  let @Array<Future<Bool>> = [@Future<Bool>.1, @Future<Bool>.0, @Future<Bool>.1, @Future<Bool>.0];
  let @Array<Future<Bool>> = array_map(@Array<Future<Bool>>.0, fn(@Future<Bool> -> @Future<Bool>) effects(pure) { @Future<Bool>.0 });
  let @Int = if await(@Array<Future<Bool>>.0[0]) then { 1000 } else { 2000 };
  let @Int = if await(@Array<Future<Bool>>.0[1]) then { 100 } else { 200 };
  let @Int = if await(@Array<Future<Bool>>.0[2]) then { 10 } else { 20 };
  let @Int = if await(@Array<Future<Bool>>.0[3]) then { 1 } else { 2 };
  @Int.3 + @Int.2 + @Int.1 + @Int.0
}
"""
        assert _run(src, "f") == 2121

    def test_nomap_future_bool_control(self) -> None:
        """Control: the same reads WITHOUT the map were correct on both
        sides of #1041 and must stay green.  2121."""
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(<Async>) {
  let @Future<Bool> = async(false);
  let @Future<Bool> = async(true);
  let @Array<Future<Bool>> = [@Future<Bool>.1, @Future<Bool>.0, @Future<Bool>.1, @Future<Bool>.0];
  let @Int = if await(@Array<Future<Bool>>.0[0]) then { 1000 } else { 2000 };
  let @Int = if await(@Array<Future<Bool>>.0[1]) then { 100 } else { 200 };
  let @Int = if await(@Array<Future<Bool>>.0[2]) then { 10 } else { 20 };
  let @Int = if await(@Array<Future<Bool>>.0[3]) then { 1 } else { 2 };
  @Int.3 + @Int.2 + @Int.1 + @Int.0
}
"""
        assert _run(src, "f") == 2121


class TestFutureClosureReturnCombinators1079:
    """#1079: array_map/mapi/fold over `Array<Future<T>>` mis-sized the
    output element (or fold accumulator).

    The bare-head family (#1057's mechanism) at the closure-return /
    fold-accumulator inference site: `_infer_closure_return_vera_type`
    (and `_infer_fold_init_vera_type`'s SlotRef-init fallback) returned
    `canonical.name` — bare `"Future"`, the type argument dropped — so
    the element-size / wasm-type deciders fell to the 4-byte i32
    default while an i64 / f64 / pair payload occupies 8 bytes.  The
    #1045/#1057 element fixes and the #1074 payload canonicalizer never
    reach this path (it returned `.name` before the deciders run), and
    the DIRECT `Future<Int>` spelling mis-sizes too, not only aliases.
    `array_map` rejects an async closure, so the trigger is a PURE
    closure forwarding an existing Future value — identity/reshuffle.

    Failure modes, all check+verify-green with compile exit 0:

      * Int/Nat/Float64 payloads (map/mapi) → `indirect call type
        mismatch` trap at run: the registered call_indirect signature
        says the closure returns i32 while the closure was compiled
        returning i64/f64.
      * String payloads → the same trap (i32 vs two-value i32_pair).
      * Bool payloads → SILENT wrong values: the signatures happen to
        agree (Bool is i32), so the loop stores at a 4-byte stride and
        the downstream index read walks the 1-byte-packed layout.
      * `array_fold` with a Future accumulator → WASM-validation error
        (`expected i32, found i64`) at instantiation: the accumulator
        local is typed i32 while the init instructions push i64.

    The fix renders the FULL compound spelling — `_format_named_type`
    plus the #1074-extended `_canonicalize_alias_slot_name` payload
    walk — at both inference sites.  Int payloads exceed 2^32 so a
    truncated read cannot coincide with the correct answer.
    """

    def test_map_future_int_identity(self) -> None:
        """Identity map over `Array<Future<Int>>`, first payload > 2^32.

        RED before the fix: `indirect call type mismatch` trap (sig
        result i32 vs compiled i64).  5000000001 - 22 = 4999999979."""
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(<Async>) {
  let @Future<Int> = async(5000000001);
  let @Future<Int> = async(22);
  let @Array<Future<Int>> = [@Future<Int>.1, @Future<Int>.0];
  let @Array<Future<Int>> = array_map(@Array<Future<Int>>.0, fn(@Future<Int> -> @Future<Int>) effects(pure) { @Future<Int>.0 });
  await(@Array<Future<Int>>.0[0]) - await(@Array<Future<Int>>.0[1])
}
"""
        assert _run(src, "f") == 4999999979

    def test_map_future_bool_silent(self) -> None:
        """Identity map over `Array<Future<Bool>>` — the SILENT shape.

        Bool payloads keep the call_indirect signatures consistent
        (both i32), so nothing traps: the loop stores i32 at a 4-byte
        stride into a `3 * 4`-byte buffer and the index read walks
        1-byte-packed — [true, false, true] misreads as
        [true, false, false].  RED before the fix: 100, not 101."""
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(<Async>) {
  let @Future<Bool> = async(true);
  let @Future<Bool> = async(false);
  let @Future<Bool> = async(true);
  let @Array<Future<Bool>> = [@Future<Bool>.2, @Future<Bool>.1, @Future<Bool>.0];
  let @Array<Future<Bool>> = array_map(@Array<Future<Bool>>.0, fn(@Future<Bool> -> @Future<Bool>) effects(pure) { @Future<Bool>.0 });
  let @Int = if await(@Array<Future<Bool>>.0[0]) then { 100 } else { 0 };
  let @Int = if await(@Array<Future<Bool>>.0[1]) then { 10 } else { 0 };
  let @Int = if await(@Array<Future<Bool>>.0[2]) then { 1 } else { 0 };
  @Int.2 + @Int.1 + @Int.0
}
"""
        assert _run(src, "f") == 101

    def test_map_future_string_pair(self) -> None:
        """Identity map over `Array<Future<String>>` (pair payload).

        RED before the fix: `indirect call type mismatch` trap (sig
        result i32 vs the closure's two-value i32_pair).  Lengths
        8 * 100 + 3 = 803."""
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(<Async>) {
  let @Future<String> = async("alphabet");
  let @Future<String> = async("dog");
  let @Array<Future<String>> = [@Future<String>.1, @Future<String>.0];
  let @Array<Future<String>> = array_map(@Array<Future<String>>.0, fn(@Future<String> -> @Future<String>) effects(pure) { @Future<String>.0 });
  string_length(await(@Array<Future<String>>.0[0])) * 100 + string_length(await(@Array<Future<String>>.0[1]))
}
"""
        assert _run(src, "f") == 803

    def test_map_future_float64(self) -> None:
        """Identity map over `Array<Future<Float64>>`.

        RED before the fix: `indirect call type mismatch` trap (sig
        result i32 vs compiled f64).  1.5 + 2.25 = 3.75 — exactly
        representable, and impossible for any i32/f64 reinterpretation
        of the mis-sized layout to produce."""
        src = """
public fn f(-> @Float64) requires(true) ensures(true) effects(<Async>) {
  let @Future<Float64> = async(1.5);
  let @Future<Float64> = async(2.25);
  let @Array<Future<Float64>> = [@Future<Float64>.1, @Future<Float64>.0];
  let @Array<Future<Float64>> = array_map(@Array<Future<Float64>>.0, fn(@Future<Float64> -> @Future<Float64>) effects(pure) { @Future<Float64>.0 });
  await(@Array<Future<Float64>>.0[0]) + await(@Array<Future<Float64>>.0[1])
}
"""
        assert _run_float(src, "f") == 3.75

    def test_mapi_future_int(self) -> None:
        """`array_mapi` twin of the identity map — its own translator
        computes `b_type` independently.  RED before the fix: the same
        `indirect call type mismatch` trap.  5000000001 - 22 =
        4999999979."""
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(<Async>) {
  let @Future<Int> = async(5000000001);
  let @Future<Int> = async(22);
  let @Array<Future<Int>> = [@Future<Int>.1, @Future<Int>.0];
  let @Array<Future<Int>> = array_mapi(@Array<Future<Int>>.0, fn(@Future<Int>, @Nat -> @Future<Int>) effects(pure) { @Future<Int>.0 });
  await(@Array<Future<Int>>.0[0]) - await(@Array<Future<Int>>.0[1])
}
"""
        assert _run(src, "f") == 4999999979

    def test_fold_future_int_accumulator(self) -> None:
        """`array_fold` with a `Future<Int>` accumulator (select-last).

        RED before the fix: WASM-validation error `expected i32, found
        i64` at instantiation — the accumulator local was typed i32
        (bare `"Future"` → 4-byte default) while the init instructions
        push an i64 payload.  The closure keeps the ELEMENT
        (`@Future<Int>.0` = most recent param), so the fold returns the
        last element: 6000000007 (> 2^32)."""
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(<Async>) {
  let @Future<Int> = async(33);
  let @Future<Int> = async(6000000007);
  let @Array<Future<Int>> = [@Future<Int>.1, @Future<Int>.0];
  let @Future<Int> = async(11);
  let @Future<Int> = array_fold(@Array<Future<Int>>.0, @Future<Int>.0, fn(@Future<Int>, @Future<Int> -> @Future<Int>) effects(pure) { @Future<Int>.0 });
  await(@Future<Int>.0)
}
"""
        assert _run(src, "f") == 6000000007

    def test_fold_future_acc_block_closure_slot_init(self) -> None:
        """Fold accumulator inferred from the INIT SlotRef, not the
        closure — `_infer_fold_init_vera_type`'s fallback arm.

        A block-wrapped closure literal defeats the closure-return
        dispatch (`_closure_arg_return_type` handles AnonFn and SlotRef
        only — a `Block` yields None), so the accumulator type comes
        from the init `@Future<Int>` slot — whose `SlotRef.type_name`
        is the bare head `"Future"` with the payload in `type_args`.
        RED before the fix: the same `expected i32, found i64`
        validation error.  (An if-expression between two closures also
        reaches this fallback, but that shape trips a distinct
        pre-existing translation bug — "values remaining on stack" even
        for a plain-Int fold — so the block form is the shape that
        isolates THIS fallback.)  The closure keeps the element, so the
        fold returns the last one: 6000000007 (> 2^32)."""
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(<Async>) {
  let @Future<Int> = async(33);
  let @Future<Int> = async(6000000007);
  let @Array<Future<Int>> = [@Future<Int>.1, @Future<Int>.0];
  let @Future<Int> = async(11);
  let @Future<Int> = array_fold(
    @Array<Future<Int>>.0,
    @Future<Int>.0,
    { fn(@Future<Int>, @Future<Int> -> @Future<Int>) effects(pure) { @Future<Int>.0 } });
  await(@Future<Int>.0)
}
"""
        assert _run(src, "f") == 6000000007

    def test_fold_future_acc_block_closure_alias_init(self) -> None:
        """Alias twin of the SlotRef-init fallback: the init slot is
        `@FI.0`, `type FI = Future<Int>` — `SlotRef.type_name` is the
        raw alias name, which the fallback must canonicalize
        (`_canonicalize_alias_slot_name`) before the size dict can key
        on it.  RED before the fix (and RED again if the fallback's
        canonicalize hop is dropped): `expected i32, found i64` at
        validation.  Select-element fold returns 6000000007."""
        src = """
type FI = Future<Int>;

public fn f(-> @Int) requires(true) ensures(true) effects(<Async>) {
  let @FI = async(33);
  let @FI = async(6000000007);
  let @Array<FI> = [@FI.1, @FI.0];
  let @FI = async(11);
  let @FI = array_fold(
    @Array<FI>.0,
    @FI.0,
    { fn(@FI, @FI -> @FI) effects(pure) { @FI.0 } });
  await(@FI.0)
}
"""
        assert _run(src, "f") == 6000000007

    def test_map_future_int_alias_element(self) -> None:
        """Aliased twin: `type FI = Future<Int>` as the element AND the
        closure's declared param/return spelling.

        `_canonical_named_type` resolves the alias to
        `NamedType("Future", [Int])` — whose `.name` is the same bare
        `"Future"`.  RED before the fix: the identity-map trap.
        5000000001 - 22 = 4999999979."""
        src = """
type FI = Future<Int>;

public fn f(-> @Int) requires(true) ensures(true) effects(<Async>) {
  let @FI = async(5000000001);
  let @FI = async(22);
  let @Array<FI> = [@FI.1, @FI.0];
  let @Array<FI> = array_map(@Array<FI>.0, fn(@FI -> @FI) effects(pure) { @FI.0 });
  await(@Array<FI>.0[0]) - await(@Array<FI>.0[1])
}
"""
        assert _run(src, "f") == 4999999979

    def test_map_future_payload_alias(self) -> None:
        """Payload-alias twin (#1074's shape at THIS site): the closure
        returns `Future<Big>`, `type Big = Int`.

        `_format_named_type` alone renders `"Future<Big>"`, whose
        payload the size dict cannot key on (4-byte default again) —
        the `_canonicalize_alias_slot_name` payload walk is what
        resolves it to `"Future<Int>"`.  RED before the fix (and RED
        again if the canonicalize wrapper is dropped): the identity-map
        trap.  5000000001 - 22 = 4999999979."""
        src = """
type Big = Int;

public fn f(-> @Int) requires(true) ensures(true) effects(<Async>) {
  let @Future<Big> = async(5000000001);
  let @Future<Big> = async(22);
  let @Array<Future<Big>> = [@Future<Big>.1, @Future<Big>.0];
  let @Array<Future<Big>> = array_map(@Array<Future<Big>>.0, fn(@Future<Big> -> @Future<Big>) effects(pure) { @Future<Big>.0 });
  await(@Array<Future<Big>>.0[0]) - await(@Array<Future<Big>>.0[1])
}
"""
        assert _run(src, "f") == 4999999979

    def test_map_future_int_concat_chained(self) -> None:
        """`array_concat` whose first arg IS an inline `array_map` call —
        `_infer_concat_elem_type`'s map arm delegates to the same
        closure-return inference (vera/wasm/calls.py), so the chained
        spelling inherits the fix.  RED before the fix: the map's own
        trap fires first.  5000000001 - 22 = 4999999979."""
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(<Async>) {
  let @Future<Int> = async(5000000001);
  let @Future<Int> = async(22);
  let @Array<Future<Int>> = [@Future<Int>.1];
  let @Array<Future<Int>> = [@Future<Int>.0];
  let @Array<Future<Int>> = array_concat(
    array_map(@Array<Future<Int>>.1, fn(@Future<Int> -> @Future<Int>) effects(pure) { @Future<Int>.0 }),
    @Array<Future<Int>>.0);
  await(@Array<Future<Int>>.0[0]) - await(@Array<Future<Int>>.0[1])
}
"""
        assert _run(src, "f") == 4999999979

    def test_map_fold_int_direct_control(self) -> None:
        """Control: plain Int map + fold (no Future anywhere) already
        worked and must stay green — pins that the full-spelling render
        leaves the primitive path unchanged.  (11+22+33)*2 = 132."""
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Array<Int> = [11, 22, 33];
  let @Array<Int> = array_map(@Array<Int>.0, fn(@Int -> @Int) effects(pure) { @Int.0 * 2 });
  let @Int = array_fold(@Array<Int>.0, 0, fn(@Int, @Int -> @Int) effects(pure) { @Int.1 + @Int.0 });
  @Int.0
}
"""
        assert _run(src, "f") == 132


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
        no callback invocation, and the $rt.alloc(0) must not trap.
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
        stays at 0, $rt.alloc(0) succeeds, the second pass is likewise
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
