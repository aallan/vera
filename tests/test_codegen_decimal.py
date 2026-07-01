"""Tests for vera.codegen — decimal (Decimal collection and monomorphization).

Split from tests/test_codegen.py (#419). Shared helpers live in tests/codegen_helpers.py.
"""
from __future__ import annotations

from tests.codegen_helpers import (
    _IO_PRELUDE,
    _compile_ok,
    _run,
    _run_float,
    _run_io,
)


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
