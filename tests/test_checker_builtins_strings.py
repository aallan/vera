"""Tests for the Vera type checker — builtins_strings (string/numeric/conversion/float/regex/markdown builtin type-checking).

Split from tests/test_checker.py (#420). Shared helpers live in tests/checker_helpers.py.
"""
from __future__ import annotations

import pytest

from tests.checker_helpers import (
    _check_err,
    _check_ok,
    _warnings,
)


# =====================================================================
# String built-in operations
# =====================================================================


class TestStringBuiltins:
    def test_string_length_ok(self) -> None:
        _check_ok("""
private fn f(@String -> @Int)
  requires(true) ensures(true) effects(pure)
{ string_length(@String.0) }
""")

    def test_string_concat_ok(self) -> None:
        _check_ok("""
private fn f(@String, @String -> @String)
  requires(true) ensures(true) effects(pure)
{ string_concat(@String.0, @String.1) }
""")

    def test_string_slice_ok(self) -> None:
        _check_ok("""
private fn f(@String, @Nat, @Nat -> @String)
  requires(true) ensures(true) effects(pure)
{ string_slice(@String.0, @Nat.0, @Nat.1) }
""")

    def test_string_length_wrong_arg(self) -> None:
        _check_err("""
private fn f(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ string_length(@Int.0) }
""", "type")

    def test_string_concat_wrong_arg(self) -> None:
        _check_err("""
private fn f(@String, @Int -> @String)
  requires(true) ensures(true) effects(pure)
{ string_concat(@String.0, @Int.0) }
""", "type")

    def test_string_char_code_ok(self) -> None:
        _check_ok("""
private fn f(@String, @Int -> @Nat)
  requires(true) ensures(true) effects(pure)
{ string_char_code(@String.0, @Int.0) }
""")

    def test_string_char_code_wrong_arg(self) -> None:
        _check_err("""
private fn f(@String, @Bool -> @Nat)
  requires(true) ensures(true) effects(pure)
{ string_char_code(@String.0, @Bool.0) }
""", "type")

    def test_parse_nat_ok(self) -> None:
        _check_ok("""
private fn f(@String -> @Result<Nat, String>)
  requires(true) ensures(true) effects(pure)
{ parse_nat(@String.0) }
""")

    def test_parse_nat_bare_nat_mismatch(self) -> None:
        _check_err("""
private fn f(@String -> @Nat)
  requires(true) ensures(true) effects(pure)
{ parse_nat(@String.0) }
""", "expected Nat")

    def test_parse_float64_ok(self) -> None:
        _check_ok("""
private data Result<T, E> { Ok(T), Err(E) }
private fn f(@String -> @Result<Float64, String>)
  requires(true) ensures(true) effects(pure)
{ parse_float64(@String.0) }
""")

    def test_parse_float64_bare_mismatch(self) -> None:
        _check_err("""
private fn f(@String -> @Float64)
  requires(true) ensures(true) effects(pure)
{ parse_float64(@String.0) }
""", "expected Float64")

    def test_parse_int_ok(self) -> None:
        _check_ok("""
private data Result<T, E> { Ok(T), Err(E) }
private fn f(@String -> @Result<Int, String>)
  requires(true) ensures(true) effects(pure)
{ parse_int(@String.0) }
""")

    def test_parse_int_bare_mismatch(self) -> None:
        _check_err("""
private fn f(@String -> @Int)
  requires(true) ensures(true) effects(pure)
{ parse_int(@String.0) }
""", "expected Int")

    def test_parse_bool_ok(self) -> None:
        _check_ok("""
private data Result<T, E> { Ok(T), Err(E) }
private fn f(@String -> @Result<Bool, String>)
  requires(true) ensures(true) effects(pure)
{ parse_bool(@String.0) }
""")

    def test_parse_bool_bare_mismatch(self) -> None:
        _check_err("""
private fn f(@String -> @Bool)
  requires(true) ensures(true) effects(pure)
{ parse_bool(@String.0) }
""", "expected Bool")

    def test_base64_encode_ok(self) -> None:
        _check_ok("""
private fn f(@String -> @String)
  requires(true) ensures(true) effects(pure)
{ base64_encode(@String.0) }
""")

    def test_base64_encode_wrong_type(self) -> None:
        _check_err("""
private fn f(@Int -> @String)
  requires(true) ensures(true) effects(pure)
{ base64_encode(@Int.0) }
""", "expected String")

    def test_base64_decode_ok(self) -> None:
        _check_ok("""
private data Result<T, E> { Ok(T), Err(E) }
private fn f(@String -> @Result<String, String>)
  requires(true) ensures(true) effects(pure)
{ base64_decode(@String.0) }
""")

    def test_base64_decode_wrong_type(self) -> None:
        _check_err("""
private fn f(@Int -> @String)
  requires(true) ensures(true) effects(pure)
{ base64_decode(@Int.0) }
""", "expected String")

    def test_url_encode_ok(self) -> None:
        _check_ok("""
private fn f(@String -> @String)
  requires(true) ensures(true) effects(pure)
{ url_encode(@String.0) }
""")

    def test_url_encode_wrong_type(self) -> None:
        _check_err("""
private fn f(@Int -> @String)
  requires(true) ensures(true) effects(pure)
{ url_encode(@Int.0) }
""", "expected String")

    def test_url_decode_ok(self) -> None:
        _check_ok("""
private data Result<T, E> { Ok(T), Err(E) }
private fn f(@String -> @Result<String, String>)
  requires(true) ensures(true) effects(pure)
{ url_decode(@String.0) }
""")

    def test_url_decode_wrong_type(self) -> None:
        _check_err("""
private fn f(@Int -> @String)
  requires(true) ensures(true) effects(pure)
{ url_decode(@Int.0) }
""", "expected String")

    def test_url_parse_ok(self) -> None:
        _check_ok("""
private data UrlParts { UrlParts(String, String, String, String, String) }
private data Result<T, E> { Ok(T), Err(E) }
private fn f(@String -> @Result<UrlParts, String>)
  requires(true) ensures(true) effects(pure)
{ url_parse(@String.0) }
""")

    def test_url_parse_wrong_type(self) -> None:
        _check_err("""
private fn f(@Int -> @String)
  requires(true) ensures(true) effects(pure)
{ url_parse(@Int.0) }
""", "expected String")

    def test_url_join_ok(self) -> None:
        _check_ok("""
private data UrlParts { UrlParts(String, String, String, String, String) }
private fn f(@UrlParts -> @String)
  requires(true) ensures(true) effects(pure)
{ url_join(@UrlParts.0) }
""")

    def test_url_join_wrong_type(self) -> None:
        _check_err("""
private fn f(@String -> @String)
  requires(true) ensures(true) effects(pure)
{ url_join(@String.0) }
""", "expected UrlParts")

    def test_to_string_ok(self) -> None:
        _check_ok("""
private fn f(@Int -> @String)
  requires(true) ensures(true) effects(pure)
{ to_string(@Int.0) }
""")

    def test_string_strip_ok(self) -> None:
        _check_ok("""
private fn f(@String -> @String)
  requires(true) ensures(true) effects(pure)
{ string_strip(@String.0) }
""")

    def test_string_strip_wrong_arg(self) -> None:
        _check_err("""
private fn f(@Int -> @String)
  requires(true) ensures(true) effects(pure)
{ string_strip(@Int.0) }
""", "type")

    def test_bool_to_string_ok(self) -> None:
        _check_ok("""
private fn f(@Bool -> @String)
  requires(true) ensures(true) effects(pure)
{ bool_to_string(@Bool.0) }
""")

    def test_bool_to_string_wrong_arg(self) -> None:
        _check_err("""
private fn f(@Int -> @String)
  requires(true) ensures(true) effects(pure)
{ bool_to_string(@Int.0) }
""", "type")

    def test_nat_to_string_ok(self) -> None:
        _check_ok("""
private fn f(@Nat -> @String)
  requires(true) ensures(true) effects(pure)
{ nat_to_string(@Nat.0) }
""")

    def test_nat_to_string_wrong_arg(self) -> None:
        _check_err("""
private fn f(@Bool -> @String)
  requires(true) ensures(true) effects(pure)
{ nat_to_string(@Bool.0) }
""", "type")

    def test_byte_to_string_ok(self) -> None:
        _check_ok("""
private fn f(@Byte -> @String)
  requires(true) ensures(true) effects(pure)
{ byte_to_string(@Byte.0) }
""")

    def test_byte_to_string_wrong_arg(self) -> None:
        _check_err("""
private fn f(@Int -> @String)
  requires(true) ensures(true) effects(pure)
{ byte_to_string(@Int.0) }
""", "type")

    def test_int_to_string_ok(self) -> None:
        _check_ok("""
private fn f(@Int -> @String)
  requires(true) ensures(true) effects(pure)
{ int_to_string(@Int.0) }
""")

    def test_int_to_string_wrong_arg(self) -> None:
        _check_err("""
private fn f(@Bool -> @String)
  requires(true) ensures(true) effects(pure)
{ int_to_string(@Bool.0) }
""", "type")

    def test_float_to_string_ok(self) -> None:
        _check_ok("""
private fn f(@Float64 -> @String)
  requires(true) ensures(true) effects(pure)
{ float_to_string(@Float64.0) }
""")

    def test_float_to_string_wrong_arg(self) -> None:
        _check_err("""
private fn f(@Int -> @String)
  requires(true) ensures(true) effects(pure)
{ float_to_string(@Int.0) }
""", "type")


# =====================================================================
# Numeric math builtins (issue #199)
# =====================================================================

class TestNumericBuiltins:
    """Type checking for numeric math built-in functions."""

    def test_abs_ok(self) -> None:
        _check_ok("""
private fn f(@Int -> @Nat)
  requires(true) ensures(true) effects(pure)
{ abs(@Int.0) }
""")

    def test_abs_wrong_arg(self) -> None:
        _check_err("""
private fn f(@String -> @Nat)
  requires(true) ensures(true) effects(pure)
{ abs(@String.0) }
""", "type")

    def test_min_ok(self) -> None:
        _check_ok("""
private fn f(@Int, @Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ min(@Int.0, @Int.1) }
""")

    def test_min_wrong_arg(self) -> None:
        _check_err("""
private fn f(@Int, @String -> @Int)
  requires(true) ensures(true) effects(pure)
{ min(@Int.0, @String.0) }
""", "type")

    def test_max_ok(self) -> None:
        _check_ok("""
private fn f(@Int, @Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ max(@Int.0, @Int.1) }
""")

    def test_floor_ok(self) -> None:
        _check_ok("""
private fn f(@Float64 -> @Int)
  requires(true) ensures(true) effects(pure)
{ floor(@Float64.0) }
""")

    def test_floor_wrong_arg(self) -> None:
        _check_err("""
private fn f(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ floor(@Int.0) }
""", "type")

    def test_ceil_ok(self) -> None:
        _check_ok("""
private fn f(@Float64 -> @Int)
  requires(true) ensures(true) effects(pure)
{ ceil(@Float64.0) }
""")

    def test_round_ok(self) -> None:
        _check_ok("""
private fn f(@Float64 -> @Int)
  requires(true) ensures(true) effects(pure)
{ round(@Float64.0) }
""")

    def test_sqrt_ok(self) -> None:
        _check_ok("""
private fn f(@Float64 -> @Float64)
  requires(true) ensures(true) effects(pure)
{ sqrt(@Float64.0) }
""")

    def test_sqrt_wrong_arg(self) -> None:
        _check_err("""
private fn f(@Int -> @Float64)
  requires(true) ensures(true) effects(pure)
{ sqrt(@Int.0) }
""", "type")

    def test_pow_ok(self) -> None:
        _check_ok("""
private fn f(@Float64, @Int -> @Float64)
  requires(true) ensures(true) effects(pure)
{ pow(@Float64.0, @Int.0) }
""")

    def test_pow_wrong_arg(self) -> None:
        _check_err("""
private fn f(@Float64, @Float64 -> @Float64)
  requires(true) ensures(true) effects(pure)
{ pow(@Float64.0, @Float64.1) }
""", "type")


# =====================================================================
# Numeric type conversions (issue #208)
# =====================================================================

class TestTypeConversionBuiltins:
    """Type-checking for numeric type conversion builtins."""

    def test_int_to_float_ok(self) -> None:
        _check_ok("""
private fn f(@Int -> @Float64)
  requires(true) ensures(true) effects(pure)
{ int_to_float(@Int.0) }
""")

    def test_int_to_float_wrong_arg(self) -> None:
        _check_err("""
private fn f(@String -> @Float64)
  requires(true) ensures(true) effects(pure)
{ int_to_float(@String.0) }
""", "type")

    def test_float_to_int_ok(self) -> None:
        _check_ok("""
private fn f(@Float64 -> @Int)
  requires(true) ensures(true) effects(pure)
{ float_to_int(@Float64.0) }
""")

    def test_float_to_int_wrong_arg(self) -> None:
        _check_err("""
private fn f(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ float_to_int(@Int.0) }
""", "type")

    def test_nat_to_int_ok(self) -> None:
        _check_ok("""
private fn f(@Nat -> @Int)
  requires(true) ensures(true) effects(pure)
{ nat_to_int(@Nat.0) }
""")

    def test_nat_to_int_wrong_arg(self) -> None:
        _check_err("""
private fn f(@String -> @Int)
  requires(true) ensures(true) effects(pure)
{ nat_to_int(@String.0) }
""", "type")

    def test_int_to_nat_ok(self) -> None:
        _check_ok("""
private fn f(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  match int_to_nat(@Int.0) {
    Some(@Nat) -> nat_to_int(@Nat.0),
    None -> 0
  }
}
""")

    def test_int_to_nat_wrong_arg(self) -> None:
        _check_err("""
private fn f(@Float64 -> @Option<Nat>)
  requires(true) ensures(true) effects(pure)
{ int_to_nat(@Float64.0) }
""", "type")

    def test_byte_to_int_ok(self) -> None:
        _check_ok("""
private fn f(@Byte -> @Int)
  requires(true) ensures(true) effects(pure)
{ byte_to_int(@Byte.0) }
""")

    def test_byte_to_int_wrong_arg(self) -> None:
        _check_err("""
private fn f(@String -> @Int)
  requires(true) ensures(true) effects(pure)
{ byte_to_int(@String.0) }
""", "type")

    def test_int_to_byte_ok(self) -> None:
        _check_ok("""
private fn f(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  match int_to_byte(@Int.0) {
    Some(@Byte) -> byte_to_int(@Byte.0),
    None -> 0
  }
}
""")

    def test_int_to_byte_wrong_arg(self) -> None:
        _check_err("""
private fn f(@Float64 -> @Option<Byte>)
  requires(true) ensures(true) effects(pure)
{ int_to_byte(@Float64.0) }
""", "type")


# =====================================================================
# Float64 predicate builtins (issue #212)
# =====================================================================

class TestFloatPredicateBuiltins:
    """Type-checking for Float64 predicate and constant builtins."""

    def test_float_is_nan_ok(self) -> None:
        _check_ok("""
private fn f(@Float64 -> @Bool)
  requires(true) ensures(true) effects(pure)
{ float_is_nan(@Float64.0) }
""")

    def test_float_is_nan_wrong_arg(self) -> None:
        _check_err("""
private fn f(@Int -> @Bool)
  requires(true) ensures(true) effects(pure)
{ float_is_nan(@Int.0) }
""", "type")

    def test_float_is_infinite_ok(self) -> None:
        _check_ok("""
private fn f(@Float64 -> @Bool)
  requires(true) ensures(true) effects(pure)
{ float_is_infinite(@Float64.0) }
""")

    def test_float_is_infinite_wrong_arg(self) -> None:
        _check_err("""
private fn f(@String -> @Bool)
  requires(true) ensures(true) effects(pure)
{ float_is_infinite(@String.0) }
""", "type")

    def test_nan_ok(self) -> None:
        _check_ok("""
private fn f(-> @Float64)
  requires(true) ensures(true) effects(pure)
{ nan() }
""")

    def test_nan_wrong_arity(self) -> None:
        _check_err("""
private fn f(@Float64 -> @Float64)
  requires(true) ensures(true) effects(pure)
{ nan(@Float64.0) }
""", "argument")

    def test_infinity_ok(self) -> None:
        _check_ok("""
private fn f(-> @Float64)
  requires(true) ensures(true) effects(pure)
{ infinity() }
""")

    def test_infinity_wrong_arity(self) -> None:
        _check_err("""
private fn f(@Float64 -> @Float64)
  requires(true) ensures(true) effects(pure)
{ infinity(@Float64.0) }
""", "argument")


# =====================================================================
# Removed legacy names (must fail after #288 naming audit)
# =====================================================================


class TestRemovedLegacyNames:
    """Assert that pre-#288 function names are no longer resolvable."""

    @pytest.mark.parametrize("src, match", [
        ("""
private fn f(@Int -> @Float64)
  requires(true) ensures(true) effects(pure)
{ to_float(@Int.0) }
""", "Unresolved"),
        ("""
private fn f(@Float64 -> @Bool)
  requires(true) ensures(true) effects(pure)
{ is_nan(@Float64.0) }
""", "Unresolved"),
        ("""
private fn f(@Float64 -> @Bool)
  requires(true) ensures(true) effects(pure)
{ is_infinite(@Float64.0) }
""", "Unresolved"),
        ("""
private fn f(@String, @String -> @Bool)
  requires(true) ensures(true) effects(pure)
{ starts_with(@String.0, @String.1) }
""", "Unresolved"),
        ("""
private fn f(@String, @String -> @Bool)
  requires(true) ensures(true) effects(pure)
{ ends_with(@String.0, @String.1) }
""", "Unresolved"),
        ("""
private fn f(@String, @String -> @Bool)
  requires(true) ensures(true) effects(pure)
{ contains(@String.0, @String.1) }
""", "Unresolved"),
        ("""
private fn f(@String, @String -> @Option<Nat>)
  requires(true) ensures(true) effects(pure)
{ index_of(@String.0, @String.1) }
""", "Unresolved"),
        ("""
private fn f(@String -> @String)
  requires(true) ensures(true) effects(pure)
{ strip(@String.0) }
""", "Unresolved"),
        ("""
private fn f(@String -> @String)
  requires(true) ensures(true) effects(pure)
{ upper(@String.0) }
""", "Unresolved"),
        ("""
private fn f(@String -> @String)
  requires(true) ensures(true) effects(pure)
{ lower(@String.0) }
""", "Unresolved"),
        ("""
private fn f(@String, @String, @String -> @String)
  requires(true) ensures(true) effects(pure)
{ replace(@String.0, @String.1, @String.2) }
""", "Unresolved"),
        ("""
private fn f(@String, @String -> @Array<String>)
  requires(true) ensures(true) effects(pure)
{ split(@String.0, @String.1) }
""", "Unresolved"),
        ("""
private fn f(@Array<String>, @String -> @String)
  requires(true) ensures(true) effects(pure)
{ join(@Array<String>.0, @String.0) }
""", "Unresolved"),
        ("""
private fn f(@String, @Int -> @Nat)
  requires(true) ensures(true) effects(pure)
{ char_code(@String.0, @Int.0) }
""", "Unresolved"),
        ("""
private fn f(@Nat -> @String)
  requires(true) ensures(true) effects(pure)
{ from_char_code(@Nat.0) }
""", "Unresolved"),
    ])
    def test_removed_builtin_names_fail(self, src: str, match: str) -> None:
        """Pre-#288 names must not resolve after the naming audit."""
        _check_ok(src)  # must produce no errors (warning-only)
        warns = _warnings(src)
        assert any(match.lower() in w.description.lower() for w in warns), \
            f"Expected warning matching '{match}', got: " \
            f"{[w.description for w in warns]}"


# =====================================================================
# String search and transformation builtins
# =====================================================================

class TestStringSearchBuiltins:
    """Type-checking for string search and transformation builtins."""

    # -- string_contains --

    def test_string_contains_ok(self) -> None:
        _check_ok("""
private fn f(@String, @String -> @Bool)
  requires(true) ensures(true) effects(pure)
{ string_contains(@String.0, @String.1) }
""")

    def test_string_contains_wrong_arg(self) -> None:
        _check_err("""
private fn f(@Int, @String -> @Bool)
  requires(true) ensures(true) effects(pure)
{ string_contains(@Int.0, @String.0) }
""", "type")

    # -- string_starts_with --

    def test_string_starts_with_ok(self) -> None:
        _check_ok("""
private fn f(@String, @String -> @Bool)
  requires(true) ensures(true) effects(pure)
{ string_starts_with(@String.0, @String.1) }
""")

    def test_string_starts_with_wrong_arg(self) -> None:
        _check_err("""
private fn f(@Int, @String -> @Bool)
  requires(true) ensures(true) effects(pure)
{ string_starts_with(@Int.0, @String.0) }
""", "type")

    # -- string_ends_with --

    def test_string_ends_with_ok(self) -> None:
        _check_ok("""
private fn f(@String, @String -> @Bool)
  requires(true) ensures(true) effects(pure)
{ string_ends_with(@String.0, @String.1) }
""")

    def test_string_ends_with_wrong_arg(self) -> None:
        _check_err("""
private fn f(@Int, @String -> @Bool)
  requires(true) ensures(true) effects(pure)
{ string_ends_with(@Int.0, @String.0) }
""", "type")

    # -- string_index_of --

    def test_string_index_of_ok(self) -> None:
        _check_ok("""
private data Option<T> { Some(T), None }
private fn f(@String, @String -> @Option<Nat>)
  requires(true) ensures(true) effects(pure)
{ string_index_of(@String.0, @String.1) }
""")

    def test_string_index_of_wrong_arg(self) -> None:
        _check_err("""
private fn f(@Int, @String -> @Bool)
  requires(true) ensures(true) effects(pure)
{ string_index_of(@Int.0, @String.0) }
""", "type")

    # -- string_upper --

    def test_string_upper_ok(self) -> None:
        _check_ok("""
private fn f(@String -> @String)
  requires(true) ensures(true) effects(pure)
{ string_upper(@String.0) }
""")

    def test_string_upper_wrong_arg(self) -> None:
        _check_err("""
private fn f(@Int -> @String)
  requires(true) ensures(true) effects(pure)
{ string_upper(@Int.0) }
""", "type")

    # -- string_lower --

    def test_string_lower_ok(self) -> None:
        _check_ok("""
private fn f(@String -> @String)
  requires(true) ensures(true) effects(pure)
{ string_lower(@String.0) }
""")

    def test_string_lower_wrong_arg(self) -> None:
        _check_err("""
private fn f(@Int -> @String)
  requires(true) ensures(true) effects(pure)
{ string_lower(@Int.0) }
""", "type")

    # -- string_replace --

    def test_string_replace_ok(self) -> None:
        _check_ok("""
private fn f(@String, @String, @String -> @String)
  requires(true) ensures(true) effects(pure)
{ string_replace(@String.0, @String.1, @String.2) }
""")

    def test_string_replace_wrong_arg(self) -> None:
        _check_err("""
private fn f(@Int, @String, @String -> @String)
  requires(true) ensures(true) effects(pure)
{ string_replace(@Int.0, @String.0, @String.1) }
""", "type")

    # -- string_split --

    def test_string_split_ok(self) -> None:
        _check_ok("""
private fn f(@String, @String -> @Array<String>)
  requires(true) ensures(true) effects(pure)
{ string_split(@String.0, @String.1) }
""")

    def test_string_split_wrong_arg(self) -> None:
        _check_err("""
private fn f(@Int, @String -> @Array<String>)
  requires(true) ensures(true) effects(pure)
{ string_split(@Int.0, @String.0) }
""", "type")

    # -- string_join --

    def test_string_join_ok(self) -> None:
        _check_ok("""
private fn f(@Array<String>, @String -> @String)
  requires(true) ensures(true) effects(pure)
{ string_join(@Array<String>.0, @String.0) }
""")

    def test_string_join_wrong_arg(self) -> None:
        _check_err("""
private fn f(@Array<Int>, @String -> @String)
  requires(true) ensures(true) effects(pure)
{ string_join(@Array<Int>.0, @String.0) }
""", "type")

    # -- string_from_char_code --

    def test_string_from_char_code_ok(self) -> None:
        _check_ok("""
private fn f(@Nat -> @String)
  requires(true) ensures(true) effects(pure)
{ string_from_char_code(@Nat.0) }
""")

    def test_string_from_char_code_wrong_arg(self) -> None:
        _check_err("""
private fn f(@String -> @String)
  requires(true) ensures(true) effects(pure)
{ string_from_char_code(@String.0) }
""", "type")

    # -- string_repeat --

    def test_string_repeat_ok(self) -> None:
        _check_ok("""
private fn f(@String, @Nat -> @String)
  requires(true) ensures(true) effects(pure)
{ string_repeat(@String.0, @Nat.0) }
""")

    def test_string_repeat_wrong_arg(self) -> None:
        _check_err("""
private fn f(@String, @Bool -> @String)
  requires(true) ensures(true) effects(pure)
{ string_repeat(@String.0, @Bool.0) }
""", "type")


class TestMarkdownBuiltins:
    """Type-checking for md_parse, md_render, md_has_heading, etc."""

    def test_md_parse_ok(self) -> None:
        _check_ok("""
private fn f(@String -> @Result<MdBlock, String>)
  requires(true) ensures(true) effects(pure)
{ md_parse(@String.0) }
""")

    def test_md_parse_wrong_type(self) -> None:
        _check_err("""
private fn f(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ md_parse(@Int.0) }
""", "expected String")

    def test_md_render_ok(self) -> None:
        _check_ok("""
private fn f(@MdBlock -> @String)
  requires(true) ensures(true) effects(pure)
{ md_render(@MdBlock.0) }
""")

    def test_md_has_heading_ok(self) -> None:
        _check_ok("""
private fn f(@MdBlock, @Nat -> @Bool)
  requires(true) ensures(true) effects(pure)
{ md_has_heading(@MdBlock.0, @Nat.0) }
""")

    def test_md_has_code_block_ok(self) -> None:
        _check_ok("""
private fn f(@MdBlock, @String -> @Bool)
  requires(true) ensures(true) effects(pure)
{ md_has_code_block(@MdBlock.0, @String.0) }
""")

    def test_md_extract_code_blocks_ok(self) -> None:
        _check_ok("""
private fn f(@MdBlock, @String -> @Array<String>)
  requires(true) ensures(true) effects(pure)
{ md_extract_code_blocks(@MdBlock.0, @String.0) }
""")


class TestRegexBuiltins:
    """Type-checking for regex_match, regex_find, regex_find_all,
    regex_replace."""

    def test_regex_match_ok(self) -> None:
        _check_ok(r"""
private fn f(@String -> @Result<Bool, String>)
  requires(true) ensures(true) effects(pure)
{ regex_match(@String.0, "\\d+") }
""")

    def test_regex_match_wrong_type(self) -> None:
        _check_err("""
private fn f(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ regex_match(@Int.0, @Int.0) }
""", "expected String")

    def test_regex_find_ok(self) -> None:
        _check_ok(r"""
private fn f(@String -> @Result<Option<String>, String>)
  requires(true) ensures(true) effects(pure)
{ regex_find(@String.0, "\\d+") }
""")

    def test_regex_find_all_ok(self) -> None:
        _check_ok(r"""
private fn f(@String -> @Result<Array<String>, String>)
  requires(true) ensures(true) effects(pure)
{ regex_find_all(@String.0, "\\d+") }
""")

    def test_regex_replace_ok(self) -> None:
        _check_ok(r"""
private fn f(@String -> @Result<String, String>)
  requires(true) ensures(true) effects(pure)
{ regex_replace(@String.0, "\\d+", "X") }
""")

    def test_regex_replace_wrong_arity(self) -> None:
        _check_err(r"""
private fn f(@String -> @Result<String, String>)
  requires(true) ensures(true) effects(pure)
{ regex_replace(@String.0, "\\d+") }
""", "expects 3 argument")
