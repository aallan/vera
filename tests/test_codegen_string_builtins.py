"""Tests for vera.codegen — string_builtins (parse/encode builtins (parse_*, base64, url), search/transform builtins, to-string conversions).

Split from tests/test_codegen.py (#419). Shared helpers live in tests/codegen_helpers.py.
"""
from __future__ import annotations

from tests.codegen_helpers import (
    _run,
    _run_io,
)


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
