"""Tests for vera.codegen — translator_fixes (WASM call-translator regression fixes (#475): slice/charcode clamps, url/base64/parse edge cases).

Split from tests/test_codegen.py (#419). Shared helpers live in tests/codegen_helpers.py.
"""
from __future__ import annotations

import pytest
import wasmtime

from vera.codegen import (
    execute,
)

from tests.codegen_helpers import (
    _compile_ok,
    _run,
    _run_io,
)


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
