"""Tests for vera.codegen — json (Json collection and typed accessors).

Split from tests/test_codegen.py (#419). Shared helpers live in tests/codegen_helpers.py.
"""
from __future__ import annotations


from tests.codegen_helpers import (
    _compile_ok,
    _run,
    _run_io,
)


class TestJsonCollection:
    """Json ADT built-in operations: json_parse, json_stringify,
    json_get, json_has_field, json_array_length, json_keys, json_type."""

    def test_json_parse_wat_import(self) -> None:
        """json_parse generates a WASM host import."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Result<Json, String> = json_parse("null");
  1
}
"""
        result = _compile_ok(source)
        assert '"json_parse"' in result.wat

    def test_json_stringify_wat_import(self) -> None:
        """json_stringify generates a WASM host import."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ string_length(json_stringify(JNull)) }
"""
        result = _compile_ok(source)
        assert '"json_stringify"' in result.wat

    def test_json_no_imports_when_unused(self) -> None:
        """Programs not using json_parse/json_stringify have no Json imports."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ json_array_length(JNull) }
"""
        result = _compile_ok(source)
        assert '"json_parse"' not in result.wat
        assert '"json_stringify"' not in result.wat

    def test_json_null_array_length(self) -> None:
        """json_array_length(JNull) returns 0."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ json_array_length(JNull) }
"""
        assert _run(source) == 0

    def test_json_type_null(self) -> None:
        """json_type(JNull) returns 'null'."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ if string_contains(json_type(JNull), "null") then { string_length(json_type(JNull)) } else { 0 } }
"""
        assert _run(source) == 4

    def test_json_type_bool(self) -> None:
        """json_type(JBool(true)) returns 'bool'."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ if string_contains(json_type(JBool(true)), "bool") then { string_length(json_type(JBool(true))) } else { 0 } }
"""
        assert _run(source) == 4

    def test_json_type_number(self) -> None:
        """json_type(JNumber(0.0)) returns 'number'."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ if string_contains(json_type(JNumber(0.0)), "number") then { string_length(json_type(JNumber(0.0))) } else { 0 } }
"""
        assert _run(source) == 6

    def test_json_type_string(self) -> None:
        """json_type(JString('hi')) returns 'string'."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ if string_contains(json_type(JString("hi")), "string") then { string_length(json_type(JString("hi"))) } else { 0 } }
"""
        assert _run(source) == 6

    def test_json_type_array(self) -> None:
        """json_type(JArray([])) returns 'array'."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ if string_contains(json_type(JArray([])), "array") then { string_length(json_type(JArray([]))) } else { 0 } }
"""
        assert _run(source) == 5

    def test_json_type_object(self) -> None:
        """json_type(JObject(map_new())) returns 'object'."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ if string_contains(json_type(JObject(map_new())), "object") then { string_length(json_type(JObject(map_new()))) } else { 0 } }
"""
        assert _run(source) == 6

    def test_json_array_length(self) -> None:
        """JArray with 3 elements has length 3."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ json_array_length(JArray([JNull, JBool(true), JNumber(1.0)])) }
"""
        assert _run(source) == 3

    def test_json_parse_array(self) -> None:
        """json_parse('[1,2,3]') returns array of length 3."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Result<Json, String> = json_parse("[1, 2, 3]");
  match @Result<Json, String>.0 {
    Ok(@Json) -> json_array_length(@Json.0),
    Err(@String) -> 0
  }
}
"""
        assert _run(source) == 3

    def test_json_parse_object(self) -> None:
        """json_parse('{"a":1}') returns object with field 'a'."""
        source = '''
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Result<Json, String> = json_parse("{\\"a\\": 1}");
  match @Result<Json, String>.0 {
    Ok(@Json) -> if json_has_field(@Json.0, "a") then { 1 } else { 0 },
    Err(@String) -> 0
  }
}
'''
        assert _run(source) == 1

    def test_json_parse_invalid(self) -> None:
        """json_parse with invalid JSON returns Err."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Result<Json, String> = json_parse("not json");
  match @Result<Json, String>.0 {
    Ok(@Json) -> 0,
    Err(@String) -> 1
  }
}
"""
        assert _run(source) == 1

    def test_json_stringify_null(self) -> None:
        """json_stringify(JNull) returns 'null' (length 4)."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ string_length(json_stringify(JNull)) }
"""
        assert _run(source) == 4

    def test_json_stringify_bool(self) -> None:
        """json_stringify(JBool(true)) returns 'true' (length 4)."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ string_length(json_stringify(JBool(true))) }
"""
        assert _run(source) == 4

    def test_json_stringify_number(self) -> None:
        """json_stringify(JNumber(42.0)) returns '42.0' (length 4)."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ string_length(json_stringify(JNumber(42.0))) }
"""
        assert _run(source) == 4

    def test_json_get_present(self) -> None:
        """json_get on JObject with present key returns Some."""
        source = '''
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Result<Json, String> = json_parse("{\\"count\\": 42}");
  match @Result<Json, String>.0 {
    Ok(@Json) ->
      match json_get(@Json.0, "count") {
        Some(@Json) ->
          match @Json.0 {
            JNumber(@Float64) -> floor(@Float64.0),
            JNull -> 0,
            JBool(@Bool) -> 0,
            JString(@String) -> 0,
            JArray(@Array<Json>) -> 0,
            JObject(@Map<String, Json>) -> 0
          },
        None -> 0
      },
    Err(@String) -> 0
  }
}
'''
        assert _run(source) == 42

    def test_json_get_absent(self) -> None:
        """json_get on JObject with absent key returns None."""
        source = '''
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Result<Json, String> = json_parse("{\\"a\\": 1}");
  match @Result<Json, String>.0 {
    Ok(@Json) ->
      match json_get(@Json.0, "missing") {
        Some(@Json) -> 0,
        None -> 1
      },
    Err(@String) -> 0
  }
}
'''
        assert _run(source) == 1

    def test_json_keys(self) -> None:
        """json_keys on JObject returns array of key strings."""
        source = '''
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Result<Json, String> = json_parse("{\\"a\\": 1, \\"b\\": 2}");
  match @Result<Json, String>.0 {
    Ok(@Json) -> array_length(json_keys(@Json.0)),
    Err(@String) -> 0
  }
}
'''
        assert _run(source) == 2

    def test_json_has_field_false(self) -> None:
        """json_has_field on JNull returns false."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ if json_has_field(JNull, "x") then { 1 } else { 0 } }
"""
        assert _run(source) == 0

    def test_json_array_get_present(self) -> None:
        """json_array_get on JArray with valid index returns Some."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Json = JArray([JNumber(10.0), JNumber(20.0)]);
  match json_array_get(@Json.0, 1) {
    Some(@Json) ->
      match @Json.0 {
        JNumber(@Float64) -> floor(@Float64.0),
        JNull -> 0,
        JBool(@Bool) -> 0,
        JString(@String) -> 0,
        JArray(@Array<Json>) -> 0,
        JObject(@Map<String, Json>) -> 0
      },
    None -> 0
  }
}
"""
        assert _run(source) == 20

    def test_json_custom_data_no_combinators(self) -> None:
        """User-defined non-standard data Json skips combinator injection."""
        source = """
private data Json { MyNode(Int) }
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Json = MyNode(42);
  match @Json.0 {
    MyNode(@Int) -> @Int.0
  }
}
"""
        assert _run(source) == 42

    def test_json_array_get_out_of_bounds(self) -> None:
        """json_array_get with out-of-bounds index returns None."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Json = JArray([JNull]);
  match json_array_get(@Json.0, 5) {
    Some(@Json) -> 0,
    None -> 1
  }
}
"""
        assert _run(source) == 1

    def test_json_array_get_negative_index(self) -> None:
        """json_array_get with negative index returns None."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Json = JArray([JNull, JBool(true)]);
  match json_array_get(@Json.0, 0 - 1) {
    Some(@Json) -> 0,
    None -> 1
  }
}
"""
        assert _run(source) == 1

    def test_json_stringify_object(self) -> None:
        """json_stringify(JObject(...)) round-trips through read_json."""
        source = '''
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Json = JObject(map_insert(map_new(), "k", JNumber(1.0)));
  string_length(json_stringify(@Json.0))
}
'''
        result = _run(source)
        assert result > 0

    def test_json_stringify_array(self) -> None:
        """json_stringify(JArray([...])) exercises read_json array path."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Json = JArray([JNull, JBool(true), JNumber(2.0)]);
  string_length(json_stringify(@Json.0))
}
"""
        result = _run(source)
        assert result > 0

    def test_json_stringify_string(self) -> None:
        """json_stringify(JString(...)) exercises read_json string path."""
        source = '''
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ string_length(json_stringify(JString("hello"))) }
'''
        result = _run(source)
        assert result > 0

    def test_json_stringify_bool_false(self) -> None:
        """json_stringify(JBool(false)) returns 'false' (5 chars)."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ string_length(json_stringify(JBool(false))) }
"""
        assert _run(source) == 5

    def test_json_stringify_number_negative(self) -> None:
        """json_stringify(JNumber(-3.5)) exercises read_json f64 path."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ string_length(json_stringify(JNumber(0.0 - 3.5))) }
"""
        result = _run(source)
        assert result > 0

    def test_json_parse_with_string_values(self) -> None:
        """json_parse with string values exercises write_json string path."""
        source = '''
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Result<Json, String> = json_parse("{\\"name\\": \\"Alice\\"}");
  match @Result<Json, String>.0 {
    Ok(@Json) -> if json_has_field(@Json.0, "name") then { 1 } else { 0 },
    Err(@String) -> 0
  }
}
'''
        assert _run(source) == 1

    def test_json_parse_nested_object(self) -> None:
        """json_parse with nested objects exercises write_json object path."""
        source = '''
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Result<Json, String> = json_parse("{\\"inner\\": {\\"x\\": 1}}");
  match @Result<Json, String>.0 {
    Ok(@Json) ->
      match json_get(@Json.0, "inner") {
        Some(@Json) -> if json_has_field(@Json.0, "x") then { 1 } else { 0 },
        None -> 0
      },
    Err(@String) -> 0
  }
}
'''
        assert _run(source) == 1

    def test_json_parse_stringify_roundtrip(self) -> None:
        """Parse then stringify exercises both write_json and read_json."""
        source = '''
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Result<Json, String> = json_parse("[1, true, null]");
  match @Result<Json, String>.0 {
    Ok(@Json) -> string_length(json_stringify(@Json.0)),
    Err(@String) -> 0
  }
}
'''
        result = _run(source)
        assert result > 0


class TestJsonTypedAccessors:
    """#366 — 11 new Json typed accessors shipped as pure-Vera prelude
    functions (no new WASM translators).  Six Layer-1 type-coercion
    accessors (Json → Option<T>) and five Layer-2 compound field
    accessors (Json, String → Option<T> = json_get + json_as_T
    composed).  ``json_as_int`` specifically guards every
    ``float_to_int`` (i.e. ``i64.trunc_f64_s``) trap path — NaN,
    +infinity, -infinity, and any finite float outside the
    closed-open i64 range ``[-2^63, 2^63)`` (that is,
    ``f >= 2^63`` or ``f < -2^63``; ``-2^63 = INT64_MIN`` is itself
    representable) — via ``float_is_nan`` / ``float_is_infinite``
    plus explicit bounds against ±9223372036854775808.0, returning
    ``None`` for every non-representable-as-Int input.
    """

    # ----- Layer 1: json_as_* -----

    def test_json_as_string_match(self) -> None:
        """JString("hi") → Some("hi")."""
        src = """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  match json_as_string(JString("hi")) {
    Some(@String) -> IO.print(@String.0),
    None -> IO.print("?")
  }
}
"""
        assert _run_io(src) == "hi"

    def test_json_as_string_mismatch(self) -> None:
        """JNumber(1.0) has no JString coercion → None."""
        src = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  match json_as_string(JNumber(1.0)) {
    Some(@String) -> 0,
    None -> 1
  }
}
"""
        assert _run(src) == 1

    def test_json_as_number_match(self) -> None:
        """JNumber(3.14) → Some(3.14)."""
        src = """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  match json_as_number(JNumber(3.14)) {
    Some(@Float64) -> IO.print(float_to_string(@Float64.0)),
    None -> IO.print("?")
  }
}
"""
        assert _run_io(src) == "3.14"

    def test_json_as_bool_match(self) -> None:
        """JBool(true) → Some(true); JBool(false) → Some(false)."""
        src_true = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  match json_as_bool(JBool(true)) {
    Some(@Bool) -> if @Bool.0 then { 1 } else { 0 },
    None -> -1
  }
}
"""
        assert _run(src_true) == 1
        src_false = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  match json_as_bool(JBool(false)) {
    Some(@Bool) -> if @Bool.0 then { 1 } else { 0 },
    None -> -1
  }
}
"""
        assert _run(src_false) == 0

    def test_json_as_int_truncates(self) -> None:
        """JNumber(42.7) → Some(42) via float_to_int truncation."""
        src = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  match json_as_int(JNumber(42.7)) {
    Some(@Int) -> @Int.0,
    None -> -1
  }
}
"""
        assert _run(src) == 42

    def test_json_as_int_negative(self) -> None:
        """JNumber(-3.9) → Some(-3) — i64.trunc_f64_s is toward-zero."""
        src = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  match json_as_int(JNumber(-3.9)) {
    Some(@Int) -> @Int.0,
    None -> 0
  }
}
"""
        assert _run(src) == -3

    def test_json_as_int_nan_returns_none(self) -> None:
        """JNumber(NaN) → None — guard prevents float_to_int trap.

        Without the `float_is_nan || float_is_infinite` guard in the
        prelude body, `float_to_int(NaN)` would trap.  This test
        pins that the accessor returns None cleanly instead.
        """
        src = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  match json_as_int(JNumber(0.0 / 0.0)) {
    Some(@Int) -> 0,
    None -> 1
  }
}
"""
        assert _run(src) == 1

    def test_json_as_int_infinity_returns_none(self) -> None:
        """JNumber(±inf) → None.  Both signs of infinity are trap
        inputs for ``i64.trunc_f64_s`` (distinct from the finite
        out-of-range case below) and the guard covers them via
        ``float_is_infinite``, which is sign-agnostic.
        """
        src_pos = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  match json_as_int(JNumber(infinity())) {
    Some(@Int) -> 0,
    None -> 1
  }
}
"""
        assert _run(src_pos) == 1
        src_neg = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  match json_as_int(JNumber(0.0 - infinity())) {
    Some(@Int) -> 0,
    None -> 1
  }
}
"""
        assert _run(src_neg) == 1

    def test_json_as_int_finite_overflow_returns_none(self) -> None:
        """JNumber with |f| >= 2^63 → None — the guard also covers
        finite-but-out-of-range values, not just NaN/infinity.

        ``i64.trunc_f64_s`` (emitted by ``float_to_int``) traps when
        the float exceeds the i64 range.  9223372036854775808.0 is
        exactly 2^63 in Float64 — representable but one above the
        maximum i64.  Without the range guard, this would trap.
        """
        src = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  match json_as_int(JNumber(9223372036854775808.0)) {
    Some(@Int) -> 0,
    None -> 1
  }
}
"""
        assert _run(src) == 1

    def test_json_as_int_finite_negative_overflow_returns_none(self) -> None:
        """JNumber with f < -2^63 → None (mirror of positive overflow)."""
        src = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  -- -2^64 is well outside i64 range.
  match json_as_int(JNumber(0.0 - 18446744073709551616.0)) {
    Some(@Int) -> 0,
    None -> 1
  }
}
"""
        assert _run(src) == 1

    def test_json_as_int_boundary_minus_2_63_is_representable(self) -> None:
        """JNumber(-2^63) → Some(INT64_MIN).

        The i64 range is closed on the low end (``[-2^63, 2^63)``):
        ``-2^63 = -9223372036854775808`` IS a valid Int.  This test
        pins both that ``Some`` is taken AND that the observed value
        is INT64_MIN (negative, and equal to itself under +1 overflow
        arithmetic).

        We probe the value indirectly because ``int_to_string(INT64_MIN)``
        hits a pre-existing bug (#475 bug 9: the negation step overflows
        i64, leaving an empty number body).  Two indirect probes pinpoint
        INT64_MIN without tripping that bug:
          (a) the value is negative: ``@Int.0 < 0`` holds,
          (b) ``@Int.0 + 1`` equals -9223372036854775807 (INT64_MIN + 1),
              which IS printable via ``int_to_string``.
        Off-by-one on the guard (``f <= -2^63`` instead of ``f < -2^63``)
        would reject this valid value; an accidental truncation to zero
        or positive value would fail probe (a).
        """
        src = """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  match json_as_int(JNumber(0.0 - 9223372036854775808.0)) {
    Some(@Int) -> {
      -- Probe (a): value is negative.
      IO.print(bool_to_string(@Int.0 < 0));
      IO.print(",");
      -- Probe (b): value + 1 = INT64_MIN + 1 = -9223372036854775807.
      IO.print(int_to_string(@Int.0 + 1))
    },
    None -> IO.print("none")
  }
}
"""
        assert _run_io(src) == "true,-9223372036854775807"

    def test_json_as_int_boundary_just_below_minus_2_63(self) -> None:
        """The Float64 value strictly below -2^63 must return None.

        Float64 precision at magnitude ~2^63 has ulp = 2^(63-52) =
        2048, so the next representable double below -2^63 is
        -2^63 - 2048 = -9223372036854777856.0.  A literal like
        -9223372036854776832.0 (= -2^63 - 1024) is *not*
        representable: it's exactly halfway between -2^63 and the
        next-lower double, and round-to-nearest-even rounds it back
        to -2^63.  Using the true next-lower value pins the guard's
        strict-less-than behaviour at the boundary.
        """
        src = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  match json_as_int(JNumber(0.0 - 9223372036854777856.0)) {
    Some(@Int) -> 0,
    None -> 1
  }
}
"""
        assert _run(src) == 1

    def test_json_as_array(self) -> None:
        """JArray([1,2,3]) → Some(array of length 3)."""
        src = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Json = JArray([JNumber(1.0), JNumber(2.0), JNumber(3.0)]);
  match json_as_array(@Json.0) {
    Some(@Array<Json>) -> nat_to_int(array_length(@Array<Json>.0)),
    None -> 0
  }
}
"""
        assert _run(src) == 3

    def test_json_as_object_from_parse(self) -> None:
        """JObject value via json_parse → Some(map); Map is opaque
        handle so we only assert round-trip, not contents."""
        src = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  match json_parse("{\\"k\\":1}") {
    Err(@String) -> 0,
    Ok(@Json) ->
      match json_as_object(@Json.0) {
        Some(@Map<String, Json>) -> 1,
        None -> 0
      }
  }
}
"""
        assert _run(src) == 1

    def test_json_as_coercions_are_disjoint(self) -> None:
        """Every Layer-1 accessor returns None for every constructor
        except its own.  This is the invariant callers rely on when
        chaining coercions.
        """
        src = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  -- JString has no bool coercion
  let @Int = match json_as_bool(JString("true")) {
    Some(@Bool) -> -1,
    None -> 0
  };
  -- JBool has no number coercion
  let @Int = match json_as_number(JBool(true)) {
    Some(@Float64) -> -1,
    None -> @Int.0
  };
  -- JNumber has no string coercion
  let @Int = match json_as_string(JNumber(1.0)) {
    Some(@String) -> -1,
    None -> @Int.0
  };
  -- JNull has no array coercion
  let @Int = match json_as_array(JNull) {
    Some(@Array<Json>) -> -1,
    None -> @Int.0
  };
  @Int.0
}
"""
        assert _run(src) == 0

    # ----- Layer 2: json_get_* -----

    def test_json_get_string_hit(self) -> None:
        """{"name":"Alice"}/name → Some("Alice")."""
        src = """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  match json_parse("{\\"name\\":\\"Alice\\"}") {
    Err(@String) -> IO.print("ERR"),
    Ok(@Json) ->
      match json_get_string(@Json.0, "name") {
        Some(@String) -> IO.print(@String.0),
        None -> IO.print("?")
      }
  }
}
"""
        assert _run_io(src) == "Alice"

    def test_json_get_int_hit(self) -> None:
        """{"age":30}/age → Some(30)."""
        src = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  match json_parse("{\\"age\\":30}") {
    Err(@String) -> -1,
    Ok(@Json) ->
      match json_get_int(@Json.0, "age") {
        Some(@Int) -> @Int.0,
        None -> -1
      }
  }
}
"""
        assert _run(src) == 30

    def test_json_get_number_hit(self) -> None:
        """{"score":3.14}/score → Some(3.14)."""
        src = """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  match json_parse("{\\"score\\":3.14}") {
    Err(@String) -> IO.print("ERR"),
    Ok(@Json) ->
      match json_get_number(@Json.0, "score") {
        Some(@Float64) -> IO.print(float_to_string(@Float64.0)),
        None -> IO.print("?")
      }
  }
}
"""
        assert _run_io(src) == "3.14"

    def test_json_get_bool_hit(self) -> None:
        """{"active":true}/active → Some(true)."""
        src = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  match json_parse("{\\"active\\":true}") {
    Err(@String) -> -1,
    Ok(@Json) ->
      match json_get_bool(@Json.0, "active") {
        Some(@Bool) -> if @Bool.0 then { 1 } else { 0 },
        None -> -1
      }
  }
}
"""
        assert _run(src) == 1

    def test_json_get_array_hit(self) -> None:
        """{"tags":[1,2,3]}/tags → Some(array of length 3)."""
        src = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  match json_parse("{\\"tags\\":[1,2,3]}") {
    Err(@String) -> -1,
    Ok(@Json) ->
      match json_get_array(@Json.0, "tags") {
        Some(@Array<Json>) -> nat_to_int(array_length(@Array<Json>.0)),
        None -> -1
      }
  }
}
"""
        assert _run(src) == 3

    def test_json_get_missing_field(self) -> None:
        """Missing field → None."""
        src = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  match json_parse("{\\"name\\":\\"Alice\\"}") {
    Err(@String) -> -1,
    Ok(@Json) ->
      match json_get_int(@Json.0, "nope") {
        Some(@Int) -> -1,
        None -> 1
      }
  }
}
"""
        assert _run(src) == 1

    def test_json_get_wrong_type(self) -> None:
        """Present field with wrong type → None (not trap)."""
        src = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  match json_parse("{\\"name\\":\\"Alice\\"}") {
    Err(@String) -> -1,
    Ok(@Json) ->
      match json_get_int(@Json.0, "name") {
        Some(@Int) -> -1,
        None -> 1
      }
  }
}
"""
        assert _run(src) == 1

    def test_json_get_on_non_object(self) -> None:
        """json_get_X on a non-JObject Json returns None (because the
        underlying json_get returns None for non-objects).
        """
        src = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  -- JArray is a valid Json but not an object, so json_get_int returns None.
  match json_get_int(JArray([JNumber(1.0)]), "any") {
    Some(@Int) -> -1,
    None -> 1
  }
}
"""
        assert _run(src) == 1

    # ----- Import gating: accessors are pure-Vera, not host imports -----

    def test_accessors_do_not_force_json_parse_import(self) -> None:
        """A program that uses only json_as_* / json_get_* accessors
        must NOT import vera.json_parse or vera.json_stringify.  These
        accessors are pure-Vera prelude functions; the host imports
        are only for the parse/serialise boundary.

        Regression test: a future refactor that accidentally routes an
        accessor through a host import would make the compiled module
        pull in unused imports.  Caught here by the import table.
        """
        src = """\
public fn test(@Json -> @Option<String>)
  requires(true) ensures(true) effects(pure)
{
  match json_get_string(@Json.0, "k") {
    Some(@String) -> Some(@String.0),
    None -> json_as_string(@Json.0)
  }
}
"""
        result = _compile_ok(src)
        assert '(import "vera" "json_parse"' not in result.wat, (
            "json_as_* / json_get_* must not force the json_parse host "
            "import — they are pure-Vera prelude functions."
        )
        assert '(import "vera" "json_stringify"' not in result.wat, (
            "json_as_* / json_get_* must not force the json_stringify "
            "host import."
        )

    def test_layer2_accessors_do_not_force_json_imports(self) -> None:
        """Mirror: json_get_int / json_get_array also pure.  Separate
        test because the accessors have slightly different return-type
        shapes (i64 payload vs i32_pair Array) and codegen might
        conceivably diverge between them.
        """
        src = """\
public fn test(@Json -> @Option<Int>)
  requires(true) ensures(true) effects(pure)
{
  match json_get_int(@Json.0, "age") {
    Some(@Int) -> Some(@Int.0),
    None ->
      match json_get_array(@Json.0, "tags") {
        Some(@Array<Json>) -> Some(nat_to_int(array_length(@Array<Json>.0))),
        None -> None
      }
  }
}
"""
        result = _compile_ok(src)
        assert '(import "vera" "json_parse"' not in result.wat
        assert '(import "vera" "json_stringify"' not in result.wat

    def test_json_parse_does_force_its_host_import(self) -> None:
        """Complementary test: json_parse IS a host import, so a
        program using it SHOULD emit the corresponding import.  Pins
        the direction of the invariant — if this test ever fails
        without the previous two also failing, the check is wrong,
        not the implementation.
        """
        src = """\
public fn test(@String -> @Result<Json, String>)
  requires(true) ensures(true) effects(pure)
{ json_parse(@String.0) }
"""
        result = _compile_ok(src)
        assert '(import "vera" "json_parse"' in result.wat, (
            "json_parse IS a host import and its import table entry "
            "must be present when the function is referenced."
        )
