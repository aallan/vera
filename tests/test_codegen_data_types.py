"""Tests for vera.codegen — data_types (ADT metadata/constructors, match expressions, tuples, ADT string fields, generic-mono regressions).

Split from tests/test_codegen.py (#419). Shared helpers live in tests/codegen_helpers.py.
"""
from __future__ import annotations

import re

from vera.codegen import (
    execute,
)

from tests.codegen_helpers import (
    _IO_PRELUDE,
    _compile,
    _compile_ok,
    _compile_with_generator,
    _run,
    _run_io,
)


class TestAdtMetadata:
    """Test ADT constructor layout metadata registration."""

    def test_nullary_layout(self) -> None:
        """Nullary constructor: tag only, total_size = 8."""
        source = """\
private data Unit2 { MkUnit }

public fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{ 42 }
"""
        _result, gen = _compile_with_generator(source)
        layout = gen._adt_layouts["Unit2"]["MkUnit"]
        assert layout.tag == 0
        assert layout.field_offsets == ()
        assert layout.total_size == 8

    def test_single_int_field_layout(self) -> None:
        """Constructor with Int field: tag(4) + pad(4) + i64(8) = 16."""
        source = """\
private data Wrapper { Wrap(Int) }

public fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{ 42 }
"""
        _result, gen = _compile_with_generator(source)
        layout = gen._adt_layouts["Wrapper"]["Wrap"]
        assert layout.tag == 0
        assert layout.field_offsets == ((8, "i64"),)
        assert layout.total_size == 16

    def test_multiple_fields_layout(self) -> None:
        """Constructor with Int + Bool: tag(4) + pad(4) + i64(8) + i32(4) → 24."""
        source = """\
private data Pair { MkPair(Int, Bool) }

public fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{ 42 }
"""
        _result, gen = _compile_with_generator(source)
        layout = gen._adt_layouts["Pair"]["MkPair"]
        assert layout.tag == 0
        assert layout.field_offsets[0] == (8, "i64")   # Int at offset 8
        assert layout.field_offsets[1] == (16, "i32")   # Bool at offset 16
        assert layout.total_size == 24  # 20 aligned up to 24

    def test_multiple_constructors_tags(self) -> None:
        """Each constructor gets a sequential tag."""
        source = """\
private data Color { Red, Green, Blue }

public fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{ 42 }
"""
        _result, gen = _compile_with_generator(source)
        layouts = gen._adt_layouts["Color"]
        assert layouts["Red"].tag == 0
        assert layouts["Green"].tag == 1
        assert layouts["Blue"].tag == 2

    def test_float64_field_layout(self) -> None:
        """Constructor with Float64 field: tag(4) + pad(4) + f64(8) = 16."""
        source = """\
private data Box { MkBox(Float64) }

public fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{ 42 }
"""
        _result, gen = _compile_with_generator(source)
        layout = gen._adt_layouts["Box"]["MkBox"]
        assert layout.field_offsets == ((8, "f64"),)
        assert layout.total_size == 16

    def test_bool_field_layout(self) -> None:
        """Constructor with Bool field: tag(4) + i32(4) = 8."""
        source = """\
private data Toggle { MkToggle(Bool) }

public fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{ 42 }
"""
        _result, gen = _compile_with_generator(source)
        layout = gen._adt_layouts["Toggle"]["MkToggle"]
        assert layout.field_offsets == ((4, "i32"),)  # i32 aligns to 4
        assert layout.total_size == 8

    def test_type_param_is_pointer(self) -> None:
        """Type parameters map to i32 (pointer)."""
        source = """\
private data Box<T> { MkBox(T) }

public fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{ 42 }
"""
        _result, gen = _compile_with_generator(source)
        layout = gen._adt_layouts["Box"]["MkBox"]
        assert layout.field_offsets == ((4, "i32"),)  # T → pointer
        assert layout.total_size == 8

    def test_mixed_adt_constructors(self) -> None:
        """Option-like ADT: None is nullary, Some has a field."""
        source = """\
private data MyOption<T> { MyNone, MySome(T) }

public fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{ 42 }
"""
        _result, gen = _compile_with_generator(source)
        layouts = gen._adt_layouts["MyOption"]
        assert layouts["MyNone"].tag == 0
        assert layouts["MyNone"].field_offsets == ()
        assert layouts["MyNone"].total_size == 8
        assert layouts["MySome"].tag == 1
        assert layouts["MySome"].field_offsets == ((4, "i32"),)  # T → pointer
        assert layouts["MySome"].total_size == 8


# =====================================================================
# C6f: ADT constructor codegen
# =====================================================================


class TestAdtConstructors:
    """Test compilation of ADT constructor expressions to WASM."""

    def test_nullary_constructor_returns_pointer(self) -> None:
        """A nullary constructor (Red) compiles and returns an i32 >= 0."""
        source = """\
private data Color { Red, Green, Blue }

public fn make_red(-> @Color)
  requires(true) ensures(true) effects(pure)
{ Red }
"""
        result = _compile_ok(source)
        assert "make_red" in result.exports
        exec_result = execute(result, fn_name="make_red")
        assert exec_result.value is not None
        assert exec_result.value >= 0  # heap pointer

    def test_nullary_different_tags(self) -> None:
        """Different nullary constructors compile to distinct functions."""
        source = """\
private data Color { Red, Green, Blue }

public fn make_red(-> @Color)
  requires(true) ensures(true) effects(pure)
{ Red }

public fn make_green(-> @Color)
  requires(true) ensures(true) effects(pure)
{ Green }

public fn make_blue(-> @Color)
  requires(true) ensures(true) effects(pure)
{ Blue }
"""
        result = _compile_ok(source)
        assert "make_red" in result.exports
        assert "make_green" in result.exports
        assert "make_blue" in result.exports

    def test_constructor_with_int_field(self) -> None:
        """Constructor with Int field: Wrap(@Int.0) compiles."""
        source = """\
private data Wrapper { Wrap(Int) }

public fn wrap(@Int -> @Wrapper)
  requires(true) ensures(true) effects(pure)
{ Wrap(@Int.0) }
"""
        result = _compile_ok(source)
        assert "wrap" in result.exports
        exec_result = execute(result, fn_name="wrap", args=[42])
        assert exec_result.value is not None
        assert exec_result.value >= 0

    def test_constructor_with_bool_field(self) -> None:
        """Constructor with Bool field: MkToggle(@Bool.0) compiles."""
        source = """\
private data Toggle { MkToggle(Bool) }

public fn toggle(@Bool -> @Toggle)
  requires(true) ensures(true) effects(pure)
{ MkToggle(@Bool.0) }
"""
        result = _compile_ok(source)
        assert "toggle" in result.exports
        exec_result = execute(result, fn_name="toggle", args=[1])
        assert exec_result.value is not None
        assert exec_result.value >= 0

    def test_option_none(self) -> None:
        """None as Option<Int> compiles (nullary constructor)."""
        source = """\
private data Option<T> { None, Some(T) }

public fn make_none(-> @Option<Int>)
  requires(true) ensures(true) effects(pure)
{ None }
"""
        result = _compile_ok(source)
        assert "make_none" in result.exports
        exec_result = execute(result, fn_name="make_none")
        assert exec_result.value is not None

    def test_option_some(self) -> None:
        """Some(@Int.0) as Option<Int> compiles."""
        source = """\
private data Option<T> { None, Some(T) }

public fn make_some(@Int -> @Option<Int>)
  requires(true) ensures(true) effects(pure)
{ Some(@Int.0) }
"""
        result = _compile_ok(source)
        assert "make_some" in result.exports
        exec_result = execute(result, fn_name="make_some", args=[99])
        assert exec_result.value is not None
        assert exec_result.value >= 0

    def test_wat_contains_alloc_call(self) -> None:
        """WAT output for constructor contains call $alloc."""
        source = """\
private data Color { Red, Green, Blue }

public fn make_red(-> @Color)
  requires(true) ensures(true) effects(pure)
{ Red }
"""
        result = _compile_ok(source)
        assert "call $alloc" in result.wat

    def test_wat_contains_store_with_offset(self) -> None:
        """WAT output for Some(x) contains field store with offset."""
        source = """\
private data Wrapper { Wrap(Int) }

public fn wrap(@Int -> @Wrapper)
  requires(true) ensures(true) effects(pure)
{ Wrap(@Int.0) }
"""
        result = _compile_ok(source)
        assert "i64.store offset=8" in result.wat

    def test_nullary_tag_store(self) -> None:
        """WAT for Red (tag=0) stores tag 0; Green (tag=1) stores tag 1."""
        source = """\
private data Color { Red, Green, Blue }

public fn make_green(-> @Color)
  requires(true) ensures(true) effects(pure)
{ Green }
"""
        result = _compile_ok(source)
        # Green has tag=1, so WAT should contain i32.const 1 before i32.store
        assert "i32.const 1" in result.wat
        assert "i32.store\n" in result.wat or "i32.store)" in result.wat or "i32.store" in result.wat

    def test_constructor_in_let_binding(self) -> None:
        """Constructor result in a let binding compiles."""
        source = """\
private data Wrapper { Wrap(Int) }

public fn make_wrap(@Int -> @Wrapper)
  requires(true) ensures(true) effects(pure)
{
  let @Wrapper = Wrap(@Int.0);
  @Wrapper.0
}
"""
        result = _compile_ok(source)
        assert "make_wrap" in result.exports
        exec_result = execute(result, fn_name="make_wrap", args=[7])
        assert exec_result.value is not None

    def test_constructor_in_if_branches(self) -> None:
        """Constructors in both branches of if-then-else compile."""
        source = """\
private data Option<T> { None, Some(T) }

public fn maybe(@Bool -> @Option<Int>)
  requires(true) ensures(true) effects(pure)
{
  if @Bool.0 then { Some(42) }
  else { None }
}
"""
        result = _compile_ok(source)
        assert "maybe" in result.exports
        # Both branches should produce valid pointers
        exec_true = execute(result, fn_name="maybe", args=[1])
        exec_false = execute(result, fn_name="maybe", args=[0])
        assert exec_true.value is not None
        assert exec_false.value is not None

    def test_adt_param_compiles(self) -> None:
        """Function taking ADT param uses (param $p0 i32) in WAT."""
        source = """\
private data Color { Red, Green, Blue }

public fn identity(@Color -> @Color)
  requires(true) ensures(true) effects(pure)
{ @Color.0 }
"""
        result = _compile_ok(source)
        assert "identity" in result.exports
        assert "(param" in result.wat  # at least one i32 param


# =====================================================================
# C6g: Match expression codegen
# =====================================================================


class TestMatchExpressions:
    """Test compilation of match expressions to WASM."""

    def test_match_option_none_arm(self) -> None:
        """Match on None arm returns 0."""
        source = """\
private data Option<T> { None, Some(T) }

public fn test_none(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Option<Int> = None;
  match @Option<Int>.0 {
    None -> 0,
    Some(@Int) -> @Int.0
  }
}
"""
        assert _run(source, fn="test_none") == 0

    def test_match_option_some_arm(self) -> None:
        """Match on Some arm extracts value."""
        source = """\
private data Option<T> { None, Some(T) }

public fn test_some(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Option<Int> = Some(42);
  match @Option<Int>.0 {
    None -> 0,
    Some(@Int) -> @Int.0
  }
}
"""
        assert _run(source, fn="test_some") == 42

    def test_match_color_red(self) -> None:
        """Match on Red arm returns 0."""
        source = """\
private data Color { Red, Green, Blue }

public fn test_red(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Color = Red;
  match @Color.0 {
    Red -> 0,
    Green -> 1,
    Blue -> 2
  }
}
"""
        assert _run(source, fn="test_red") == 0

    def test_match_color_green(self) -> None:
        """Match on Green arm returns 1."""
        source = """\
private data Color { Red, Green, Blue }

public fn test_green(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Color = Green;
  match @Color.0 {
    Red -> 0,
    Green -> 1,
    Blue -> 2
  }
}
"""
        assert _run(source, fn="test_green") == 1

    def test_match_color_blue(self) -> None:
        """Match on Blue arm returns 2."""
        source = """\
private data Color { Red, Green, Blue }

public fn test_blue(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Color = Blue;
  match @Color.0 {
    Red -> 0,
    Green -> 1,
    Blue -> 2
  }
}
"""
        assert _run(source, fn="test_blue") == 2

    def test_match_extracts_int(self) -> None:
        """Match extracts Int field and uses it in body."""
        source = """\
private data Option<T> { None, Some(T) }

public fn test(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Option<Int> = Some(99);
  match @Option<Int>.0 {
    None -> 0,
    Some(@Int) -> @Int.0 + 1
  }
}
"""
        assert _run(source, fn="test") == 100

    def test_match_extracts_bool(self) -> None:
        """Match extracts Bool field."""
        source = """\
private data Toggle { MkToggle(Bool) }

public fn test(-> @Bool)
  requires(true) ensures(true) effects(pure)
{
  let @Toggle = MkToggle(true);
  match @Toggle.0 {
    MkToggle(@Bool) -> @Bool.0
  }
}
"""
        assert _run(source, fn="test") == 1

    def test_match_two_fields(self) -> None:
        """Match extracts first of two fields."""
        source = """\
private data Pair { MkPair(Int, Bool) }

public fn test(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Pair = MkPair(42, true);
  match @Pair.0 {
    MkPair(@Int, @Bool) -> @Int.0
  }
}
"""
        assert _run(source, fn="test") == 42

    def test_match_wildcard_catchall(self) -> None:
        """Wildcard catch-all matches None."""
        source = """\
private data Option<T> { None, Some(T) }

public fn test(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Option<Int> = None;
  match @Option<Int>.0 {
    Some(@Int) -> @Int.0,
    _ -> 0
  }
}
"""
        assert _run(source, fn="test") == 0

    def test_match_wildcard_only(self) -> None:
        """Single wildcard arm on Int."""
        source = """\
public fn test(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  match @Int.0 {
    _ -> 42
  }
}
"""
        assert _run(source, fn="test", args=[999]) == 42

    def test_match_wildcard_sub_pattern(self) -> None:
        """Wildcard inside constructor sub-pattern."""
        source = """\
private data Option<T> { None, Some(T) }

public fn test(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Option<Int> = Some(77);
  match @Option<Int>.0 {
    Some(_) -> 1,
    None -> 0
  }
}
"""
        assert _run(source, fn="test") == 1

    def test_match_bool_true(self) -> None:
        """Bool match on true arm."""
        source = """\
public fn test(@Bool -> @Int)
  requires(true) ensures(true) effects(pure)
{
  match @Bool.0 {
    true -> 1,
    false -> 0
  }
}
"""
        assert _run(source, fn="test", args=[1]) == 1

    def test_match_bool_false(self) -> None:
        """Bool match on false arm."""
        source = """\
public fn test(@Bool -> @Int)
  requires(true) ensures(true) effects(pure)
{
  match @Bool.0 {
    true -> 1,
    false -> 0
  }
}
"""
        assert _run(source, fn="test", args=[0]) == 0

    def test_match_int_literal(self) -> None:
        """Int literal match, first arm."""
        source = """\
public fn test(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  match @Int.0 {
    0 -> 100,
    1 -> 200,
    _ -> 300
  }
}
"""
        assert _run(source, fn="test", args=[0]) == 100

    def test_match_int_second_arm(self) -> None:
        """Int literal match, second arm."""
        source = """\
public fn test(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  match @Int.0 {
    0 -> 100,
    1 -> 200,
    _ -> 300
  }
}
"""
        assert _run(source, fn="test", args=[1]) == 200

    def test_match_int_wildcard_fallback(self) -> None:
        """Int literal match, wildcard fallback."""
        source = """\
public fn test(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  match @Int.0 {
    0 -> 100,
    1 -> 200,
    _ -> 300
  }
}
"""
        assert _run(source, fn="test", args=[99]) == 300

    def test_match_binding_catchall(self) -> None:
        """Binding pattern as catch-all."""
        source = """\
private data Option<T> { None, Some(T) }

public fn test(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Option<Int> = None;
  match @Option<Int>.0 {
    Some(@Int) -> @Int.0,
    @Option<Int> -> 0
  }
}
"""
        assert _run(source, fn="test") == 0

    def test_match_in_let_binding(self) -> None:
        """Match result used in a let binding."""
        source = """\
private data Option<T> { None, Some(T) }

public fn test(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Option<Int> = Some(10);
  let @Int = match @Option<Int>.0 {
    None -> 0,
    Some(@Int) -> @Int.0
  };
  @Int.0 + 1
}
"""
        assert _run(source, fn="test") == 11

    def test_match_wat_contains_tag_load(self) -> None:
        """WAT output for ADT match contains i32.load (tag load)."""
        source = """\
private data Color { Red, Green, Blue }

public fn test(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Color = Red;
  match @Color.0 {
    Red -> 0,
    Green -> 1,
    Blue -> 2
  }
}
"""
        result = _compile_ok(source)
        assert "i32.load" in result.wat

    def test_match_function_compiles(self) -> None:
        """Function with match is now exported (not skipped)."""
        source = """\
private data Option<T> { None, Some(T) }

public fn unwrap_or(@Option<Int> -> @Int)
  requires(true) ensures(true) effects(pure)
{
  match @Option<Int>.0 {
    None -> 0,
    Some(@Int) -> @Int.0
  }
}
"""
        result = _compile_ok(source)
        assert "unwrap_or" in result.exports

    def test_match_nested_some(self) -> None:
        """Nested constructor: Cons(Some(@Int), _) extracts the inner Int."""
        source = """\
private data Option<T> { None, Some(T) }
private data List<T> { Nil, Cons(T, List<T>) }

public fn first_val(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @List<Option<Int>> = Cons(Some(42), Nil);
  match @List<Option<Int>>.0 {
    Cons(Some(@Int), _) -> @Int.0,
    _ -> 0
  }
}
"""
        assert _run(source, fn="first_val") == 42

    def test_match_nested_none(self) -> None:
        """Nested nullary: Cons(None, _) arm is selected."""
        source = """\
private data Option<T> { None, Some(T) }
private data List<T> { Nil, Cons(T, List<T>) }

public fn test_none(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @List<Option<Int>> = Cons(None, Nil);
  match @List<Option<Int>>.0 {
    Cons(Some(@Int), _) -> @Int.0,
    Cons(None, _) -> 99,
    _ -> 0
  }
}
"""
        assert _run(source, fn="test_none") == 99

    def test_match_nested_multi_field(self) -> None:
        """Nested constructor with both fields used."""
        source = """\
private data Option<T> { None, Some(T) }
private data Pair<A, B> { MkPair(A, B) }

public fn test(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Pair<Option<Int>, Int> = MkPair(Some(10), 5);
  match @Pair<Option<Int>, Int>.0 {
    MkPair(Some(@Int), _) -> @Int.0,
    _ -> 0
  }
}
"""
        assert _run(source, fn="test") == 10

    def test_match_nested_different_arms(self) -> None:
        """Different nesting per arm selects correct arm."""
        source = """\
private data Option<T> { None, Some(T) }
private data List<T> { Nil, Cons(T, List<T>) }

public fn test(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @List<Option<Int>> = Cons(Some(77), Nil);
  match @List<Option<Int>>.0 {
    Cons(None, _) -> 0,
    Cons(Some(@Int), _) -> @Int.0,
    _ -> 99
  }
}
"""
        assert _run(source, fn="test") == 77

    def test_match_nested_fallthrough(self) -> None:
        """Nested Some doesn't match None, falls through to wildcard."""
        source = """\
private data Option<T> { None, Some(T) }
private data List<T> { Nil, Cons(T, List<T>) }

public fn test(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @List<Option<Int>> = Cons(None, Nil);
  match @List<Option<Int>>.0 {
    Cons(Some(@Int), _) -> @Int.0,
    _ -> 55
  }
}
"""
        assert _run(source, fn="test") == 55


# =====================================================================
# Tuple codegen
# =====================================================================


class TestTuple:
    """Tuple construction, match destructuring, and LetDestruct codegen."""

    def test_tuple_int_int(self) -> None:
        """Tuple(10, 20) — match destructuring, @Int.0 is most recent (20)."""
        source = """\
public fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Tuple<Int, Int> = Tuple(10, 20);
  match @Tuple<Int, Int>.0 {
    Tuple(@Int, @Int) -> @Int.0
  }
}
"""
        # @Int.0 = most recently bound = second field = 20
        assert _run(source, fn="f") == 20

    def test_tuple_int_int_sum(self) -> None:
        """Tuple(10, 20) — match destructure and sum both fields."""
        source = """\
public fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Tuple<Int, Int> = Tuple(10, 20);
  match @Tuple<Int, Int>.0 {
    Tuple(@Int, @Int) -> @Int.0 + @Int.1
  }
}
"""
        assert _run(source, fn="f") == 30

    def test_tuple_int_string(self) -> None:
        """Tuple(42, "hello") — mixed Int and String fields."""
        source = _IO_PRELUDE + """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Tuple<Int, String> = Tuple(42, "hello");
  match @Tuple<Int, String>.0 {
    Tuple(@Int, @String) -> IO.print(@String.0)
  }
}
"""
        assert _run_io(source, fn="main") == "hello"

    def test_tuple_let_destruct_int(self) -> None:
        """let Tuple<@Int, @Int> = Tuple(42, 99); @Int.0 → 99 (most recent)."""
        source = """\
public fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let Tuple<@Int, @Int> = Tuple(42, 99);
  @Int.0
}
"""
        # @Int.0 = most recently bound = second field = 99
        assert _run(source, fn="f") == 99

    def test_tuple_let_destruct_second(self) -> None:
        """let Tuple<@Int, @Int> = Tuple(42, 99); @Int.1 → 42 (first field)."""
        source = """\
public fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let Tuple<@Int, @Int> = Tuple(42, 99);
  @Int.1
}
"""
        # @Int.1 = earlier binding = first field = 42
        assert _run(source, fn="f") == 42

    def test_tuple_let_destruct_string(self) -> None:
        """LetDestruct Tuple with String field."""
        source = _IO_PRELUDE + """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let Tuple<@Int, @String> = Tuple(42, "world");
  IO.print(@String.0)
}
"""
        assert _run_io(source, fn="main") == "world"

    def test_tuple_three_fields(self) -> None:
        """3-field Tuple: Tuple(100, 5, 3) — sum all fields."""
        source = """\
public fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Tuple<Int, Int, Int> = Tuple(100, 5, 3);
  match @Tuple<Int, Int, Int>.0 {
    Tuple(@Int, @Int, @Int) -> @Int.0 + @Int.1 + @Int.2
  }
}
"""
        assert _run(source, fn="f") == 108

    def test_tuple_in_result(self) -> None:
        """Ok(Tuple(1, 2)) — nested Tuple inside Result."""
        source = """\
private data Result<T, E> { Ok(T), Err(E) }

public fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Result<Tuple<Int, Int>, Int> = Ok(Tuple(10, 20));
  match @Result<Tuple<Int, Int>, Int>.0 {
    Ok(@Tuple<Int, Int>) -> match @Tuple<Int, Int>.0 {
      Tuple(@Int, @Int) -> @Int.0 + @Int.1
    },
    Err(@Int) -> 0 - 1
  }
}
"""
        assert _run(source, fn="f") == 30

    def test_let_destruct_user_adt(self) -> None:
        """LetDestruct with a user-defined single-constructor ADT."""
        source = """\
private data Pair<A, B> { Pair(A, B) }

public fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let Pair<@Int, @Int> = Pair(7, 8);
  @Int.0 + @Int.1
}
"""
        assert _run(source, fn="f") == 15

    def test_let_destruct_urlparts(self) -> None:
        """LetDestruct with UrlParts (5-field ADT, knock-on effect)."""
        source = _IO_PRELUDE + """\
private data UrlParts { UrlParts(String, String, String, String, String) }

public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let UrlParts<@String, @String, @String, @String, @String> =
    UrlParts("https", "example.com", "/path", "q=1", "frag");
  IO.print(@String.4)
}
"""
        # @String.4 = deepest binding = first field = "https"
        assert _run_io(source, fn="main") == "https"


class TestAdtStringFields:
    """ADT constructors with String/Array fields (bug #266)."""

    def test_wrap_one_string(self) -> None:
        src = """
effect IO { op print(String -> Unit); }
private data Wrap { Wrap(String) }
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  match Wrap("hello") {
    Wrap(@String) -> IO.print(@String.0)
  }
}
"""
        assert _run_io(src) == "hello"

    def test_pair_two_strings(self) -> None:
        src = """
effect IO { op print(String -> Unit); }
private data Pair { Pair(String, String) }
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  match Pair("hello", "world") {
    Pair(@String, @String) -> {
      IO.print(@String.1);
      IO.print(@String.0)
    }
  }
}
"""
        assert _run_io(src) == "helloworld"

    def test_mixed_int_string(self) -> None:
        src = """
effect IO { op print(String -> Unit); }
private data Mixed { Mixed(Int, String) }
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  match Mixed(42, "hi") {
    Mixed(@Int, @String) -> {
      IO.print(to_string(@Int.0));
      IO.print(@String.0)
    }
  }
}
"""
        assert _run_io(src) == "42hi"

    def test_multi_constructor_string(self) -> None:
        src = """
effect IO { op print(String -> Unit); }
private data Either { Left(String), Right(String) }
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  match Left("left") {
    Left(@String) -> IO.print(@String.0),
    Right(@String) -> IO.print(@String.0)
  };
  match Right("right") {
    Left(@String) -> IO.print(@String.0),
    Right(@String) -> IO.print(@String.0)
  }
}
"""
        assert _run_io(src) == "leftright"

    def test_five_string_fields(self) -> None:
        src = """
effect IO { op print(String -> Unit); }
private data Parts { Parts(String, String, String, String, String) }
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  match Parts("a", "b", "c", "d", "e") {
    Parts(@String, @String, @String, @String, @String) -> {
      IO.print(@String.4);
      IO.print(@String.3);
      IO.print(@String.2);
      IO.print(@String.1);
      IO.print(@String.0)
    }
  }
}
"""
        assert _run_io(src) == "abcde"


class TestEqConstraintParameterizedAdtName767:
    """PR #767 review — an `Eq`-constrained generic called with a
    parameterized-ADT slot ref (`@Box<Int>.0`) must not spuriously fail the
    `Eq` ability check.

    `_check_constraints` infers the constrained type var's concrete name from
    the argument; a `SlotRef` with type args yields the *parameterized* name
    `Box<Int>`, but `_adt_layouts` (and thus `_adt_satisfies_eq`) is keyed by the
    bare ADT name `Box`.  Pre-fix the layout lookup missed and codegen emitted
    `[E613] Type 'Box<Int>' does not satisfy ability 'Eq'`, rejecting a valid
    program — even though the same ADT is accepted when inferred from a
    constructor (`MkBox(...)`, which yields the bare `Box`).  `_adt_satisfies_eq`
    now splits the parameterized name into base + type args, looks up the bare
    layout, and validates each type-parameter field against its concrete type
    argument — so `Box<Int>` derives `Eq` (Int is scalar) while `Box<Array<Int>>`
    does not (`Array` is not `Eq`).  (`String` itself *is* `Eq`, just not as a
    scalar ADT field — the scalar-only auto-derivation basis, and the choice of
    `Array<Int>` over `String` for the unambiguous reject fixture, is tracked in
    #773.)  (A constructor-inferred type still resolves to the bare `Box` in the
    monomorphizer, so this type-arg validation only reaches the slot-ref /
    parameterized-name path.)
    """

    _SRC = """
public data Box<T> { MkBox(T) }

private forall<T where Eq<T>> fn eq2(@T, @T -> @Bool)
  requires(true) ensures(true) effects(pure)
{ @T.1 == @T.0 }

public fn main(@Unit -> @Bool)
  requires(true) ensures(true) effects(pure)
{
  let @Box<Int> = MkBox(1);
  eq2(@Box<Int>.0, @Box<Int>.0)
}
"""

    def test_eq_generic_over_parameterized_adt_slotref_compiles(self) -> None:
        """Compiles without a spurious E613 (pre-fix the parameterized
        `Box<Int>` name missed the bare-keyed layout and was rejected)."""
        result = _compile(self._SRC)
        e613 = [
            d for d in result.diagnostics
            if d.severity == "error" and d.error_code == "E613"
        ]
        assert not e613, f"spurious E613: {[d.description for d in e613]}"

    def test_eq_generic_over_parameterized_adt_slotref_runs(self) -> None:
        """The Eq derivation works at run time: `MkBox(1) == MkBox(1)` -> true."""
        assert _run(self._SRC) == 1

    _REJECT_SRC = """
public data Box<T> { MkBox(T) }

private forall<T where Eq<T>> fn eq2(@T, @T -> @Bool)
  requires(true) ensures(true) effects(pure)
{ @T.1 == @T.0 }

public fn main(@Unit -> @Bool)
  requires(true) ensures(true) effects(pure)
{
  let @Box<Array<Int>> = MkBox([1, 2, 3]);
  eq2(@Box<Array<Int>>.0, @Box<Array<Int>>.0)
}
"""

    def test_eq_generic_over_non_eq_parameterized_adt_rejected(self) -> None:
        """Type-arg validation is sound, not just a bare-name strip: `Box<Array<Int>>`
        (a non-`Eq` `Array` type argument) is correctly REJECTED with E613, where a
        naive strip-to-`Box` would have false-accepted it.  `Array` is used rather
        than `String` for an UNAMBIGUOUS non-`Eq` arg: `String` itself *is* `Eq`,
        just not as a scalar ADT field — the scalar-only auto-derivation basis (and
        its String false-reject / nested-ADT false-accept) is tracked in #773."""
        result = _compile(self._REJECT_SRC)
        e613 = [
            d for d in result.diagnostics
            if d.severity == "error" and d.error_code == "E613"
        ]
        assert e613, "Box<Array<Int>> must fail Eq (Array is not Eq)"


class TestGenericMonoSuffixFromSlotRef604:
    """`#604` / `#655` — generic prelude combinator mono clones now
    produce the correct type-arg suffix when the closure argument is
    a ``SlotRef`` typed as an FnType alias (e.g. ``@Doubler.0``).

    Pre-fix `_unify_param_arg` in `vera/codegen/monomorphize.py` had
    an AnonFn-specific alias-resolution path; `SlotRef` args typed as
    FnType aliases skipped that path and left the closure's return
    type variable unbound.  The unbound type var fell to the
    ``"Bool"`` phantom-var fallback at result-building time, producing
    mono suffixes like ``option_map$Int_Bool`` instead of
    ``option_map$Int_Int`` and trapping at runtime with ``indirect
    call type mismatch``.

    Post-fix (this commit): both AnonFn literals AND SlotRef-typed-as-
    FnType-alias args flow through the shared ``_resolve_arg_fn_shape``
    helper, binding the closure's return type uniformly.

    Two tests below pin the contract:

    1. ``option_map(opt, fn_alias_slot)`` produces ``option_map$Int_Int``
       and runs correctly (not a runtime trap).
    2. The template-only ``[E602]``/``[E604]`` warnings on the prelude
       generics are suppressed in programs that successfully call them
       — audit recommendation 2 from #604.
    """

    _SLOT_FN_SRC = """
type Doubler = fn(Int -> Int) effects(pure);

private fn use_map(@Option<Int>, @Doubler -> @Option<Int>)
  requires(true) ensures(true) effects(pure)
{
  option_map(@Option<Int>.0, @Doubler.0)
}

public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  option_unwrap_or(use_map(Some(10), fn(@Int -> @Int) effects(pure) { @Int.0 * 2 }), 0)
}
"""

    def test_mono_suffix_correct_for_slotref_fn_alias_arg(self) -> None:
        """`option_map(opt, @Doubler.0)` where ``Doubler = fn(Int -> Int)``
        produces a mono clone with suffix ``$Int_Int`` (not ``$Int_Bool``)
        and runs without trapping.

        Pre-fix this produced ``option_map$Int_Bool`` and trapped at
        runtime with ``wasm trap: indirect call type mismatch`` because
        the closure's i64 return mismatched the i32 (Bool) the wrongly-
        suffixed mono clone expected.

        CR-2 on PR #659 — the WAT-only assertions pinned suffix
        correctness but didn't catch the actual user-visible failure
        mode (the runtime trap).  Add a runtime execution assertion
        so a regression in indirect-call signature wiring fails the
        test rather than silently slipping through with the right
        suffix in WAT but wrong execution.
        """
        result = _compile_ok(self._SLOT_FN_SRC)
        # The compiled module should contain the correctly-suffixed
        # mono clone, not the wrongly-suffixed one.  Use
        # boundary-safe regex (CR-10 on PR #659) so longer variants
        # like `$option_map$Int_Int_X` don't slip past as substrings
        # of the expected token.
        wat = result.wat or ""
        assert re.search(r"\$option_map\$Int_Int(?![A-Za-z0-9_])", wat), (
            f"Expected correctly-suffixed mono clone "
            f"`$option_map$Int_Int` in WAT; got WAT containing "
            f"option_map suffixes: "
            f"{[line for line in wat.splitlines() if 'option_map$' in line]}"
        )
        assert not re.search(r"\$option_map\$Int_Bool(?![A-Za-z0-9_])", wat), (
            "Wrong-suffix mono clone `$option_map$Int_Bool` "
            "should not appear post-#604 fix; found in WAT"
        )
        # F8 on PR #659 review — independently pin the WASM-side
        # call-site rewriter (`vera/wasm/calls.py::_resolve_arg_fn_shape_wasm`
        # + `_infer_fn_alias_type_args_wasm`).  The function
        # definition `(func $option_map$Int_Int ...)` is emitted by
        # the monomorphizer at Pass 1.5; the `call` instruction is
        # emitted later by the WASM call-site rewriter, which has
        # an independent SlotRef-FnType-alias resolution path.  A
        # regression where Pass 1.5 produces the right clone but
        # the rewriter mangles the call to a different name would
        # pass the function-definition assertion above but fail at
        # WASM validation with `unknown function $option_map$<wrong>`.
        # Assert both names match by counting `call $option_map$Int_Int`
        # (or `return_call $option_map$Int_Int`) occurrences.
        call_pattern = (
            r"(?:^|\s)(?:return_)?call\s+\$option_map\$Int_Int"
            r"(?![A-Za-z0-9_])"
        )
        assert re.search(call_pattern, wat, re.MULTILINE), (
            f"Expected a `call $option_map$Int_Int` (or "
            f"`return_call`) instruction in WAT — without it the "
            f"call-site rewriter's mangled name doesn't match the "
            f"mono clone's definition.  Got option_map references: "
            f"{[line.strip() for line in wat.splitlines() if 'option_map' in line]}"
        )
        # Runtime pin: execute and confirm no trap.  `Some(10) * 2 = 20`.
        # Pre-fix this would have trapped with
        # `wasm trap: indirect call type mismatch`.
        exec_result = execute(result, fn_name="main")
        assert exec_result.value == 20, (
            f"Expected main() to return 20 (Some(10) * 2 unwrapped); "
            f"got {exec_result.value!r}.  A non-20 result OR a trap "
            f"signals indirect-call signature regression."
        )

    def test_parameterised_alias_substitutes_type_args(self) -> None:
        """`option_map(opt, @Mapper<Int>.0)` where
        ``type Mapper<T> = fn(T -> T)`` substitutes ``T → Int`` in
        the alias body before unifying against the generic call's
        ``OptionMapFn<A, B>`` param.

        CR-4 / CR-5 on PR #659: without substitution, the
        ``_resolve_arg_fn_shape`` helper returned the raw alias body
        ``fn(T -> T)`` and the downstream
        ``_infer_fn_alias_type_args`` matcher bound alias-local names
        (``A → T``, ``B → T``) instead of concrete ones.  The mono
        suffix would have been ``option_map$T_T`` rather than
        ``option_map$Int_Int`` — wrong shape, wouldn't match the
        clone Pass 1.5 registered, runtime trap.
        """
        src = """
type Mapper<T> = fn(T -> T) effects(pure);

private fn use_map(@Option<Int>, @Mapper<Int> -> @Option<Int>)
  requires(true) ensures(true) effects(pure)
{
  option_map(@Option<Int>.0, @Mapper<Int>.0)
}

public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  option_unwrap_or(use_map(Some(7), fn(@Int -> @Int) effects(pure) { @Int.0 * 3 }), 0)
}
"""
        result = _compile_ok(src)
        wat = result.wat or ""
        # Boundary-safe regex (CR-10 on PR #659) — see sibling test.
        assert re.search(r"\$option_map\$Int_Int(?![A-Za-z0-9_])", wat), (
            f"Expected `$option_map$Int_Int` from parameterised "
            f"alias `Mapper<Int>`; got option_map suffixes: "
            f"{[line for line in wat.splitlines() if 'option_map$' in line]}"
        )
        # Negative pin (CR-9 on PR #659): the unsubstituted alias-
        # local-name clone must not be emitted alongside the correct
        # one.  A bug that produced both (e.g. partial substitution
        # leaking the raw alias body into a second registration) would
        # otherwise slip past the positive assertion.
        assert not re.search(r"\$option_map\$T_T(?![A-Za-z0-9_])", wat), (
            "Unsubstituted parameterised-alias clone "
            "`$option_map$T_T` should not appear after the "
            "`T → Int` substitution fix; found in WAT"
        )
        # Runtime pin — `Some(7) * 3 = 21`.
        exec_result = execute(result, fn_name="main")
        assert exec_result.value == 21

    def test_template_warning_suppressed_when_mono_clone_compiles(
        self,
    ) -> None:
        """Audit recommendation 2 from #604: template-only `[E602]` /
        `[E604]` warnings on a generic decl are suppressed when at
        least one mono clone of that decl successfully compiles.

        Pre-fix every program that imported the prelude saw 5 spurious
        warnings about ``option_unwrap_or`` / ``option_map`` / etc.
        even when those functions worked end-to-end via mono.  The
        warnings were misleading (they suggested a problem when there
        was none) and drowned out genuine `[E602]` skips in the
        Layer 1 e602 gate (#656).

        Post-fix the post-compile suppression pass in
        ``vera/codegen/core.py::compile_program`` drops the spurious
        warnings.  Programs that never call a given generic still see
        the warning (preserving the "this generic can't compile and
        you're never using a mono clone" signal).
        """
        result = _compile_ok(self._SLOT_FN_SRC)
        warnings = [d for d in result.diagnostics if d.severity == "warning"]
        # The two generics actually called in `main` — `option_map`
        # and `option_unwrap_or` — must not appear in template-only
        # warning diagnostics.
        for fn_name in ("option_map", "option_unwrap_or"):
            offending = [
                d for d in warnings
                if d.error_code in {"E602", "E604", "E605"}
                and d.description.startswith(f"Function '{fn_name}' ")
            ]
            assert not offending, (
                f"Template-only warning for '{fn_name}' should be "
                f"suppressed (mono clones compiled); got: "
                f"{[d.description for d in offending]}"
            )

    def test_template_warning_NOT_suppressed_when_generic_never_called(
        self,
    ) -> None:
        """Negative control for the suppression pass.

        A user-defined generic ``forall<T>`` decl with a bare ``@T``
        parameter that is **never called** still emits its template
        warning.  Pre-fix this would have emitted `[E604]` ("function
        has unsupported parameter type") for every prelude generic on
        every compile; post-fix the suppression pass only fires when
        at least one mono clone of the generic actually compiled
        (`compiled_mono_bases` in
        `vera/codegen/core.py::compile_program`).  An over-broad
        suppressor that dropped *all* template warnings would pass
        the sibling test above but fail this one.

        CR-7 on PR #659.
        """
        src = """
private forall<T> fn unused_generic(@T -> @T)
  requires(true) ensures(true) effects(pure)
{
  @T.0
}

public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  42
}
"""
        result = _compile_ok(src)
        warnings = [d for d in result.diagnostics if d.severity == "warning"]
        offending = [
            d for d in warnings
            if d.error_code in {"E602", "E604", "E605"}
            and d.description.startswith("Function 'unused_generic' ")
        ]
        assert offending, (
            f"Expected `unused_generic` template warning to fire (no "
            f"mono clone exists since the generic is never called); "
            f"got warnings: "
            f"{[d.description for d in warnings]}"
        )
