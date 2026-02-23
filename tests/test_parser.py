"""Parser tests — verify that valid Vera programs parse without error."""

from pathlib import Path

import pytest

from vera.parser import parse, parse_file
from vera.errors import ParseError

EXAMPLES_DIR = Path(__file__).parent.parent / "examples"


# =====================================================================
# Example file tests
# =====================================================================


@pytest.mark.parametrize(
    "filename",
    [f.name for f in sorted(EXAMPLES_DIR.glob("*.vera"))],
)
def test_example_files_parse(filename: str) -> None:
    """Every .vera file in examples/ must parse without error."""
    parse_file(EXAMPLES_DIR / filename)


# =====================================================================
# Individual construct tests
# =====================================================================


class TestExpressions:
    def test_integer_literal(self) -> None:
        tree = parse("fn f(@Unit -> @Int) requires(true) ensures(true) effects(pure) { 42 }")
        assert tree is not None

    def test_arithmetic(self) -> None:
        parse("fn f(@Int -> @Int) requires(true) ensures(true) effects(pure) { @Int.0 + 1 }")
        parse("fn f(@Int -> @Int) requires(true) ensures(true) effects(pure) { @Int.0 * 2 - 3 }")
        parse("fn f(@Int -> @Int) requires(true) ensures(true) effects(pure) { @Int.0 / 2 % 3 }")

    def test_comparison(self) -> None:
        parse("fn f(@Int -> @Bool) requires(true) ensures(true) effects(pure) { @Int.0 > 0 }")
        parse("fn f(@Int -> @Bool) requires(true) ensures(true) effects(pure) { @Int.0 <= 10 }")

    def test_boolean_operators(self) -> None:
        parse("fn f(@Bool, @Bool -> @Bool) requires(true) ensures(true) effects(pure) { @Bool.0 && @Bool.1 }")
        parse("fn f(@Bool, @Bool -> @Bool) requires(true) ensures(true) effects(pure) { @Bool.0 || @Bool.1 }")
        parse("fn f(@Bool -> @Bool) requires(true) ensures(true) effects(pure) { !@Bool.0 }")

    def test_implies(self) -> None:
        parse("fn f(@Bool, @Bool -> @Bool) requires(true) ensures(true) effects(pure) { @Bool.0 ==> @Bool.1 }")

    def test_pipe(self) -> None:
        parse("fn f(@Int -> @Int) requires(true) ensures(true) effects(pure) { @Int.0 + 1 |> abs() }")

    def test_negation(self) -> None:
        parse("fn f(@Int -> @Int) requires(true) ensures(true) effects(pure) { -@Int.0 }")

    def test_parenthesized(self) -> None:
        parse("fn f(@Int -> @Int) requires(true) ensures(true) effects(pure) { (@Int.0 + 1) * 2 }")

    def test_array_literal(self) -> None:
        parse("fn f(@Unit -> @Array<Int>) requires(true) ensures(true) effects(pure) { [1, 2, 3] }")

    def test_array_index(self) -> None:
        parse("fn f(@Array<Int> -> @Int) requires(true) ensures(true) effects(pure) { @Array<Int>.0[0] }")

    def test_string_literal(self) -> None:
        parse('fn f(@Unit -> @String) requires(true) ensures(true) effects(pure) { "hello" }')

    def test_unit_literal(self) -> None:
        parse("fn f(@Unit -> @Unit) requires(true) ensures(true) effects(pure) { () }")


class TestFunctions:
    def test_multiple_params(self) -> None:
        parse("fn f(@Int, @Bool, @String -> @Int) requires(true) ensures(true) effects(pure) { @Int.0 }")

    def test_multiple_requires(self) -> None:
        parse("fn f(@Int -> @Int) requires(@Int.0 > 0) requires(@Int.0 < 100) ensures(true) effects(pure) { @Int.0 }")

    def test_multiple_ensures(self) -> None:
        parse("fn f(@Int -> @Nat) requires(true) ensures(@Nat.result >= 0) ensures(@Nat.result <= @Int.0) effects(pure) { @Int.0 }")

    def test_decreases_clause(self) -> None:
        parse("fn f(@Nat -> @Nat) requires(true) ensures(true) decreases(@Nat.0) effects(pure) { @Nat.0 }")

    def test_recursive_call(self) -> None:
        parse("""
        fn f(@Nat -> @Nat)
          requires(true)
          ensures(true)
          decreases(@Nat.0)
          effects(pure)
        {
          if @Nat.0 == 0 then { 0 } else { f(@Nat.0 - 1) }
        }
        """)

    def test_where_block(self) -> None:
        parse("""
        fn outer(@Int -> @Int)
          requires(true)
          ensures(true)
          effects(pure)
        {
          helper(@Int.0)
        }
        where {
          fn helper(@Int -> @Int)
            requires(true)
            ensures(true)
            effects(pure)
          {
            @Int.0 + 1
          }
        }
        """)


class TestConditionals:
    def test_if_then_else(self) -> None:
        parse("""
        fn f(@Bool -> @Int)
          requires(true)
          ensures(true)
          effects(pure)
        {
          if @Bool.0 then { 1 } else { 0 }
        }
        """)


class TestPatternMatching:
    def test_match_constructors(self) -> None:
        parse("""
        data Color { Red, Green, Blue }

        fn to_int(@Color -> @Int)
          requires(true)
          ensures(true)
          effects(pure)
        {
          match @Color.0 {
            Red -> 0,
            Green -> 1,
            Blue -> 2
          }
        }
        """)

    def test_match_with_binding(self) -> None:
        parse("""
        data Maybe<T> { Nothing, Just(T) }

        fn unwrap_or(@Maybe<Int>, @Int -> @Int)
          requires(true)
          ensures(true)
          effects(pure)
        {
          match @Maybe<Int>.0 {
            Nothing -> @Int.0,
            Just(@Int) -> @Int.0
          }
        }
        """)

    def test_wildcard_pattern(self) -> None:
        parse("""
        fn f(@Int -> @Int)
          requires(true)
          ensures(true)
          effects(pure)
        {
          match @Int.0 {
            0 -> 1,
            _ -> 0
          }
        }
        """)


class TestEffects:
    def test_pure(self) -> None:
        parse("fn f(@Int -> @Int) requires(true) ensures(true) effects(pure) { @Int.0 }")

    def test_single_effect(self) -> None:
        parse("fn f(@Unit -> @Unit) requires(true) ensures(true) effects(<IO>) { () }")

    def test_parameterized_effect(self) -> None:
        parse("fn f(@Unit -> @Unit) requires(true) ensures(true) effects(<State<Int>>) { () }")

    def test_multiple_effects(self) -> None:
        parse("fn f(@Unit -> @Unit) requires(true) ensures(true) effects(<State<Int>, IO>) { () }")

    def test_effect_declaration(self) -> None:
        parse("""
        effect Console {
          op print(String -> Unit);
          op read_line(Unit -> String);
        }
        """)

    def test_handler(self) -> None:
        parse("""
        fn f(@Unit -> @Int)
          requires(true)
          ensures(true)
          effects(pure)
        {
          handle[State<Int>](@Int = 0) {
            get(@Unit) -> { resume(@Int.0) },
            put(@Int) -> { resume(()) }
          } in {
            put(42);
            get(())
          }
        }
        """)


class TestBlocks:
    def test_let_binding(self) -> None:
        parse("""
        fn f(@Int -> @Int)
          requires(true)
          ensures(true)
          effects(pure)
        {
          let @Int = @Int.0 + 1;
          @Int.0
        }
        """)

    def test_multiple_statements(self) -> None:
        parse("""
        fn f(@Int -> @Int)
          requires(true)
          ensures(true)
          effects(pure)
        {
          let @Int = @Int.0 + 1;
          let @Int = @Int.0 * 2;
          @Int.0
        }
        """)

    def test_expression_statement(self) -> None:
        parse("""
        fn f(@Unit -> @Unit)
          requires(true)
          ensures(true)
          effects(<IO>)
        {
          print("hello");
          ()
        }
        """)


class TestContracts:
    def test_old_new_in_ensures(self) -> None:
        parse("""
        fn f(@Unit -> @Unit)
          requires(true)
          ensures(new(State<Int>) == old(State<Int>) + 1)
          effects(<State<Int>>)
        {
          ()
        }
        """)

    def test_result_reference(self) -> None:
        parse("""
        fn f(@Int -> @Int)
          requires(true)
          ensures(@Int.result >= 0)
          effects(pure)
        {
          @Int.0
        }
        """)


class TestDataTypes:
    def test_simple_adt(self) -> None:
        parse("data Bool { True, False }")

    def test_parameterized_adt(self) -> None:
        parse("data Option<T> { None, Some(T) }")

    def test_adt_with_invariant(self) -> None:
        parse("""
        data Positive invariant(@Int.0 > 0) {
          MkPositive(Int)
        }
        """)

    def test_type_alias(self) -> None:
        parse("type Name = String;")


class TestModules:
    def test_module_declaration(self) -> None:
        parse("module vera.math;")

    def test_import(self) -> None:
        parse("import vera.math;")

    def test_import_list(self) -> None:
        parse("import vera.math(abs, max);")

    def test_import_types(self) -> None:
        parse("import vera.collections(List, Option);")

    def test_visibility(self) -> None:
        parse("""
        public fn f(@Int -> @Int)
          requires(true)
          ensures(true)
          effects(pure)
        {
          @Int.0
        }
        """)


class TestComments:
    def test_line_comment(self) -> None:
        parse("""
        -- this is a comment
        fn f(@Int -> @Int)
          requires(true)
          ensures(true)
          effects(pure)
        {
          @Int.0 -- inline comment
        }
        """)

    def test_block_comment(self) -> None:
        parse("""
        {- block comment -}
        fn f(@Int -> @Int)
          requires(true)
          ensures(true)
          effects(pure)
        {
          @Int.0
        }
        """)


# =====================================================================
# Error case tests — verify that invalid programs produce ParseError
# =====================================================================


class TestParseErrors:
    def test_missing_contract_block(self) -> None:
        with pytest.raises(ParseError):
            parse("fn f(@Int -> @Int) { @Int.0 }")

    def test_missing_effects(self) -> None:
        with pytest.raises(ParseError):
            parse("fn f(@Int -> @Int) requires(true) ensures(true) { @Int.0 }")

    def test_missing_body(self) -> None:
        with pytest.raises(ParseError):
            parse("fn f(@Int -> @Int) requires(true) ensures(true) effects(pure)")

    def test_unclosed_brace(self) -> None:
        with pytest.raises(ParseError):
            parse("fn f(@Int -> @Int) requires(true) ensures(true) effects(pure) { @Int.0")

    def test_invalid_token(self) -> None:
        with pytest.raises(ParseError):
            parse("fn f(@Int -> @Int) requires(true) ensures(true) effects(pure) { $ }")
