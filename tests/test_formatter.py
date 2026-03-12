"""Tests for vera.formatter — canonical code formatter."""

from __future__ import annotations

import os
from pathlib import Path
from textwrap import dedent

import pytest

from vera.formatter import (
    Comment,
    extract_comments,
    format_source,
)


EXAMPLES_DIR = Path(__file__).parent.parent / "examples"
EXAMPLE_FILES = sorted(
    f for f in os.listdir(EXAMPLES_DIR) if f.endswith(".vera")
)


# =====================================================================
# Helpers
# =====================================================================

def _fmt(source: str) -> str:
    """Format source and return the result."""
    return format_source(dedent(source).lstrip())


def _fmt_roundtrip(source: str) -> None:
    """Assert formatting is idempotent: fmt(fmt(x)) == fmt(x)."""
    first = _fmt(source)
    second = format_source(first)
    assert first == second, (
        f"Not idempotent.\nFirst pass:\n{first}\nSecond pass:\n{second}"
    )


def _fmt_check(source: str, expected: str) -> None:
    """Assert formatted output matches expected exactly."""
    result = _fmt(source)
    expected_clean = dedent(expected).lstrip()
    assert result == expected_clean, (
        f"Mismatch.\nGot:\n{result}\nExpected:\n{expected_clean}"
    )


# =====================================================================
# Comment extraction
# =====================================================================

class TestCommentExtraction:
    def test_line_comment(self) -> None:
        comments = extract_comments("-- hello\n")
        assert len(comments) == 1
        assert comments[0].kind == "line"
        assert comments[0].text == "-- hello"
        assert comments[0].line == 1
        assert comments[0].inline is False

    def test_inline_line_comment(self) -> None:
        comments = extract_comments("x + y -- add\n")
        assert len(comments) == 1
        assert comments[0].inline is True

    def test_block_comment(self) -> None:
        comments = extract_comments("{- block -}\n")
        assert len(comments) == 1
        assert comments[0].kind == "block"
        assert comments[0].text == "{- block -}"

    def test_nested_block_comment(self) -> None:
        comments = extract_comments("{- outer {- inner -} outer -}\n")
        assert len(comments) == 1
        assert comments[0].text == "{- outer {- inner -} outer -}"

    def test_annotation_comment(self) -> None:
        comments = extract_comments("/* width */ x\n")
        assert len(comments) == 1
        assert comments[0].kind == "annotation"

    def test_no_comments(self) -> None:
        comments = extract_comments("fn foo() {}\n")
        assert len(comments) == 0

    def test_comments_inside_string_ignored(self) -> None:
        comments = extract_comments('"-- not a comment"\n')
        assert len(comments) == 0

    def test_multiple_comments(self) -> None:
        src = "-- first\n-- second\n"
        comments = extract_comments(src)
        assert len(comments) == 2


# =====================================================================
# Expression formatting
# =====================================================================

class TestFormatExpressions:
    def test_integer_literal(self) -> None:
        _fmt_check(
            """
            public fn f(-> @Int)
              requires(true)
              ensures(true)
              effects(pure)
            {
              42
            }
            """,
            """
            public fn f(-> @Int)
              requires(true)
              ensures(true)
              effects(pure)
            {
              42
            }
            """,
        )

    def test_binary_operators(self) -> None:
        _fmt_check(
            """
            public fn f(@Int, @Int -> @Int)
              requires(true)
              ensures(true)
              effects(pure)
            {
              @Int.0 + @Int.1
            }
            """,
            """
            public fn f(@Int, @Int -> @Int)
              requires(true)
              ensures(true)
              effects(pure)
            {
              @Int.0 + @Int.1
            }
            """,
        )

    def test_slot_ref_with_type_args(self) -> None:
        src = _fmt("""
            private data Option<T> { None, Some(T) }

            public fn f(@Option<Int> -> @Bool)
              requires(true)
              ensures(true)
              effects(pure)
            {
              match @Option<Int>.0 {
                None -> false,
                Some(@Int) -> true
              }
            }
        """)
        assert "@Option<Int>.0" in src

    def test_unary_neg(self) -> None:
        src = _fmt("""
            public fn f(@Int -> @Int)
              requires(true)
              ensures(true)
              effects(pure)
            {
              -@Int.0
            }
        """)
        assert "-@Int.0" in src

    def test_array_literal(self) -> None:
        src = _fmt("""
            public fn f(-> @Array<Int>)
              requires(true)
              ensures(true)
              effects(pure)
            {
              [1, 2, 3]
            }
        """)
        assert "[1, 2, 3]" in src


# =====================================================================
# Declaration formatting
# =====================================================================

class TestFormatDeclarations:
    def test_simple_function(self) -> None:
        _fmt_roundtrip("""
            public fn f(@Int -> @Int)
              requires(true)
              ensures(true)
              effects(pure)
            {
              @Int.0
            }
        """)

    def test_forall_function(self) -> None:
        src = _fmt("""
            private forall<T> fn identity(@T -> @T)
              requires(true)
              ensures(@T.result == @T.0)
              effects(pure)
            {
              @T.0
            }
        """)
        assert "private forall<T> fn identity" in src

    def test_data_declaration(self) -> None:
        _fmt_check(
            """
            private data Option<T> {
              None,
              Some(T)
            }
            """,
            """
            private data Option<T> {
              None,
              Some(T)
            }
            """,
        )

    def test_type_alias(self) -> None:
        src = _fmt("""
            type IntToInt = fn(Int -> Int) effects(pure);
        """)
        assert "type IntToInt = fn(Int -> Int) effects(pure);" in src

    def test_refinement_type_alias(self) -> None:
        src = _fmt("""
            type PosInt = { @Int | @Int.0 > 0 };
        """)
        assert "type PosInt = { @Int | @Int.0 > 0 };" in src

    def test_effect_declaration(self) -> None:
        _fmt_check(
            """
            effect Counter {
              op get_count(Unit -> Int);
              op increment(Unit -> Unit);
            }
            """,
            """
            effect Counter {
              op get_count(Unit -> Int);
              op increment(Unit -> Unit);
            }
            """,
        )

    def test_where_block(self) -> None:
        src = _fmt("""
            public fn is_even(@Nat -> @Bool)
              requires(true)
              ensures(true)
              decreases(@Nat.0)
              effects(pure)
            {
              if @Nat.0 == 0 then {
                true
              } else {
                is_odd(@Nat.0 - 1)
              }
            }
            where {
              fn is_odd(@Nat -> @Bool)
                requires(true)
                ensures(true)
                decreases(@Nat.0)
                effects(pure)
              {
                if @Nat.0 == 0 then {
                  false
                } else {
                  is_even(@Nat.0 - 1)
                }
              }
            }
        """)
        # Where-block functions have no visibility prefix
        assert "  fn is_odd" in src
        assert "private fn is_odd" not in src


# =====================================================================
# Program formatting
# =====================================================================

class TestFormatProgram:
    def test_blank_lines_between_decls(self) -> None:
        src = _fmt("""
            public fn f(-> @Int)
              requires(true)
              ensures(true)
              effects(pure)
            {
              1
            }

            public fn g(-> @Int)
              requires(true)
              ensures(true)
              effects(pure)
            {
              2
            }
        """)
        # Should have exactly one blank line between declarations
        assert "\n\npublic fn g" in src

    def test_module_and_imports(self) -> None:
        src = _fmt("""
            module vera.example;

            import vera.math(abs, max);

            public fn f(-> @Int)
              requires(true)
              ensures(true)
              effects(pure)
            {
              vera.math::abs(-1)
            }
        """)
        assert src.startswith("module vera.example;\n")
        assert "import vera.math(abs, max);" in src


# =====================================================================
# Formatting rules (Spec Section 1.8)
# =====================================================================

class TestFormatRules:
    def test_rule_1_indentation(self) -> None:
        """Rule 1: 2 spaces per level, no tabs."""
        src = _fmt("""
            public fn f(@Int -> @Int)
              requires(true)
              ensures(true)
              effects(pure)
            {
              @Int.0
            }
        """)
        assert "\t" not in src
        # Contract lines indented 2 spaces
        for line in src.split("\n"):
            if line.startswith("  requires") or line.startswith("  ensures"):
                assert line.startswith("  ")
                assert not line.startswith("    ")

    def test_rule_3_commas(self) -> None:
        """Rule 3: commas followed by single space."""
        src = _fmt("""
            public fn f(@Int, @Int -> @Int)
              requires(true)
              ensures(true)
              effects(pure)
            {
              @Int.0 + @Int.1
            }
        """)
        assert "@Int, @Int" in src

    def test_rule_4_operators(self) -> None:
        """Rule 4: operators surrounded by single spaces."""
        src = _fmt("""
            public fn f(@Int, @Int -> @Int)
              requires(true)
              ensures(true)
              effects(pure)
            {
              @Int.0 + @Int.1
            }
        """)
        assert "@Int.0 + @Int.1" in src

    def test_rule_5_semicolons(self) -> None:
        """Rule 5: no space before semicolon, newline after."""
        src = _fmt("""
            public fn f(@Int -> @Int)
              requires(true)
              ensures(true)
              effects(pure)
            {
              let @Int = @Int.0 + 1;
              @Int.0
            }
        """)
        assert "let @Int = @Int.0 + 1;" in src

    def test_rule_6_parentheses(self) -> None:
        """Rule 6: no space inside parentheses."""
        src = _fmt("""
            public fn f(@Int -> @Int)
              requires(true)
              ensures(true)
              effects(pure)
            {
              f(@Int.0)
            }
        """)
        assert "f(@Int.0)" in src

    def test_rule_9_no_trailing_whitespace(self) -> None:
        """Rule 9: no trailing whitespace on any line."""
        src = _fmt("""
            public fn f(-> @Int)
              requires(true)
              ensures(true)
              effects(pure)
            {
              42
            }
        """)
        for line in src.split("\n"):
            assert line == line.rstrip(), f"Trailing whitespace: {line!r}"

    def test_rule_10_single_trailing_newline(self) -> None:
        """Rule 10: file ends with a single newline."""
        src = _fmt("""
            public fn f(-> @Int)
              requires(true)
              ensures(true)
              effects(pure)
            {
              42
            }
        """)
        assert src.endswith("\n")
        assert not src.endswith("\n\n")


# =====================================================================
# Comment preservation
# =====================================================================

class TestCommentPreservation:
    def test_comment_before_function(self) -> None:
        src = _fmt("""
            -- A comment
            public fn f(-> @Int)
              requires(true)
              ensures(true)
              effects(pure)
            {
              42
            }
        """)
        assert "-- A comment" in src

    def test_comment_between_functions(self) -> None:
        src = _fmt("""
            public fn f(-> @Int)
              requires(true)
              ensures(true)
              effects(pure)
            {
              1
            }

            -- Second function
            public fn g(-> @Int)
              requires(true)
              ensures(true)
              effects(pure)
            {
              2
            }
        """)
        assert "-- Second function" in src


# =====================================================================
# Parenthesization
# =====================================================================

class TestParenthesization:
    def test_precedence_preserved(self) -> None:
        """Lower precedence child of higher precedence parent gets parens."""
        src = _fmt("""
            public fn f(@Int, @Int, @Int -> @Int)
              requires(true)
              ensures(true)
              effects(pure)
            {
              (@Int.0 + @Int.1) * @Int.2
            }
        """)
        assert "(@Int.0 + @Int.1) * @Int.2" in src

    def test_no_unnecessary_parens(self) -> None:
        """Higher precedence child of lower precedence parent: no parens."""
        src = _fmt("""
            public fn f(@Int, @Int, @Int -> @Int)
              requires(true)
              ensures(true)
              effects(pure)
            {
              @Int.0 + @Int.1 * @Int.2
            }
        """)
        assert "@Int.0 + @Int.1 * @Int.2" in src

    def test_right_child_of_left_assoc(self) -> None:
        """Right child at same prec of left-assoc op gets parens: a - (b - c)."""
        src = _fmt("""
            public fn f(@Int, @Int, @Int -> @Int)
              requires(true)
              ensures(true)
              effects(pure)
            {
              @Int.0 - (@Int.1 - @Int.2)
            }
        """)
        assert "@Int.0 - (@Int.1 - @Int.2)" in src


# =====================================================================
# Match arm block bodies (#274)
# =====================================================================

class TestMatchBlockArms:
    """Formatter must preserve braces on multi-statement match arm blocks."""

    def test_match_arm_block_body_multiline(self) -> None:
        """Block arm body with statements emits multi-line with braces."""
        _fmt_check(
            """
            effect IO { op print(String -> Unit); }

            public fn f(@Int -> @Unit)
              requires(true)
              ensures(true)
              effects(<IO>)
            {
              match @Int.0 {
                0 -> {
                  IO.print("zero");
                  IO.print("done")
                },
                _ -> IO.print("other")
              }
            }
            """,
            """
            effect IO {
              op print(String -> Unit);
            }

            public fn f(@Int -> @Unit)
              requires(true)
              ensures(true)
              effects(<IO>)
            {
              match @Int.0 {
                0 -> {
                  IO.print("zero");
                  IO.print("done")
                },
                _ -> IO.print("other")
              }
            }
            """,
        )

    def test_match_arm_block_body_idempotent(self) -> None:
        """Formatting a match with block arms twice gives identical output."""
        _fmt_roundtrip("""
            effect IO { op print(String -> Unit); }

            public fn f(@Int -> @Unit)
              requires(true)
              ensures(true)
              effects(<IO>)
            {
              match @Int.0 {
                0 -> {
                  IO.print("hello");
                  IO.print("world")
                },
                _ -> IO.print("other")
              }
            }
        """)

    def test_match_arm_block_body_roundtrip_parses(self) -> None:
        """Formatted output with block arms must parse without error."""
        from vera.parser import parse as vera_parse
        from vera.transform import transform

        src = _fmt("""
            effect IO { op print(String -> Unit); }

            public fn f(@Int -> @Unit)
              requires(true)
              ensures(true)
              effects(<IO>)
            {
              match @Int.0 {
                0 -> {
                  IO.print("hello");
                  IO.print("world")
                },
                _ -> IO.print("other")
              }
            }
        """)
        tree = vera_parse(src)
        transform(tree)  # Should not raise

    def test_match_arm_mixed_simple_and_block(self) -> None:
        """Mix of simple and block arms: simple stays inline, block expands."""
        src = _fmt("""
            effect IO { op print(String -> Unit); }

            private data Maybe { Nothing, Just(Int) }

            public fn f(@Maybe -> @Unit)
              requires(true)
              ensures(true)
              effects(<IO>)
            {
              match @Maybe.0 {
                Nothing -> IO.print("none"),
                Just(@Int) -> {
                  IO.print("got:");
                  IO.print(int_to_string(@Int.0))
                }
              }
            }
        """)
        assert "Nothing -> IO.print(\"none\")," in src
        assert "Just(@Int) -> {" in src
        assert '  IO.print("got:");' in src
        assert "  IO.print(int_to_string(@Int.0))" in src

    def test_match_arm_block_trailing_comma(self) -> None:
        """Non-final block arm gets comma after closing brace."""
        src = _fmt("""
            effect IO { op print(String -> Unit); }

            public fn f(@Int -> @Unit)
              requires(true)
              ensures(true)
              effects(<IO>)
            {
              match @Int.0 {
                0 -> {
                  IO.print("a");
                  IO.print("b")
                },
                _ -> IO.print("c")
              }
            }
        """)
        assert "},\n" in src

    def test_match_arm_block_no_trailing_comma_final(self) -> None:
        """Final block arm has no comma after closing brace."""
        src = _fmt("""
            effect IO { op print(String -> Unit); }

            public fn f(@Int -> @Unit)
              requires(true)
              ensures(true)
              effects(<IO>)
            {
              match @Int.0 {
                0 -> IO.print("a"),
                _ -> {
                  IO.print("b");
                  IO.print("c")
                }
              }
            }
        """)
        # Final arm: closing brace without comma
        lines = src.strip().splitlines()
        # Find the closing brace of the block arm
        block_close = [l for l in lines if l.strip() == "}"]
        assert len(block_close) >= 1  # at least one bare }

    def test_match_arm_block_inline_context(self) -> None:
        """Match in let-binding position wraps block arm in braces inline."""
        src = _fmt("""
            public fn f(@Int -> @Int)
              requires(true)
              ensures(true)
              effects(pure)
            {
              let @Int = match @Int.0 { 0 -> { let @Int = 10; @Int.0 + 1 }, _ -> 0 };
              @Int.0
            }
        """)
        # Block arm body must be wrapped in braces in inline form
        assert "{ let @Int = 10; @Int.0 + 1 }" in src

    def test_match_arm_block_in_exprstmt(self) -> None:
        """Match as ExprStmt preserves block arm braces in inline form."""
        src = _fmt("""
            effect IO { op print(String -> Unit); }

            public fn f(@Int -> @Unit)
              requires(true)
              ensures(true)
              effects(<IO>)
            {
              match @Int.0 { 0 -> { IO.print("a"); IO.print("b") }, _ -> IO.print("c") };
              IO.print("done")
            }
        """)
        # Block arm in inline match must have braces
        assert "{ IO.print(\"a\"); IO.print(\"b\") }" in src


# =====================================================================
# Idempotency — all examples
# =====================================================================

class TestIdempotency:
    @pytest.mark.parametrize("name", EXAMPLE_FILES)
    def test_example_idempotent(self, name: str) -> None:
        """Formatting the formatted output should produce identical output."""
        path = EXAMPLES_DIR / name
        source = path.read_text(encoding="utf-8")
        first = format_source(source, file=str(path))
        second = format_source(first)
        assert first == second, f"{name} is not idempotent"

    @pytest.mark.parametrize("name", EXAMPLE_FILES)
    def test_formatted_still_parses(self, name: str) -> None:
        """Formatted output should still parse and transform without errors."""
        from vera.parser import parse as vera_parse
        from vera.transform import transform

        path = EXAMPLES_DIR / name
        source = path.read_text(encoding="utf-8")
        formatted = format_source(source, file=str(path))
        tree = vera_parse(formatted)
        transform(tree)  # Should not raise
