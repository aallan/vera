"""Tests for scripts/check_examples_readme.py's Demonstrates-column gate.

The gate's `name_appears_in_source` originally matched a Demonstrates-column
name TEXTUALLY against the whole file, so a name mentioned only inside a
comment or a string literal (never executed, never even parsed as an
identifier) still satisfied the column's claim that the example demonstrates
it — a real gap found by mutation testing on PR #1377's review: a
comment-only mention of a phantom builtin plus a matching Demonstrates entry
passed the gate before this fix.  Comments and string-literal CONTENT are
now stripped before matching, reusing `vera.lexical.blank_comments` — the
same nesting-aware scanner `vera/parser.py` itself runs on — rather than a
second, independent comment regex: Vera has three comment forms (`--` to
end of line, nestable `{- -}`, and non-nesting `/* */` annotation
comments), and only a real scanner can count `{- -}` nesting depth
correctly (the #1112 shape `blank_comments` exists to prevent).  A `--`
inside a STRING LITERAL (`examples/regex.vera`'s
`IO.print("-- Matching --")`) must survive, since it is part of the
string, never a comment start.
"""

from __future__ import annotations

import importlib.util
from pathlib import Path

_SCRIPT = Path(__file__).parent.parent / "scripts" / "check_examples_readme.py"

# scripts/ is not a package: load the module by file path (same pattern as
# tests/test_doc_annotations.py and tests/test_build_site.py).
_spec = importlib.util.spec_from_file_location("check_examples_readme", _SCRIPT)
assert _spec is not None and _spec.loader is not None
check_examples_readme = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(check_examples_readme)

_strip_non_code = check_examples_readme._strip_non_code
name_appears_in_source = check_examples_readme.name_appears_in_source
extract_backticked_names = check_examples_readme.extract_backticked_names
extract_example_rows = check_examples_readme.extract_example_rows


def _program(body: str) -> str:
    """A minimal well-formed program wrapping `body` as the entry point,
    so each fixture below states only the fragment under test."""
    return (
        "public fn main(@Unit -> @Unit)\n"
        "  requires(true)\n"
        "  ensures(true)\n"
        "  effects(pure)\n"
        f"{{ {body} }}\n"
    )


class TestStripNonCode:
    def test_strips_line_comment(self) -> None:
        assert _strip_non_code("let x = 1; -- comment\n") == "let x = 1;           \n"

    def test_strips_nestable_block_comment(self) -> None:
        """Vera's `{- -}` block comment nests (spec 1.3) — a regex cannot
        count depth, which is exactly why this reuses vera.lexical's real
        scanner rather than a hand-written pattern."""
        src = "{- outer {- inner -} still outer -}code\n"
        stripped = _strip_non_code(src)
        assert "code" in stripped
        assert "outer" not in stripped
        assert "inner" not in stripped

    def test_strips_annotation_comment(self) -> None:
        src = "/* a label */code\n"
        stripped = _strip_non_code(src)
        assert "code" in stripped
        assert "label" not in stripped

    def test_dashes_inside_a_string_do_not_open_a_comment(self) -> None:
        """The examples/regex.vera shape: a `--` inside a string is part
        of the string, never a comment start, so it must not make the
        scanner consume text AFTER the string as if the rest of the
        line were a comment (the string's own content is still blanked
        by the separate string-content pass — only that has to survive)."""
        src = 'IO.print("-- Matching --") code_after\n'
        assert _strip_non_code(src) == 'IO.print("              ") code_after\n'

    def test_strips_comment_following_a_string_literal(self) -> None:
        src = 'IO.print("ok") -- trailing note\n'
        assert _strip_non_code(src) == 'IO.print("  ")                 \n'

    def test_blanks_string_content_but_keeps_the_quotes(self) -> None:
        src = 'IO.print("phantom_builtin")\n'
        stripped = _strip_non_code(src)
        assert "phantom_builtin" not in stripped
        assert stripped.count('"') == 2


class TestNameAppearsInSource:
    def test_name_only_in_line_comment_does_not_count(self, tmp_path: Path) -> None:
        """The #1377-review gap, red before the comment-stripping fix:
        a name mentioned only in prose (a `--` comment) must not satisfy
        a Demonstrates-column claim about the CODE."""
        vera_file = tmp_path / "example.vera"
        vera_file.write_text(
            "-- Uses phantom_builtin somewhere, in prose only.\n"
            + _program("()"),
            encoding="utf-8",
        )
        assert name_appears_in_source(vera_file, "phantom_builtin") is False

    def test_same_name_as_a_real_call_does_count(self, tmp_path: Path) -> None:
        """Positive twin of the test above (#1377 review): the identical
        name `phantom_builtin`, this time as a genuine call, must still
        be found — proving the stripped-source match isn't vacuously
        False for every name, only for ones that never appear as code."""
        vera_file = tmp_path / "example.vera"
        vera_file.write_text(_program("phantom_builtin()"), encoding="utf-8")
        assert name_appears_in_source(vera_file, "phantom_builtin") is True

    def test_name_only_in_block_comment_does_not_count(self, tmp_path: Path) -> None:
        vera_file = tmp_path / "example.vera"
        vera_file.write_text(
            "{- Uses phantom_block somewhere, in prose only. -}\n"
            + _program("()"),
            encoding="utf-8",
        )
        assert name_appears_in_source(vera_file, "phantom_block") is False

    def test_name_only_in_annotation_comment_does_not_count(
        self, tmp_path: Path,
    ) -> None:
        vera_file = tmp_path / "example.vera"
        vera_file.write_text(
            "/* mentions phantom_annotation */\n" + _program("()"),
            encoding="utf-8",
        )
        assert name_appears_in_source(vera_file, "phantom_annotation") is False

    def test_name_only_inside_a_string_literal_does_not_count(
        self, tmp_path: Path,
    ) -> None:
        """A name that is only STRING DATA, never a call, must not
        satisfy the Demonstrates claim either — the same principle as
        excluding comments, extended to string content (#1377 review)."""
        vera_file = tmp_path / "example.vera"
        vera_file.write_text(
            _program('IO.print("phantom_string")'), encoding="utf-8",
        )
        assert name_appears_in_source(vera_file, "phantom_string") is False

    def test_name_only_inside_string_literal_containing_dashes_still_counts(
        self, tmp_path: Path,
    ) -> None:
        """A `--` inside a string must not make the comment-stripper eat
        the rest of the line — `IO` and `print` sit right before the
        string and must still be found."""
        vera_file = tmp_path / "example.vera"
        vera_file.write_text(
            _program('IO.print("-- Matching --")'), encoding="utf-8",
        )
        assert name_appears_in_source(vera_file, "IO") is True
        assert name_appears_in_source(vera_file, "print") is True


class TestExtractBacktickedNames:
    def test_bare_identifier_is_a_name_claim(self) -> None:
        assert extract_backticked_names("Uses `array_slice` and `decreases`.") == [
            "array_slice", "decreases",
        ]

    def test_non_identifier_span_is_not_a_name_claim(self) -> None:
        # A call expression, a declaration snippet, a module path — none
        # is a single bare identifier, so none is checked against source.
        assert extract_backticked_names(
            "Calls `async(Http.get)`, declares `type Board = Map<String, Int>`,"
            " imports `wasi:http`."
        ) == []


class TestExtractExampleRows:
    def test_three_cell_row_with_vera_filename_is_extracted(
        self, tmp_path: Path,
    ) -> None:
        readme = tmp_path / "README.md"
        readme.write_text(
            "| Example | Run | Demonstrates |\n"
            "|---|---|---|\n"
            "| `array_utilities.vera` | `vera run examples/array_utilities.vera` |"
            " `array_slice`, `array_map` |\n",
            encoding="utf-8",
        )
        rows = extract_example_rows(readme)
        assert rows == [
            (3, "array_utilities.vera", "`array_slice`, `array_map`"),
        ]
