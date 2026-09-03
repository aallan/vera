"""Tests for scripts/check_examples_readme.py's Demonstrates-column gate.

The gate's `name_appears_in_source` originally matched a Demonstrates-column
name TEXTUALLY against the whole file, so a name mentioned only inside a
`--` comment (never executed, never even parsed as an identifier) still
satisfied the column's claim that the example demonstrates it — a real gap
found by mutation testing on PR #1377's review: a comment-only mention of a
phantom builtin plus a matching Demonstrates entry passed the gate before
this fix (`-- mentions phantom_builtin in prose only`).  These tests pin the
fix: comments are stripped before matching, but a `--` inside a STRING
LITERAL (`examples/regex.vera`'s `IO.print("-- Matching --")`) must survive
intact, mirroring vera/grammar.lark's own STRING_LIT-before-`--`-ignore
token precedence.
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

_strip_comments = check_examples_readme._strip_comments
name_appears_in_source = check_examples_readme.name_appears_in_source
extract_backticked_names = check_examples_readme.extract_backticked_names
extract_example_rows = check_examples_readme.extract_example_rows


class TestStripComments:
    def test_strips_trailing_comment(self) -> None:
        assert _strip_comments("let x = 1; -- comment\n") == "let x = 1; \n"

    def test_preserves_dashes_inside_string_literal(self) -> None:
        """The examples/regex.vera shape: a `--` inside a string is part
        of the string, never a comment start."""
        src = 'IO.print("-- Matching --")\n'
        assert _strip_comments(src) == src

    def test_strips_comment_following_a_string_literal(self) -> None:
        src = 'IO.print("ok") -- trailing note\n'
        assert _strip_comments(src) == 'IO.print("ok") \n'


class TestNameAppearsInSource:
    def test_name_only_in_comment_does_not_count(self, tmp_path: Path) -> None:
        """The #1377-review gap, red before the comment-stripping fix:
        a name mentioned only in prose (a `--` comment) must not satisfy
        a Demonstrates-column claim about the CODE."""
        vera_file = tmp_path / "example.vera"
        vera_file.write_text(
            "-- Uses phantom_builtin somewhere, in prose only.\n"
            "public fn main(@Unit -> @Unit)\n"
            "  requires(true)\n"
            "  ensures(true)\n"
            "  effects(pure)\n"
            "{ () }\n",
            encoding="utf-8",
        )
        assert name_appears_in_source(vera_file, "phantom_builtin") is False

    def test_name_in_real_code_still_counts(self, tmp_path: Path) -> None:
        vera_file = tmp_path / "example.vera"
        vera_file.write_text(
            "public fn main(@Unit -> @Unit)\n"
            "  requires(true)\n"
            "  ensures(true)\n"
            "  effects(pure)\n"
            "{ real_builtin_use() }\n",
            encoding="utf-8",
        )
        assert name_appears_in_source(vera_file, "real_builtin_use") is True

    def test_name_only_inside_string_literal_containing_dashes_still_counts(
        self, tmp_path: Path,
    ) -> None:
        """A `--` inside a string must not make the comment-stripper eat
        the rest of the line — `IO` and `print` sit right before the
        string and must still be found."""
        vera_file = tmp_path / "example.vera"
        vera_file.write_text(
            "public fn main(@Unit -> @Unit)\n"
            "  requires(true)\n"
            "  ensures(true)\n"
            "  effects(pure)\n"
            '{ IO.print("-- Matching --") }\n',
            encoding="utf-8",
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
