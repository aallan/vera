"""Tests for the KNOWN_ISSUES / HISTORY checks in scripts/check_doc_counts.py.

Covers the two checks added in the June 2026 planning-document rework:

- ``check_refactoring_counts`` — KNOWN_ISSUES.md "Refactoring needed"
  line counts must stay within ±10% of the measured file sizes.
- ``check_history_row_format`` — HISTORY.md version rows carry at most
  one issue link and no " — " separator.
"""

from __future__ import annotations

import importlib.util
from pathlib import Path
from typing import Any

_SCRIPT = Path(__file__).parent.parent / "scripts" / "check_doc_counts.py"


def _load() -> Any:
    spec = importlib.util.spec_from_file_location("check_doc_counts", _SCRIPT)
    assert spec is not None
    module = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    spec.loader.exec_module(module)
    return module


_MOD = _load()


def _refactoring_doc(rel: str, cited: int) -> str:
    return (
        "## Refactoring needed\n\n"
        "| File | Lines | Refactoring | Issue |\n"
        "|------|-------|-------------|-------|\n"
        f"| `{rel}` | {cited:,} | Split it. Soon. |"
        " [#1](https://github.com/aallan/vera/issues/1) |\n"
        "\n## Next section\n"
    )


def _write_lines(path: Path, n: int) -> None:
    path.write_text("x\n" * n, encoding="utf-8")


class TestRefactoringCounts:
    def test_exact_match_passes(self, tmp_path: Path) -> None:
        _write_lines(tmp_path / "big.py", 1000)
        errors = _MOD.check_refactoring_counts(
            _refactoring_doc("big.py", 1000), tmp_path
        )
        assert errors == []

    def test_within_tolerance_passes(self, tmp_path: Path) -> None:
        _write_lines(tmp_path / "big.py", 1000)
        errors = _MOD.check_refactoring_counts(
            _refactoring_doc("big.py", 950), tmp_path
        )
        assert errors == []

    def test_drift_beyond_tolerance_fails(self, tmp_path: Path) -> None:
        _write_lines(tmp_path / "big.py", 2000)
        errors = _MOD.check_refactoring_counts(
            _refactoring_doc("big.py", 1000), tmp_path
        )
        assert len(errors) == 1
        assert ">10% drift" in errors[0]
        assert "big.py" in errors[0]

    def test_exact_tolerance_boundary_passes(self, tmp_path: Path) -> None:
        _write_lines(tmp_path / "big.py", 1000)
        errors = _MOD.check_refactoring_counts(
            _refactoring_doc("big.py", 1100), tmp_path
        )
        assert errors == []

    def test_empty_file_with_nonzero_citation_fails(
        self, tmp_path: Path
    ) -> None:
        (tmp_path / "big.py").write_text("", encoding="utf-8")
        errors = _MOD.check_refactoring_counts(
            _refactoring_doc("big.py", 1000), tmp_path
        )
        assert len(errors) == 1
        assert "measured 0" in errors[0]

    def test_hyphenated_path_matched(self, tmp_path: Path) -> None:
        (tmp_path / "spec").mkdir()
        _write_lines(tmp_path / "spec" / "09-standard-library.md", 2000)
        errors = _MOD.check_refactoring_counts(
            _refactoring_doc("spec/09-standard-library.md", 1000), tmp_path
        )
        assert len(errors) == 1
        assert ">10% drift" in errors[0]

    def test_empty_section_with_sentinel_passes(self, tmp_path: Path) -> None:
        """The #419 empty-state convention: once the last oversized file is
        split, the table is replaced by this exact sentence and the gate
        accepts the rowless section."""
        doc = (
            "## Refactoring needed\n\n"
            "No files currently need decomposition.\n"
            "\n## Next section\n"
        )
        assert _MOD.check_refactoring_counts(doc, tmp_path) == []

    def test_empty_section_without_sentinel_fails(self, tmp_path: Path) -> None:
        """The sentinel carve-out must not mask a malformed table: a rowless
        section with any OTHER wording (e.g. a reworded sentence, or a table
        whose rows no longer parse) still trips the gate."""
        doc = (
            "## Refactoring needed\n\n"
            "Nothing needs decomposing right now.\n"
            "\n## Next section\n"
        )
        errors = _MOD.check_refactoring_counts(doc, tmp_path)
        assert len(errors) == 1
        assert "no `file` | count rows" in errors[0]

    def test_missing_file_fails(self, tmp_path: Path) -> None:
        errors = _MOD.check_refactoring_counts(
            _refactoring_doc("gone.py", 1000), tmp_path
        )
        assert len(errors) == 1
        assert "does not exist" in errors[0]

    def test_missing_section_fails(self, tmp_path: Path) -> None:
        errors = _MOD.check_refactoring_counts("# No tables here\n", tmp_path)
        assert errors and "Refactoring needed" in errors[0]

    def test_empty_table_fails(self, tmp_path: Path) -> None:
        text = "## Refactoring needed\n\nNothing tabulated.\n\n## Next\n"
        errors = _MOD.check_refactoring_counts(text, tmp_path)
        assert errors and "no" in errors[0]


_LINK = "[#100](https://github.com/aallan/vera/issues/100)"
_LINK2 = "[#200](https://github.com/aallan/vera/issues/200)"


class TestHistoryRowFormat:
    def test_clean_row_passes(self) -> None:
        text = f"| v0.0.5 | 1 Mar | One sentence with one link ({_LINK}). |\n"
        assert _MOD.check_history_row_format(text) == []

    def test_two_links_fail(self) -> None:
        text = f"| v0.0.5 | 1 Mar | Two fixes ({_LINK}, {_LINK2}). |\n"
        errors = _MOD.check_history_row_format(text)
        assert len(errors) == 1
        assert "2 issue links" in errors[0]

    def test_em_dash_separator_fails(self) -> None:
        text = "| v0.0.5 | 1 Mar | Feature — detail clause. |\n"
        errors = _MOD.check_history_row_format(text)
        assert len(errors) == 1
        assert "separator" in errors[0]

    def test_dateless_rows_exempt(self) -> None:
        text = f"| — | 1 Mar | Tooling row — with links {_LINK} {_LINK2}. |\n"
        assert _MOD.check_history_row_format(text) == []

    def test_prose_and_headers_exempt(self) -> None:
        text = (
            "Prose with — dashes and links to issues/1 issues/2.\n"
            "| Version | Date | What shipped |\n"
            "|---------|------|-------------|\n"
        )
        assert _MOD.check_history_row_format(text) == []

    def test_reports_line_numbers(self) -> None:
        text = "line one\n| v0.0.9 | 2 Mar | Bad — row. |\n"
        errors = _MOD.check_history_row_format(text)
        assert "line 2" in errors[0]
