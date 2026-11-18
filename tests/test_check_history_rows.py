"""Unit tests for `scripts/check_history_rows.py` (#1880).

Each rule gets a failing and a passing case on a synthetic file, and the
repository's HISTORY.md must pass.  The script lives in `scripts/`, not a
package, so it is loaded as a module.
"""

from __future__ import annotations

import importlib.util
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parent.parent
SCRIPT_PATH = ROOT / "scripts" / "check_history_rows.py"


@pytest.fixture(scope="module")
def mod() -> object:
    """Import `check_history_rows.py` as a module."""
    spec = importlib.util.spec_from_file_location("check_history_rows", SCRIPT_PATH)
    assert spec is not None and spec.loader is not None
    m = importlib.util.module_from_spec(spec)
    sys.modules["check_history_rows"] = m
    spec.loader.exec_module(m)
    return m


def _rules(mod: object, source: str) -> list[str]:
    return [v.rule for v in mod.check_text(source)]


def _row(text: str, version: str = "v0.9.1") -> str:
    return f"| {version} | 1 Dec | {text} |\n"


ISSUE = "[#7](https://github.com/aallan/vera/issues/7)"


# --- Rule 1: a row's word cap -------------------------------------------------

def test_row_at_the_cap_passes(mod: object) -> None:
    text = " ".join(["word"] * mod.ROW_CAP) + "."
    assert _rules(mod, _row(text)) == []


def test_row_over_the_cap_fails(mod: object) -> None:
    text = " ".join(["word"] * (mod.ROW_CAP + 1)) + "."
    assert _rules(mod, _row(text)) == ["row over the word cap"]


def test_row_words_are_counted_without_link_targets_or_markup(mod: object) -> None:
    # A link counts as its text, so a long URL adds no words.
    text = "**Label**: " + " ".join(["word"] * (mod.ROW_CAP - 3)) + f" {ISSUE}."
    assert _rules(mod, _row(text)) == []


# --- Rule 2: one sentence -----------------------------------------------------

def test_bold_label_then_one_sentence_passes(mod: object) -> None:
    # The shape of v0.0.1's row: a bold label ending in a full stop.
    assert _rules(mod, _row("**Parser.** Lark grammar with natural-language errors.")) == []


def test_two_sentences_fail(mod: object) -> None:
    text = "**Label**: the first thing shipped.  The second thing shipped too."
    assert _rules(mod, _row(text)) == ["row is more than one sentence"]


def test_a_full_stop_inside_a_name_is_not_a_sentence_end(mod: object) -> None:
    assert _rules(mod, _row("Specification Chapters 9 and 12, see spec/09.md for details.")) == []


# --- Rule 3: at most one issue link --------------------------------------------

def test_one_issue_link_passes(mod: object) -> None:
    assert _rules(mod, _row(f"A fix ({ISSUE}).")) == []


def test_two_issue_links_fail(mod: object) -> None:
    other = "[#8](https://github.com/aallan/vera/pull/8)"
    assert _rules(mod, _row(f"A fix ({ISSUE}, {other}).")) == ["row has more than one issue link"]


# --- Rule 4: no em dash -------------------------------------------------------

def test_en_dash_range_row_passes(mod: object) -> None:
    assert _rules(mod, _row("Housekeeping, 1–3 December.", version="v0.9.1–v0.9.2")) == []


def test_em_dash_fails(mod: object) -> None:
    assert _rules(mod, _row("A fix — and another.")) == ["row has an em dash"]


# --- Rule 5: a stage's prose --------------------------------------------------

def _stage(words: int, heading: str = "## Stage 40: A theme (1 December)") -> str:
    prose = " ".join(["word"] * (words - 2))
    return (
        f"{heading}\n\n*A tagline.*\n\n{prose}\n\n"
        "| Version | Date | What shipped |\n|---|---|---|\n"
        + _row("**Theme**: one sentence.")
        + "\n---\n\n## By the numbers\n\nNot a stage, " + " ".join(["word"] * 200) + "\n"
    )


def test_stage_at_the_cap_passes(mod: object) -> None:
    assert _rules(mod, _stage(mod.STAGE_CAP)) == []


def test_stage_over_the_cap_fails(mod: object) -> None:
    assert _rules(mod, _stage(mod.STAGE_CAP + 1)) == ["stage prose over the word cap"]


def test_a_combined_stage_heading_is_a_stage(mod: object) -> None:
    source = _stage(mod.STAGE_CAP + 1, heading="## Stages 40–41: Two themes (1–3 December)")
    assert _rules(mod, source) == ["stage prose over the word cap"]


def test_the_stage_index_is_not_a_stage(mod: object) -> None:
    source = "## Stage index\n\n" + " ".join(["word"] * 200) + "\n"
    assert _rules(mod, source) == []


# --- The repository -----------------------------------------------------------

def test_repository_history_passes(mod: object) -> None:
    violations = mod.check_text((ROOT / "HISTORY.md").read_text(encoding="utf-8"))
    assert violations == [], violations


def test_main_reports_the_line(mod: object, tmp_path: Path, capsys: pytest.CaptureFixture[str]) -> None:
    path = tmp_path / "HISTORY.md"
    path.write_text("# History\n\n" + _row("One.  Two."), encoding="utf-8")
    assert mod.main([str(path)]) == 1
    assert "HISTORY.md:3: row is more than one sentence" in capsys.readouterr().err
