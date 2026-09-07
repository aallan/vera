"""Tests for the pure per-document checks in scripts/check_doc_counts.py.

Each of these is a function of text (plus, for one, the filesystem), so it
is testable without a pytest collection run:

- ``check_refactoring_counts`` — KNOWN_ISSUES.md "Refactoring needed"
  line counts must stay within ±10% of the measured file sizes.
- ``check_history_row_format`` — HISTORY.md version rows carry at most
  one issue link and no " — " separator.
- ``check_tests_breakdown`` — TESTING.md's passed/stress-deselected/skipped parts
  must sum to the collected total.
- ``check_vera_readme_test_counts`` — the four counts in vera/README.md's
  Test Suite paragraph.
- ``check_release_count`` — README.md's and HISTORY.md's release counts,
  against each other AND against the repository's tags.
- ``check_contributing_hook_count`` — CONTRIBUTING.md's pre-commit hook
  count, against the live `.pre-commit-config.yaml`.
- ``check_ci_lint_scripts`` — TESTING.md's CI-pipeline lint row against the
  scripts `.github/workflows/ci.yml`'s lint job actually runs, in order.

The last four share a failure mode with every other check here and it is
tested for each: a reworded sentence must be an ERROR, not a silent skip,
or rewording switches the gate off.
"""

from __future__ import annotations

import importlib.util
import json
import os
import re
import subprocess
import sys
from pathlib import Path
from typing import Any

import pytest

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

    def test_single_lead_in_dash_passes(self) -> None:
        # The v0.1.x-era template: **bold lead-in** — clauses (one dash).
        text = "| v0.1.5 | 1 Mar | **Feature** — detail clause. |\n"
        assert _MOD.check_history_row_format(text) == []

    def test_second_em_dash_fails(self) -> None:
        text = "| v0.0.5 | 1 Mar | Feature — detail — second clause. |\n"
        errors = _MOD.check_history_row_format(text)
        assert len(errors) == 1
        assert "separator" in errors[0]

    def test_v01_rows_are_inspected(self) -> None:
        # The pre-#972 regex was pinned to v0.0.x; v0.1.x rows went
        # uninspected entirely.
        text = f"| v0.1.5 | 1 Mar | Two fixes ({_LINK}, {_LINK2}). |\n"
        errors = _MOD.check_history_row_format(text)
        assert len(errors) == 1
        assert "2 issue links" in errors[0]

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
        text = "line one\n| v0.0.9 | 2 Mar | Bad — row — twice. |\n"
        errors = _MOD.check_history_row_format(text)
        assert "line 2" in errors[0]


def _overview(passed: int, stress: int, skipped: int, total: int) -> str:
    return (
        "| Metric | Value |\n"
        "|--------|-------|\n"
        f"| **Tests** | {total:,} across 143 files (~108,000 lines of test"
        f" code; {passed:,} passed + {stress} stress-deselected,"
        f" {skipped} skipped) |\n"
    )


class TestTestsBreakdown:
    def test_parts_summing_to_the_total_pass(self) -> None:
        text = _overview(9235, 26, 121, 9382)
        assert _MOD.check_tests_breakdown(text, 9382) == []

    def test_parts_not_summing_to_the_total_fail(self) -> None:
        # The shape that motivated the check: the total is refreshed at
        # release time because a gate reads it, the parts are not.
        text = _overview(9230, 26, 121, 9382)
        errors = _MOD.check_tests_breakdown(text, 9382)
        assert len(errors) == 1
        assert "9,377" in errors[0]
        assert "9,382" in errors[0]

    def test_a_right_total_with_wrong_parts_still_fails(self) -> None:
        # The row's own total is NOT what the parts are checked against —
        # the collected count is — so a self-consistent but stale row is
        # caught by the existing total check, and an inconsistent one here.
        text = _overview(9000, 26, 121, 9147)
        errors = _MOD.check_tests_breakdown(text, 9382)
        assert len(errors) == 1

    def test_reworded_row_is_an_error_not_a_skip(self) -> None:
        text = (
            "| **Tests** | 9,382 across 143 files (~108,000 lines of test"
            " code; 9,235 green, 26 stress and 121 skipped) |\n"
        )
        errors = _MOD.check_tests_breakdown(text, 9382)
        assert len(errors) == 1
        assert "no longer gated" in errors[0]


def _test_suite_para(
    tests: int, files: int, conformance: int, examples: int
) -> str:
    return (
        "## Test Suite\n\n"
        f"Testing spans a **pytest suite** of {tests:,} tests across {files}"
        " files — compiler-internals unit tests plus a **conformance suite**"
        f" ({conformance} programs in `tests/conformance/` validating every"
        " language feature against the spec) and **example programs**"
        f" ({examples} end-to-end demos).\n"
    )


class TestVeraReadmeTestCounts:
    def test_matching_counts_pass(self) -> None:
        text = _test_suite_para(9382, 143, 196, 42)
        assert _MOD.check_vera_readme_test_counts(
            text, 9382, 143, 196, 42
        ) == []

    def test_every_count_is_checked_independently(self) -> None:
        text = _test_suite_para(1, 2, 3, 4)
        errors = _MOD.check_vera_readme_test_counts(text, 9382, 143, 196, 42)
        # Four separate citations, four separate errors — a single
        # aggregate would let three stay wrong after one is fixed.
        assert len(errors) == 4
        joined = " ".join(errors)
        for label in (
            "total tests",
            "test file count",
            "conformance programs",
            "example programs",
        ):
            assert label in joined

    def test_stale_example_count_alone_fails(self) -> None:
        text = _test_suite_para(9382, 143, 196, 37)
        errors = _MOD.check_vera_readme_test_counts(text, 9382, 143, 196, 42)
        assert len(errors) == 1
        assert "example programs" in errors[0]

    def test_reworded_paragraph_is_an_error_not_a_skip(self) -> None:
        text = (
            "## Test Suite\n\nTesting spans 9,382 tests in 143 modules,"
            " 196 conformance programs and 42 demos.\n"
        )
        errors = _MOD.check_vera_readme_test_counts(text, 9382, 143, 196, 42)
        assert len(errors) == 1
        assert "no longer gated" in errors[0]

    def test_thousands_separators_are_read_in_every_count(self) -> None:
        # The prose writes counts with thousands separators once they cross
        # a thousand.  A digits-only group for any of the four would stop
        # matching at that point and report the paragraph as ungated —
        # switching the check off exactly when the number it guards grows.
        text = (
            "## Test Suite\n\n"
            "Testing spans a **pytest suite** of 12,345 tests across 1,143"
            " files — compiler-internals unit tests plus a **conformance"
            " suite** (1,196 programs in `tests/conformance/` validating"
            " every language feature against the spec) and **example"
            " programs** (1,042 end-to-end demos).\n"
        )
        assert _MOD.check_vera_readme_test_counts(
            text, 12345, 1143, 1196, 1042
        ) == []

    def test_counts_are_read_from_the_test_suite_section_only(self) -> None:
        # The pattern spans several sentences, so it matches with DOTALL.
        # Run against the whole file that lets the paragraph's head pair
        # with digits from any LATER section: the Test Suite paragraph can
        # be reworded — no longer stating the counts at all — and the gate
        # still greens off a decoy elsewhere.  That is the silent skip this
        # check exists to prevent, so it must fail loud instead.
        text = (
            "## Test Suite\n\n"
            "Testing spans a **pytest suite** of 9,382 tests across 143"
            " files — unit tests, 196 conformance programs and 42"
            " examples.\n\n"
            "## Current Limitations\n\n"
            "Historic note: the suite once shipped (196 programs in"
            " `tests/conformance/` validating every feature) and (42"
            " end-to-end demos).\n"
        )
        errors = _MOD.check_vera_readme_test_counts(text, 9382, 143, 196, 42)
        assert len(errors) == 1
        assert "no longer gated" in errors[0]

    def test_missing_test_suite_heading_is_an_error_not_a_skip(self) -> None:
        # Renaming the heading moves the paragraph out of the slice; the
        # counts must stop being "checked" loudly, not quietly.
        text = _test_suite_para(9382, 143, 196, 42).replace(
            "## Test Suite", "## Testing"
        )
        errors = _MOD.check_vera_readme_test_counts(text, 9382, 143, 196, 42)
        assert len(errors) == 1
        assert "no longer gated" in errors[0]


class TestContributingHookCount:
    """CONTRIBUTING.md's hook count, and what happens when the sentence moves.

    The number is only tied to `.pre-commit-config.yaml` by this one
    sentence, so a rewrite the pattern stops matching would switch the check
    off in silence — the failure the TESTING.md twin already reports.
    """

    def test_matching_count_passes(self) -> None:
        text = "The repository configures 33 hooks across both stages.\n"
        assert _MOD.check_contributing_hook_count(text, 33) == []

    def test_stale_count_fails(self) -> None:
        text = "The repository configures 32 hooks across both stages.\n"
        errors = _MOD.check_contributing_hook_count(text, 33)
        assert len(errors) == 1
        assert "doc says 32" in errors[0]
        assert "live is 33" in errors[0]

    def test_reworded_sentence_is_an_error_not_a_skip(self) -> None:
        # Same true number, phrasing the pattern cannot see.  Reporting []
        # here would mean any future rewording silently disarms the check.
        text = "The repository sets up 33 pre-commit hooks in total.\n"
        errors = _MOD.check_contributing_hook_count(text, 33)
        assert len(errors) == 1
        assert "could not find" in errors[0]


def _ci_workflow(*lint_scripts: str) -> str:
    """A workflow whose ``lint`` job runs ``lint_scripts``, in order.

    Deliberately carries decoys the check must not pick up: `on:` has
    two-space-indented keys that are not jobs, and the `test`/`security`
    jobs run scripts of their own.
    """
    steps = "".join(
        f"      - name: Step {i}\n        run: python scripts/{name}\n"
        for i, name in enumerate(lint_scripts)
    )
    return (
        "name: CI\n\non:\n  push:\n    branches: [main]\n  pull_request:\n\n"
        "jobs:\n"
        "  test:\n    steps:\n      - run: python scripts/decoy_test.py\n\n"
        "  lint:\n    steps:\n" + steps + "      - name: Lint (ruff)\n"
        "        run: ruff check .\n\n"
        "  security:\n    steps:\n      - run: python scripts/decoy_sec.py\n"
    )


def _lint_row(*scripts: str) -> str:
    listed = ", ".join(f"`{s}`" for s in scripts)
    return (
        "## CI Pipeline\n\n"
        "| Job | Matrix / Runner | What it checks |\n"
        "|-----|----------------|---------------|\n"
        f"| **lint** | Python 3.12 x Ubuntu | {listed}, `ruff check .`,"
        " `uv lock --check` |\n"
    )


class TestCiLintScripts:
    """TESTING.md's CI-pipeline lint row against the workflow it describes.

    The row hand-enumerates the scripts the lint job runs, and nothing tied
    the two together: PR #1257 added `check_editor_grammars.py` as a lint-job
    step without adding it to the row, and the documentation described 22 of
    23 scripts with every gate green.
    """

    def test_matching_row_passes(self) -> None:
        assert _MOD.check_ci_lint_scripts(
            _lint_row("check_a.py", "check_b.py"),
            _ci_workflow("check_a.py", "check_b.py"),
        ) == []

    def test_only_the_lint_job_is_read(self) -> None:
        # The fixture's other jobs run decoy_test.py and decoy_sec.py.  A
        # whole-file scan would report both as undocumented; a job-scoped
        # one reports nothing.
        errors = _MOD.check_ci_lint_scripts(
            _lint_row("check_a.py"), _ci_workflow("check_a.py")
        )
        assert errors == [], errors

    def test_missing_entry_fails(self) -> None:
        # The drift that actually shipped: a step in CI, absent from the row.
        errors = _MOD.check_ci_lint_scripts(
            _lint_row("check_a.py"),
            _ci_workflow("check_a.py", "check_b.py"),
        )
        assert len(errors) == 1
        assert "check_b.py" in errors[0]
        assert "not listed" in errors[0]

    def test_extra_entry_fails(self) -> None:
        # The other direction: a row entry CI stopped running.
        errors = _MOD.check_ci_lint_scripts(
            _lint_row("check_a.py", "check_b.py"),
            _ci_workflow("check_a.py"),
        )
        assert len(errors) == 1
        assert "check_b.py" in errors[0]
        assert "does not run it" in errors[0]

    def test_order_mismatch_fails(self) -> None:
        # Same set, different sequence.  The row reads as the job's order, so
        # a set-only comparison would call this clean and let the row lie.
        errors = _MOD.check_ci_lint_scripts(
            _lint_row("check_b.py", "check_a.py"),
            _ci_workflow("check_a.py", "check_b.py"),
        )
        assert len(errors) == 1
        assert "not in the same order" in errors[0]

    def test_reworded_row_is_an_error_not_a_skip(self) -> None:
        # Renaming the job label loses the row; the scripts must stop being
        # "checked" loudly, not quietly.
        text = _lint_row("check_a.py").replace("| **lint**", "| **linting**")
        errors = _MOD.check_ci_lint_scripts(text, _ci_workflow("check_a.py"))
        assert len(errors) == 1
        assert "could not find" in errors[0]

    def test_missing_lint_job_is_an_error_not_a_skip(self) -> None:
        # And the same on the workflow side — a renamed job would otherwise
        # leave the row compared against nothing.
        ci = _ci_workflow("check_a.py").replace("  lint:", "  linting:")
        errors = _MOD.check_ci_lint_scripts(_lint_row("check_a.py"), ci)
        assert len(errors) == 1
        assert "could not find" in errors[0]
        assert "lint" in errors[0]

    def test_the_shipped_row_matches_the_workflow(self) -> None:
        """The tree is currently clean — this is what keeps CI red if a lint
        step is added without the row, which is how the drift got in."""
        root = _SCRIPT.parent.parent
        testing = (root / "TESTING.md").read_text(encoding="utf-8")
        ci = (root / ".github/workflows/ci.yml").read_text(encoding="utf-8")
        assert _MOD.check_ci_lint_scripts(testing, ci) == []

    def test_the_shipped_row_with_an_entry_removed_fails(self) -> None:
        """Mutation of the artefact rather than the checker: drop the entry
        that actually drifted and the real files must go red."""
        root = _SCRIPT.parent.parent
        testing = (root / "TESTING.md").read_text(encoding="utf-8")
        ci = (root / ".github/workflows/ci.yml").read_text(encoding="utf-8")
        mutated = testing.replace("`check_editor_grammars.py`, ", "", 1)
        assert mutated != testing
        errors = _MOD.check_ci_lint_scripts(mutated, ci)
        assert len(errors) == 1
        assert "check_editor_grammars.py" in errors[0]


def _readme(n: int) -> str:
    return f"Vera is in **active development** at v0.1.10: {n} releases, x.\n"


def _history(n: int) -> str:
    return f"Total: **2,000+ commits, {n} tagged releases, 103 days.**\n"


_TAGS = [f"v0.1.{i}" for i in range(10)]  # ten tags, v0.1.9 the newest


class TestReleaseCount:
    """The release count against the tags, not just against itself.

    README's status line and HISTORY's "By the numbers" total are one
    hand-maintained number in two places.  Cross-checking them against
    EACH OTHER catches a half-applied bump and nothing else: from
    v0.1.8 both read 206 while the repository held 207 tags, agreeing
    with each other the whole way down.  Two documents can be
    consistently wrong, so the tags are the oracle.

    The fixture is ten tags, `v0.1.0`..`v0.1.9`, so "10" is the count
    once the newest is tagged and "11" the count while an eleventh
    release is being cut.
    """

    def test_counts_matching_the_tags_pass(self) -> None:
        assert _MOD.check_release_count(
            _readme(10), _history(10), _TAGS, "0.1.9",
        ) == []

    def test_a_release_cut_counts_its_own_pending_tag(self) -> None:
        # The convention: the PR that bumps the version to an UNTAGGED
        # release also bumps the count, because the release workflow
        # creates that tag only after the merge.  Requiring equality
        # with `git tag` would fail exactly those PRs.
        assert _MOD.check_release_count(
            _readme(11), _history(11), _TAGS, "0.1.10",
        ) == []

    def test_the_pending_tag_is_the_only_slack(self) -> None:
        # Once the version IS tagged, +1 is drift, not a pending release.
        errors = _MOD.check_release_count(
            _readme(11), _history(11), _TAGS, "0.1.9",
        )
        assert len(errors) == 2, errors
        assert "README.md" in errors[0] and "HISTORY.md" in errors[1]

    def test_the_drift_that_shipped_is_caught(self) -> None:
        # v0.1.10's actual state: both documents two behind the tags.
        errors = _MOD.check_release_count(
            _readme(8), _history(8), _TAGS, "0.1.10",
        )
        assert len(errors) == 2, errors
        for err in errors:
            assert "11" in err, err

    def test_each_document_is_reported_separately(self) -> None:
        # One aggregate error would let the second document stay wrong
        # after the first is fixed.
        errors = _MOD.check_release_count(
            _readme(11), _history(8), _TAGS, "0.1.10",
        )
        joined = " ".join(errors)
        assert "HISTORY.md" in joined
        assert any("mismatch" in e for e in errors), errors

    def test_readme_and_history_must_still_agree(self) -> None:
        errors = _MOD.check_release_count(
            _readme(10), _history(9), _TAGS, "0.1.9",
        )
        assert any("mismatch" in e for e in errors), errors

    def test_no_tags_skips_the_oracle_but_not_the_cross_check(self) -> None:
        # A clone without tags (a shallow CI checkout) yields None, which
        # means "no evidence", not "zero releases".  The tag comparison
        # stands down; the two documents must still agree.
        assert _MOD.check_release_count(
            _readme(999), _history(999), None, "0.1.10",
        ) == []
        errors = _MOD.check_release_count(
            _readme(999), _history(998), None, "0.1.10",
        )
        assert any("mismatch" in e for e in errors), errors

    def test_a_reworded_line_is_an_error_not_a_skip(self) -> None:
        # Rewording either sentence must switch the gate OFF loudly.
        errors = _MOD.check_release_count(
            "Vera is at v0.1.10 with lots of releases.\n",
            _history(11), _TAGS, "0.1.10",
        )
        assert any("README.md" in e and "not found" in e for e in errors), (
            errors
        )
        errors = _MOD.check_release_count(
            _readme(11), "Total: 2,000+ commits.\n", _TAGS, "0.1.10",
        )
        assert any("HISTORY.md" in e and "not found" in e for e in errors), (
            errors
        )


def _git_repo(path: Path, tags: tuple[str, ...]) -> Path:
    import subprocess

    # Same sanitised environment the reader uses, taken from the module
    # rather than copied, so the two cannot fall out of step.  Under
    # pre-commit `GIT_DIR`/`GIT_INDEX_FILE` are set, and every command
    # below would then act on the repository being committed to instead
    # of this one — a `git init` under an inherited `GIT_DIR`
    # reinitialises THAT repository, which is not a failure mode to
    # discover twice.  The check is made before any git runs, because
    # `init` is itself the damaging step: a guard after it would fire
    # too late to prevent anything.
    env = _MOD.git_env()
    leaked = set(_MOD.GIT_REPO_ENV_VARS) & set(env)
    assert not leaked, leaked

    def run(*args: str) -> None:
        subprocess.run(
            ["git", "-C", str(path), *args],
            check=True, capture_output=True, text=True, encoding="utf-8",
            env=env,
        )

    path.mkdir(parents=True, exist_ok=True)
    run("init", "-q")
    run("-c", "user.email=t@e.invalid", "-c", "user.name=T",
        "commit", "-q", "--allow-empty", "-m", "seed")
    for tag in tags:
        run("tag", tag)
    return path


class TestReleaseTags:
    """The reader that decides whether the oracle runs at all.

    `check_release_count` stands down when handed ``None``, so a reader
    that answered ``None`` everywhere would switch the gate off in
    silence — the failure mode every other check in this script is
    written against.  These pin both answers on real repositories.
    """

    def test_release_tags_are_read(self, tmp_path: Path) -> None:
        repo = _git_repo(tmp_path / "r", ("v0.1.9", "v0.1.10", "v0.0.24.1"))
        assert sorted(_MOD.release_tags(repo)) == [
            "v0.0.24.1", "v0.1.10", "v0.1.9",
        ]

    def test_non_release_tags_are_not_counted(self, tmp_path: Path) -> None:
        # A `nightly` or `v1.0.0-rc1` is not a release; counting one
        # would push the expected count past every document at once.
        repo = _git_repo(tmp_path / "r", ("v0.1.9", "nightly", "v1.0.0-rc1"))
        assert _MOD.release_tags(repo) == ["v0.1.9"]

    def test_a_checkout_without_tags_is_no_evidence(
        self, tmp_path: Path,
    ) -> None:
        # None, not [] — an empty list would read as "zero releases" and
        # make every documented count wrong.
        repo = _git_repo(tmp_path / "r", ())
        assert _MOD.release_tags(repo) is None

    def test_a_directory_that_is_not_a_repository_is_no_evidence(
        self, tmp_path: Path,
    ) -> None:
        plain = tmp_path / "plain"
        plain.mkdir()
        assert _MOD.release_tags(plain) is None


# ---------------------------------------------------------------------------
# README's project-status line (#1290 rider): the sentence gated the tests
# figure and nothing else on it.  The conformance count beside it drifted
# through two rebases unseen, because `check_readme` returned silently when a
# pattern matched nothing — four of its five patterns matched nothing at all.
# ---------------------------------------------------------------------------

_STATUS = (
    "Vera is in **active development** at v0.1.11: 2,000+ commits, 209 "
    "releases, 11,134 tests, 95% Python code coverage, 229 conformance "
    "programs, 42 examples, and a 14-chapter specification.\n"
)


class TestProjectStatusLine:
    def test_the_shipped_line_is_consistent(self) -> None:
        assert _MOD.check_project_status(_STATUS, 11134, 229, 42, 14) == []

    def test_every_count_on_the_line_is_gated(self) -> None:
        """One error per wrong figure, and the conformance one is among them."""
        errors = _MOD.check_project_status(_STATUS, 1, 2, 3, 4)
        assert len(errors) == 4
        assert any("conformance" in e for e in errors)
        assert any("examples" in e for e in errors)
        assert any("chapter" in e for e in errors)

    def test_the_conformance_count_alone_is_caught(self) -> None:
        """The measured drift: tests right, conformance stale beside it."""
        errors = _MOD.check_project_status(_STATUS, 11134, 230, 42, 14)
        assert len(errors) == 1
        assert "229" in errors[0] and "230" in errors[0]

    def test_a_missing_status_line_is_an_error_not_a_skip(self) -> None:
        # Same true numbers, phrasing the pattern cannot see.  Returning []
        # here is what let four of the five README gates sit dead.
        text = "Vera has 11,134 tests and 229 conformance programs.\n"
        errors = _MOD.check_project_status(text, 11134, 229, 42, 14)
        assert len(errors) == 1
        assert "could not find" in errors[0]

    def test_a_count_dropped_from_the_line_is_an_error_not_a_skip(self) -> None:
        text = _STATUS.replace("229 conformance programs, ", "")
        errors = _MOD.check_project_status(text, 11134, 229, 42, 14)
        assert len(errors) == 1
        # Both branches say "could not find", so the phrase alone cannot
        # tell "the line is gone" from "one figure on it is gone" — and
        # this cell is about the second.  Naming the figure is the
        # discriminator (#1330 review).
        assert "could not find the conformance programs count" in errors[0]
        # The missing-LINE branch quotes the pattern it looked for; the
        # missing-FIGURE branch names the figure.  Both mention the line,
        # so that phrase is not the discriminator.
        assert "Python code coverage" not in errors[0]

    def test_the_counts_are_read_from_the_status_line_only(self) -> None:
        """A decoy elsewhere in the file must not satisfy the gate."""
        text = "Elsewhere: 999 conformance programs.\n\n" + _STATUS
        assert _MOD.check_project_status(text, 11134, 229, 42, 14) == []


# ---------------------------------------------------------------------------
# TESTING.md's dual-target row (#1290 rider): a run-level total from the
# manifest, and a tested/skipped split with three category counts that no
# oracle read.
# ---------------------------------------------------------------------------

_DUAL_ROW = (
    "the **dual-target conformance differential** (all 168 run-level "
    "conformance programs driven under both targets, byte-identical "
    "stdout/stderr required — 118 are dual-tested and 50 skip *loudly* "
    "rather than passing silently: 43 whose compiled WAT imports a host "
    "family outside `IO`/`Random`, 6 with no public zero-argument `main`, "
    "and 1 calling a nondeterministic op.)\n"
)


def _split(**overrides: int) -> Any:
    values = dict(tested=118, skipped=50, families=43, no_main=6, nondeterministic=1)
    values.update(overrides)
    return _MOD.DualTargetSplit(**values)


class TestDualTargetRow:
    def test_the_shipped_row_is_consistent(self) -> None:
        assert _MOD.check_dual_target_row(_DUAL_ROW, 168, _split()) == []

    def test_the_run_level_total_comes_from_the_manifest(self) -> None:
        errors = _MOD.check_dual_target_row(_DUAL_ROW, 169, _split())
        assert [e for e in errors if "run-level total" in e]

    def test_each_part_of_the_split_is_gated(self) -> None:
        errors = _MOD.check_dual_target_row(
            _DUAL_ROW, 168, _split(tested=117, skipped=51)
        )
        assert len(errors) == 2

    def test_each_category_is_gated(self) -> None:
        errors = _MOD.check_dual_target_row(
            _DUAL_ROW, 168, _split(families=42, no_main=7, nondeterministic=2)
        )
        assert len(errors) == 3
        # Counted AND attributed: three errors are also what a reporter
        # that swapped two category messages returns, and the three
        # values are distinct, so each can name its own (#1330 review).
        joined = "\n".join(errors)
        assert "families: doc says 43, a live run has 42" in joined
        assert "no_main: doc says 6, a live run has 7" in joined
        assert "nondeterministic: doc says 1, a live run has 2" in joined

    def test_the_split_must_sum_to_the_run_level_total(self) -> None:
        """Three consistent-looking numbers that do not add up is drift."""
        errors = _MOD.check_dual_target_row(
            _DUAL_ROW.replace("all 168 run-level", "all 200 run-level"),
            200,
            _split(),
        )
        assert [e for e in errors if "does not add up" in e]

    def test_the_categories_must_sum_to_the_skip_total(self) -> None:
        row = _DUAL_ROW.replace("and 1 calling", "and 2 calling")
        errors = _MOD.check_dual_target_row(row, 168, _split(nondeterministic=2))
        assert [e for e in errors if "do not add up" in e]

    def test_a_reworded_row_is_an_error_not_a_skip(self) -> None:
        # The same true numbers, phrased so no pattern sees them.
        text = "The differential drives 168 programmes, skipping 50 of them.\n"
        errors = _MOD.check_dual_target_row(text, 168, _split())
        assert [e for e in errors if "could not find" in e]

    def test_one_reworded_figure_is_an_error_not_a_skip(self) -> None:
        """The row still parses; a single category has been reworded away.

        Every other figure agrees, so a silent skip here leaves the row
        looking checked while one of its five numbers is unread.
        """
        row = _DUAL_ROW.replace("43 whose compiled WAT", "forty-three whose WAT")
        errors = _MOD.check_dual_target_row(row, 168, _split())
        assert len(errors) == 1
        assert "could not find" in errors[0] and "families" in errors[0]

    def test_the_live_split_is_read_from_the_test_run(self) -> None:
        """Non-vacuity: parsed from real ``-rs`` output, not from the doc."""
        report = (
            "SKIPPED [43] tests/test_wasi_target.py:1130: family gate: "
            "--target wasi-p2 does not support the following host family: map\n"
            "SKIPPED [6] tests/test_wasi_target.py:1130: family gate: "
            "--target wasi-p2 requires a public zero-argument `main` entry point\n"
            "SKIPPED [1] tests/test_wasi_target.py:1124: nondeterministic ops "
            "['random_int']\n"
            "118 passed, 50 skipped in 3.15s\n"
        )
        assert _MOD.parse_dual_target_report(report) == _split()

    def test_an_unclassified_skip_is_an_error_not_a_skip(self) -> None:
        report = (
            "SKIPPED [50] tests/test_wasi_target.py:1130: some new reason\n"
            "118 passed, 50 skipped in 3.15s\n"
        )
        assert _MOD.parse_dual_target_report(report) is None

    def test_an_unclassified_skip_beside_a_correct_total_is_still_an_error(
        self,
    ) -> None:
        """The three documented categories already account for every skip.

        Folding a fourth reason into none of them leaves the arithmetic
        looking right, so the sum reconciliation alone cannot catch it.
        """
        report = (
            "SKIPPED [43] host family: map\n"
            "SKIPPED [6] requires a public zero-argument `main`\n"
            "SKIPPED [1] nondeterministic ops ['random_int']\n"
            "SKIPPED [3] tests/test_wasi_target.py:9: a brand new reason\n"
            "118 passed, 50 skipped in 3.15s\n"
        )
        assert _MOD.parse_dual_target_report(report) is None

    def test_classified_skips_that_miss_the_summary_total_are_an_error(self) -> None:
        """Every reason is known and they still do not account for the run.

        The complement of the case above: the unclassified-reason guard is
        satisfied here, so only the sum reconciliation can catch it.
        """
        report = (
            "SKIPPED [43] host family: map\n"
            "SKIPPED [6] requires a public zero-argument `main`\n"
            "SKIPPED [1] nondeterministic ops ['random_int']\n"
            "118 passed, 55 skipped in 3.15s\n"
        )
        assert _MOD.parse_dual_target_report(report) is None

    def test_a_report_with_no_summary_line_is_an_error_not_a_skip(self) -> None:
        assert _MOD.parse_dual_target_report("nothing to see here\n") is None

    def test_a_summary_omitting_the_skipped_category_is_read(self) -> None:
        """pytest prints no category with a zero count, so `174 passed in
        3.1s` is a well-formed summary.  Requiring both groups made it
        unreadable, and an unreadable report is reported as drift — a
        false failure (#1329 review)."""
        split = _MOD.parse_dual_target_report("174 passed in 3.15s\n")
        assert split == _MOD.DualTargetSplit(174, 0, 0, 0, 0)

    def test_a_summary_omitting_the_passed_category_is_read(self) -> None:
        """The complement: every run-level programme skipped."""
        report = (
            "SKIPPED [52] host family: map\n"
            "52 skipped in 3.15s\n"
        )
        assert _MOD.parse_dual_target_report(report) == _MOD.DualTargetSplit(
            0, 52, 52, 0, 0
        )


# ---------------------------------------------------------------------------
# KNOWN_ISSUES' Bugs table (#1290 rider): one row per open `bug` issue.
#
# The parity half needs the GitHub API, which a pre-commit hook must not
# depend on, so it is opt-in: `--check-bug-issues` at release-PR time.  The
# structural half is pure text and always on.
# ---------------------------------------------------------------------------


# The standing paragraph the `## Bugs` section has carried since the file
# was written.  Every fixture keeps one, because it is exactly what made
# the old whole-body-equals-the-marker reading of the empty form
# unsatisfiable (#1401): a section written the documented way was rejected
# by the message that prescribed it.
_BUGS_DESCRIPTION = (
    "Defects in shipped compiler, runtime, or tooling behaviour — this"
    " table matches the issue tracker's open `bug`-labelled issues"
    " one-to-one."
)


def _bugs_section(body: str) -> str:
    """A KNOWN_ISSUES.md whose `## Bugs` section holds `body`."""
    return (
        f"# Known Issues\n\n## Bugs\n\n{_BUGS_DESCRIPTION}\n\n{body}\n\n"
        "## Limitations\n\n| Limitation | Issue |\n|-----------|-------|\n"
        "| Something missing. |"
        " [#900](https://github.com/aallan/vera/issues/900) |\n"
    )


def _bugs(*rows: str) -> str:
    body = "\n".join(rows)
    return _bugs_section(f"| Bug | Issue |\n|-----|-------|\n{body}")


def _row(number: int, text: str = "Something is wrong.") -> str:
    url = f"https://github.com/aallan/vera/issues/{number}"
    return f"| {text} | [#{number}]({url}) |"


class TestBugRows:
    def test_the_shipped_table_parses(self) -> None:
        text = (Path(__file__).parent.parent / "KNOWN_ISSUES.md").read_text(
            encoding="utf-8"
        )
        rows = _MOD.bug_rows(text)
        assert rows is not None
        # The floor is derived from the file, not a literal: `> 5` would
        # fail the day the tracker is burned down to five open bugs, which
        # is a project state rather than a regression — and it would not
        # catch the parser returning a SHORT list, which is the failure
        # worth naming (#1329 review).
        section = re.search(r"^## Bugs[ \t]*$(.*?)(?=^## )", text, re.M | re.S)
        assert section is not None
        table = [
            line
            for line in section.group(1).splitlines()
            if line.startswith("|") and not set(line) <= set("|- ")
        ][1:]  # drop the header row
        assert table, "the Bugs table is no longer being read"
        assert len(rows) == len(table)
        assert len(set(rows)) == len(rows)

    def test_a_row_with_no_issue_link_is_an_error(self) -> None:
        text = _bugs("| A bug with no tracker. | none |")
        errors = _MOD.check_bug_rows(text)
        assert len(errors) == 1 and "does not hold exactly one" in errors[0]

    def test_two_rows_for_one_issue_are_an_error(self) -> None:
        """One-to-one: two rows citing one issue is a duplicate, not two bugs."""
        text = _bugs(_row(101), _row(101, "The same bug again."))
        errors = _MOD.check_bug_rows(text)
        assert len(errors) == 1 and "twice" in errors[0]

    def test_a_link_whose_number_and_url_disagree_is_an_error(self) -> None:
        text = _bugs(
            "| Mislinked. | [#101](https://github.com/aallan/vera/issues/202) |"
        )
        errors = _MOD.check_bug_rows(text)
        assert len(errors) == 1 and "does not hold exactly one" in errors[0]

    def test_a_pull_request_link_is_not_an_issue_link(self) -> None:
        text = _bugs("| Wrong kind. | [#101](https://github.com/aallan/vera/pull/101) |")
        errors = _MOD.check_bug_rows(text)
        assert len(errors) == 1 and "does not hold exactly one" in errors[0]

    def test_a_row_carrying_a_pipe_in_its_prose_still_parses(self) -> None:
        text = _bugs(_row(101, "The `|>` operator is wrong."))
        assert _MOD.check_bug_rows(text) == []

    def test_the_no_known_bugs_convention_is_not_an_empty_table(self) -> None:
        text = "# Known Issues\n\n## Bugs\n\nNo known bugs.\n\n## Limitations\n"
        assert _MOD.bug_rows(text) == []
        assert _MOD.check_bug_rows(text) == []

    def test_an_empty_bugs_section_is_an_error_not_a_skip(self) -> None:
        text = "# Known Issues\n\n## Bugs\n\n## Limitations\n"
        errors = _MOD.check_bug_rows(text)
        assert len(errors) == 1 and "does not end with" in errors[0]

    def test_a_renamed_heading_is_an_error_not_a_skip(self) -> None:
        text = _bugs(_row(101)).replace("## Bugs", "## Open bugs")
        errors = _MOD.check_bug_rows(text)
        assert len(errors) == 1 and "not found" in errors[0]


class TestBugsTableDrivenToZero:
    """#1401 — the burndown's success state has to be writable.

    The marker is recognised BESIDE the section's standing description
    rather than instead of it, which is what the old whole-body-equals
    reading could not express: the documented empty form was rejected by
    the very message that prescribed it, and the condition is reachable
    exactly when the burndown succeeds — blocking the PR that makes it
    succeed.  What must NOT become readable is a table emptied without a
    marker, which is the accident the gate exists for.
    """

    def test_the_marker_is_read_beside_the_description(self) -> None:
        text = _bugs_section("No known bugs.")
        assert _MOD.bug_rows(text) == []
        assert _MOD.check_bug_rows(text) == []
        assert _BUGS_DESCRIPTION in text

    def test_a_rowless_section_without_the_marker_is_an_error(self) -> None:
        """The description alone is not a claim of zero — it is a
        section whose table went missing."""
        text = _bugs_section("Some prose but no table and no marker.")
        errors = _MOD.check_bug_rows(text)
        assert _MOD.bug_rows(text) is None
        assert len(errors) == 1 and "No known bugs." in errors[0]

    def test_an_emptied_table_left_behind_is_an_error(self) -> None:
        """The accident the gate exists for: the last row is deleted and
        the table's header and separator are left standing."""
        text = _bugs_section("| Bug | Issue |\n|-----|-------|")
        errors = _MOD.check_bug_rows(text)
        assert _MOD.bug_rows(text) is None
        assert len(errors) == 1 and "does not end with" in errors[0]

    @pytest.mark.parametrize(
        "body",
        [
            pytest.param(
                f"| Bug | Issue |\n|-----|-------|\n{_row(101)}\n\n"
                "No known bugs.",
                id="marker-after-the-table",
            ),
            pytest.param(
                "No known bugs.\n\n"
                f"| Bug | Issue |\n|-----|-------|\n{_row(101)}",
                id="marker-before-the-table",
            ),
            pytest.param(
                f"| Bug | Issue |\n|-----|-------|\n{_row(101)}\n\n"
                "No known bugs.\n\n"
                f"| Bug | Issue |\n|-----|-------|\n{_row(102)}",
                id="marker-between-two-tables",
            ),
        ],
    )
    def test_the_marker_beside_a_stray_row_is_a_contradiction(
        self, body: str
    ) -> None:
        """A section claiming both zero and one is not readable as
        either, in ANY ordering.

        Written as a permutation rather than one projection of it: the
        guard was `lines[-1] == marker`, so the marker ABOVE a table was
        no marker at all and the rows came back clean — and that is the
        ordinary shape, since at zero the section ends with the marker
        and the next bug's table is appended below it (PR #1411 review).
        """
        text = _bugs_section(body)
        errors = _MOD.check_bug_rows(text)
        assert _MOD.bug_rows(text) is None
        assert len(errors) == 1 and "both some open bugs and none" in errors[0]

    def test_a_leftover_table_header_beside_the_marker_is_an_error(
        self,
    ) -> None:
        """The zero form has no table at all.  A header and separator
        left standing beside the marker parsed to no rows and read as
        zero, so the enforced form and the documented one differed."""
        text = _bugs_section("| Bug | Issue |\n|-----|-------|\n\nNo known bugs.")
        assert _MOD.bug_rows(text) is None
        errors = _MOD.check_bug_rows(text)
        assert len(errors) == 1 and "not even a leftover header row" in errors[0]

    def test_the_marker_must_be_the_last_line(self) -> None:
        """Trailing prose after the marker means the section says
        something further, and the gate cannot know it is not a
        qualification of the claim."""
        text = _bugs_section("No known bugs.\n\nBut see the tracker.")
        assert _MOD.bug_rows(text) is None

    def test_a_prose_mention_of_the_marker_is_not_the_marker(self) -> None:
        """The marker is a whole line, not a substring: the standing
        description is precisely the place that would one day quote it,
        and a quotation is not a claim."""
        text = _bugs_section(
            "An empty section is written `No known bugs.` rather than left"
            " as a bare table."
        )
        assert _MOD.bug_rows(text) is None

    @pytest.mark.parametrize(
        "body",
        [
            pytest.param("No known bugs.", id="zero"),
            pytest.param(f"| Bug | Issue |\n|--|--|\n{_row(101)}", id="one-row"),
            pytest.param("No table and no marker.", id="unreadable"),
            pytest.param("| Bug | Issue |\n|--|--|", id="emptied-table"),
            pytest.param(
                f"No known bugs.\n\n| Bug | Issue |\n|--|--|\n{_row(101)}",
                id="contradiction",
            ),
            pytest.param("No known bugs.\n\nAnd more.", id="marker-not-last"),
        ],
    )
    def test_the_two_readers_of_the_section_agree(self, body: str) -> None:
        """`bug_rows` and `check_bug_rows` read the SAME section through
        the same configuration, and must not disagree about whether it is
        readable: an unreadable section that reports no error would leave
        `main()` skipping the parity check in silence, and a readable one
        that reports an error would block a correctly-written file.

        Pinned as behaviour rather than by sharing a constant, which is
        what the duplication between the two call sites would otherwise
        risk (PR #1411 CodeRabbit review).
        """
        text = _bugs_section(body)
        readable = _MOD.bug_rows(text) is not None
        clean = _MOD.check_bug_rows(text) == []
        assert readable == clean

    def test_the_two_readers_of_the_burndown_agree(self) -> None:
        """The burndown pair carries the same obligation."""
        for body in (
            f"*One open bugs, driven to zero.*\n\n{_BURNDOWN_DESCRIPTION}\n\n"
            "| Issue | What |\n|---|---|\n"
            "| [#101](https://github.com/aallan/vera/issues/101) | A bug. |",
            f"*Zero open bugs, driven to zero.*\n\n{_BURNDOWN_DESCRIPTION}\n\n"
            "No open bugs.",
            f"*Zero open bugs, driven to zero.*\n\n{_BURNDOWN_DESCRIPTION}",
        ):
            roadmap = _roadmap(body)
            readable = _MOD.roadmap_burndown_rows(roadmap) is not None
            rows = _MOD.roadmap_burndown_rows(roadmap) or []
            known = _bugs(*(_row(n) for n in rows)) if rows else _bugs_section(
                "No known bugs."
            )
            clean = _MOD.check_burndown_header_matches_rows(roadmap, known) == []
            assert readable == clean, body

    def test_the_error_names_the_form_it_wants(self) -> None:
        """The regression in prose: the old single message rejected the
        documented form while prescribing it, so a maintainer following
        the error could not satisfy it."""
        errors = _MOD.check_bug_rows(_bugs_section("No table here."))
        assert len(errors) == 1
        prescribed = re.search(r"`([^`]*bugs\.)`", errors[0])
        assert prescribed is not None
        fixed = _bugs_section(prescribed.group(1))
        assert _MOD.check_bug_rows(fixed) == []


# ---------------------------------------------------------------------------
# ROADMAP's burndown header word vs. its own table vs. KNOWN_ISSUES' Bugs
# table (#1370-class): two parallel PRs each hand-wrote "Nineteen" from a
# stale 20-count independently on the same night, and whichever merged
# second was silently wrong.  This is the gate that ends the class.
# ---------------------------------------------------------------------------


_BURNDOWN_DESCRIPTION = (
    "A bug class outranks stage work, so the next release takes the open"
    " `bug`-labelled set as its queue."
)


def _roadmap(burndown_body: str | None) -> str:
    """A ROADMAP.md whose burndown section holds `burndown_body`.

    ``None`` builds the file with NO burndown section at all — the form
    a burndown driven to zero takes once it is past, its record living
    in HISTORY.md and CHANGELOG.md (#1401).
    """
    burndown = (
        ""
        if burndown_body is None
        else f"## The v0.1.14 burndown\n\n{burndown_body}\n\n"
    )
    return (
        "# Roadmap\n\n"
        "## Where we are\n\n"
        "12,290 tests, 244 conformance programs, 43 examples, 14 spec chapters.\n\n"
        f"{burndown}"
        "## Stage 19 — next stage\n\n"
        "Some stage content.\n"
    )


def _roadmap_burndown(header_word: str, *issue_numbers: int) -> str:
    rows = "\n".join(
        f"| [#{n}](https://github.com/aallan/vera/issues/{n}) | Something. |"
        for n in issue_numbers
    )
    return _roadmap(
        f"*{header_word} open bugs, driven to zero.*\n\n"
        f"{_BURNDOWN_DESCRIPTION}\n\n"
        "| Issue | What |\n|---|---|\n"
        f"{rows}"
    )


class TestBurndownHeaderMatchesRows:
    def test_the_shipped_roadmap_is_consistent(self) -> None:
        """Regression pin against the real files: the header word, the
        burndown table's own row count, and KNOWN_ISSUES.md's Bugs
        table row count must already agree."""
        roadmap = (Path(__file__).parent.parent / "ROADMAP.md").read_text(
            encoding="utf-8"
        )
        known_issues = (
            Path(__file__).parent.parent / "KNOWN_ISSUES.md"
        ).read_text(encoding="utf-8")
        assert _MOD.check_burndown_header_matches_rows(roadmap, known_issues) == []

    def test_all_three_agreeing_is_clean(self) -> None:
        roadmap = _roadmap_burndown("Two", 101, 102)
        known_issues = _bugs(_row(101), _row(102))
        assert _MOD.check_burndown_header_matches_rows(roadmap, known_issues) == []

    def test_header_word_stale_relative_to_both_tables_is_an_error(self) -> None:
        """The exact #1370 shape: the header still says a count from
        before a row was removed, while both tables already agree with
        each other at the new (lower) count."""
        roadmap = _roadmap_burndown("Twenty", 101)
        known_issues = _bugs(_row(101))
        errors = _MOD.check_burndown_header_matches_rows(roadmap, known_issues)
        assert len(errors) == 1
        assert "Twenty" in errors[0] and "20" in errors[0] and "1" in errors[0]

    def test_burndown_table_row_count_disagreeing_is_an_error(self) -> None:
        """Header and KNOWN_ISSUES agree; the burndown table itself
        has a stray extra (or missing) row — a copy/rebase slip in the
        table rather than in the header word."""
        roadmap = _roadmap_burndown("One", 101, 102)
        known_issues = _bugs(_row(101))
        errors = _MOD.check_burndown_header_matches_rows(roadmap, known_issues)
        assert len(errors) == 1

    def test_known_issues_row_count_disagreeing_is_an_error(self) -> None:
        """Header and the burndown table agree with each other; only
        KNOWN_ISSUES.md's Bugs table has drifted from both."""
        roadmap = _roadmap_burndown("Two", 101, 102)
        known_issues = _bugs(_row(101))
        errors = _MOD.check_burndown_header_matches_rows(roadmap, known_issues)
        assert len(errors) == 1

    def test_hyphenated_compound_number_words_parse(self) -> None:
        roadmap = _roadmap_burndown(
            "Twenty-one", *range(101, 122)
        )
        known_issues = _bugs(*(_row(n) for n in range(101, 122)))
        assert _MOD.check_burndown_header_matches_rows(roadmap, known_issues) == []

    def test_an_unrecognised_header_word_is_an_error(self) -> None:
        roadmap = _roadmap_burndown("Several", 101)
        known_issues = _bugs(_row(101))
        errors = _MOD.check_burndown_header_matches_rows(roadmap, known_issues)
        assert len(errors) == 1 and "Several" in errors[0]

    def test_a_missing_burndown_section_beside_open_bugs_is_an_error(self) -> None:
        roadmap = "# Roadmap\n\n## Where we are\n\nNo burndown here.\n"
        known_issues = _bugs(_row(101))
        errors = _MOD.check_burndown_header_matches_rows(roadmap, known_issues)
        assert len(errors) == 1 and "burndown" in errors[0]

    def test_an_unreadable_bugs_table_is_reported_not_assumed_zero(self) -> None:
        """The cross-check's other input failing must not be mistaken
        for agreement: an unreadable Bugs table is its own error, and it
        is reported before the burndown section is consulted at all."""
        roadmap = _roadmap_burndown("One", 101)
        known_issues = _bugs_section("A table that went missing.")
        errors = _MOD.check_burndown_header_matches_rows(roadmap, known_issues)
        assert len(errors) == 1 and "KNOWN_ISSUES.md" in errors[0]


class TestBurndownDrivenToZero:
    """#1401 — ROADMAP's half of the same wall.

    An emptied burndown table returned ``None`` and reported "burndown
    table has no issue rows", so `*Zero open bugs, driven to zero.*` was
    unwritable.  Two forms read as zero: the section RETIRED (deleted —
    a burndown all of whose rows are closed is past, and the project's
    future-vs-past rule puts past in HISTORY/CHANGELOG), and the section
    KEPT with its table replaced by the sibling marker `No open bugs.`.
    Neither is a way past the gate — both are still cross-checked
    against KNOWN_ISSUES.md's Bugs table.
    """

    _ZERO_BUGS = _bugs_section("No known bugs.")

    def test_a_retired_section_reads_as_zero(self) -> None:
        assert (
            _MOD.check_burndown_header_matches_rows(
                _roadmap(None), self._ZERO_BUGS
            )
            == []
        )

    def test_a_retired_section_is_still_cross_checked(self) -> None:
        """Absence reads as zero, so it must disagree with a Bugs table
        that still has rows — otherwise deleting the section becomes the
        way past the gate rather than the way to express success."""
        errors = _MOD.check_burndown_header_matches_rows(
            _roadmap(None), _bugs(_row(101), _row(102))
        )
        assert len(errors) == 1
        assert "#101" in errors[0] and "#102" in errors[0]

    def test_a_kept_section_with_the_marker_reads_as_zero(self) -> None:
        roadmap = _roadmap(
            "*Zero open bugs, driven to zero.*\n\n"
            f"{_BURNDOWN_DESCRIPTION}\n\nNo open bugs."
        )
        assert _MOD.roadmap_burndown_rows(roadmap) == []
        assert (
            _MOD.check_burndown_header_matches_rows(roadmap, self._ZERO_BUGS)
            == []
        )

    def test_a_kept_section_with_a_bare_empty_table_is_an_error(self) -> None:
        """The same accident as its KNOWN_ISSUES sibling: the last row
        deleted, the header and separator left standing, no marker."""
        roadmap = _roadmap(
            "*Zero open bugs, driven to zero.*\n\n"
            f"{_BURNDOWN_DESCRIPTION}\n\n| Issue | What |\n|---|---|"
        )
        errors = _MOD.check_burndown_header_matches_rows(
            roadmap, self._ZERO_BUGS
        )
        assert _MOD.roadmap_burndown_rows(roadmap) is None
        assert len(errors) == 1 and "No open bugs." in errors[0]

    _BURNDOWN_ROW = "| [#101](https://github.com/aallan/vera/issues/101) | A bug. |"

    @pytest.mark.parametrize(
        "order",
        ["marker-after-the-table", "marker-before-the-table"],
    )
    def test_the_marker_beside_a_stray_row_is_a_contradiction(
        self, order: str
    ) -> None:
        """The burndown twin of the KNOWN_ISSUES permutation: the marker
        above a table was ignored, so `No open bugs.` could sit over a
        one-row burndown and read as one open bug with the header word
        `One` agreeing (PR #1411 review)."""
        table = f"| Issue | What |\n|---|---|\n{self._BURNDOWN_ROW}"
        body = (
            f"{table}\n\nNo open bugs."
            if order == "marker-after-the-table"
            else f"No open bugs.\n\n{table}"
        )
        roadmap = _roadmap(
            "*One open bugs, driven to zero.*\n\n"
            f"{_BURNDOWN_DESCRIPTION}\n\n{body}"
        )
        assert _MOD.roadmap_burndown_rows(roadmap) is None
        errors = _MOD.check_burndown_header_matches_rows(
            roadmap, _bugs(_row(101))
        )
        assert len(errors) == 1 and "both some open bugs and none" in errors[0]

    def test_the_marker_does_not_bypass_the_header_word(self) -> None:
        """The zero form is still three numbers agreeing: a marked table
        beside a header word that has not been updated is the #1370
        drift, unchanged by the new empty form."""
        roadmap = _roadmap(
            "*One open bugs, driven to zero.*\n\n"
            f"{_BURNDOWN_DESCRIPTION}\n\nNo open bugs."
        )
        errors = _MOD.check_burndown_header_matches_rows(
            roadmap, self._ZERO_BUGS
        )
        assert len(errors) == 1 and "'One'" in errors[0]

    def test_a_kept_marked_section_is_still_cross_checked(self) -> None:
        """The other zero form's cross-check: `No open bugs.` beside a
        Bugs table that still has a row is a disagreement, not zero."""
        roadmap = _roadmap(
            "*Zero open bugs, driven to zero.*\n\n"
            f"{_BURNDOWN_DESCRIPTION}\n\nNo open bugs."
        )
        errors = _MOD.check_burndown_header_matches_rows(
            roadmap, _bugs(_row(101))
        )
        assert len(errors) == 1
        assert "KNOWN_ISSUES.md Bugs table rows = 1" in errors[0]


class TestBugIssueParity:
    def test_a_matching_pair_of_sets_is_clean(self) -> None:
        assert _MOD.check_bug_issue_parity([101, 102], [102, 101]) == []

    def test_an_open_bug_issue_with_no_row_is_reported(self) -> None:
        errors = _MOD.check_bug_issue_parity([101], [101, 102])
        assert len(errors) == 1 and "#102" in errors[0]

    def test_a_row_whose_issue_is_not_an_open_bug_is_reported(self) -> None:
        errors = _MOD.check_bug_issue_parity([101, 103], [101])
        assert len(errors) == 1 and "#103" in errors[0]

    def test_no_open_bug_issues_is_an_error_not_a_skip(self) -> None:
        """An empty fetch beside rows is a failed query, not a clean
        bill of health."""
        errors = _MOD.check_bug_issue_parity([101], [])
        assert [e for e in errors if "not found" in e]

    def test_both_sides_at_zero_agree(self) -> None:
        """#1401 — the burndown's success state, checked against the
        tracker rather than exempted from it.  A query that FAILED
        cannot reach here as `[]`: `open_bug_issues` raises
        `BugQueryError` instead, which is what lets an empty list be
        read as the real answer it is."""
        assert _MOD.check_bug_issue_parity([], []) == []

    def test_zero_rows_against_a_non_empty_tracker_is_an_error(self) -> None:
        """The other half of the zero contract: agreeing at zero must
        not become passing at zero.  A file claiming no open bugs while
        the tracker carries some is exactly the state the release gate
        is for."""
        errors = _MOD.check_bug_issue_parity([], [1317])
        assert len(errors) == 1 and "#1317" in errors[0]

    def test_the_empty_query_guard_still_raises_at_the_query(self) -> None:
        """The guard `check_bug_issue_parity` gave up at zero has to
        live somewhere: `open_bug_issues` raises rather than returning
        an empty list, so a transport or payload failure is never read
        as a burned-down tracker."""
        source = _SCRIPT.read_text(encoding="utf-8")
        body = source[source.index("def open_bug_issues(") :]
        body = body[: body.index("\ndef ")]
        assert "raise BugQueryError" in body

    def test_the_parity_check_is_not_wired_into_the_default_run(self) -> None:
        """A pre-commit hook must not depend on the GitHub API."""
        source = _SCRIPT.read_text(encoding="utf-8")
        assert "--check-bug-issues" in source
        # EVERY call site, not just the last one: `rindex` inspected only
        # the final occurrence, so an unguarded call added above it would
        # leave this green while the pre-commit hook made a network call
        # (#1329 review).
        calls = [
            index
            for index in range(len(source))
            if source.startswith("check_bug_issue_parity(", index)
            and not source.startswith("def check_bug_issue_parity(", max(0, index - 4))
        ]
        assert calls, "the parity check is no longer called at all"
        for index in calls:
            guarded = source[max(0, index - 600) : index]
            assert "args.check_bug_issues" in guarded


# ---------------------------------------------------------------------------
# The shipped documents, driven to the zero forms they will take (#1401).
# The fixtures above pin the RULE; these pin that the rule fits the real
# files, which is the half a synthetic fixture cannot show.
# ---------------------------------------------------------------------------

_ROOT = Path(__file__).parent.parent
_TIP_BUGS_SECTION = re.compile(r"^## Bugs[ \t]*$(.*?)(?=^## |\Z)", re.M | re.S)
_TIP_BURNDOWN_SECTION = re.compile(
    r"^## The v[\d.]+ burndown[ \t]*$(.*?)(?=^## |\Z)", re.M | re.S
)


def _tip_known_issues_at_zero() -> tuple[str, str]:
    """The shipped KNOWN_ISSUES.md with its Bugs rows removed and the
    marker written after the description the section keeps.

    Returns the text and that description, so a cell can assert the
    paragraph SURVIVED rather than trust the transformation: the
    workaround available before this fix was to delete it, which lost
    the file's statement of the one-to-one convention.
    """
    text = (_ROOT / "KNOWN_ISSUES.md").read_text(encoding="utf-8")
    section = _TIP_BUGS_SECTION.search(text)
    assert section is not None
    description = section.group(1).strip().split("\n\n")[0]
    zeroed = f"\n\n{description}\n\nNo known bugs.\n\n"
    return (
        text[: section.start(1)] + zeroed + text[section.end(1) :],
        description,
    )


def _tip_roadmap_retired() -> str:
    """The shipped ROADMAP.md with its burndown section deleted."""
    text = (_ROOT / "ROADMAP.md").read_text(encoding="utf-8")
    section = _TIP_BURNDOWN_SECTION.search(text)
    if section is None:
        return text
    return text[: section.start()] + text[section.end() :]


def _tip_roadmap_marked() -> str:
    """The shipped ROADMAP.md with its burndown section kept and its
    table replaced by the marker.  Built by substitution when the tip
    still has the section and by appending when it no longer does, so
    this form is exercised either side of the retirement."""
    text = (_ROOT / "ROADMAP.md").read_text(encoding="utf-8")
    kept = (
        "## The v0.2.0 burndown\n\n"
        "*Zero open bugs, driven to zero.*\n\n"
        f"{_BURNDOWN_DESCRIPTION}\n\n"
        "No open bugs.\n\n"
    )
    section = _TIP_BURNDOWN_SECTION.search(text)
    if section is None:
        return text.rstrip("\n") + "\n\n" + kept
    return text[: section.start()] + kept + text[section.end() :]


class TestReleaseTipZeroState:
    def test_the_shipped_bugs_section_at_zero_keeps_its_description(self) -> None:
        text, description = _tip_known_issues_at_zero()
        # Not the table's first line, and not the marker itself: either
        # would make the fixture pass for a reason that is not the one
        # being pinned.
        assert description and not description.startswith("|")
        assert description != "No known bugs."
        assert description in text
        assert _MOD.bug_rows(text) == []
        assert _MOD.check_bug_rows(text) == []

    def test_the_shipped_roadmap_retired_reads_as_zero(self) -> None:
        known_issues, _ = _tip_known_issues_at_zero()
        assert _TIP_BURNDOWN_SECTION.search(_tip_roadmap_retired()) is None
        assert (
            _MOD.check_burndown_header_matches_rows(
                _tip_roadmap_retired(), known_issues
            )
            == []
        )

    def test_the_shipped_roadmap_marked_reads_as_zero(self) -> None:
        known_issues, _ = _tip_known_issues_at_zero()
        assert (
            _MOD.check_burndown_header_matches_rows(
                _tip_roadmap_marked(), known_issues
            )
            == []
        )

    def test_the_shipped_files_at_zero_disagree_with_a_live_bugs_table(
        self,
    ) -> None:
        """The zero forms are not a bypass: the shipped ROADMAP driven to
        zero beside a Bugs table that still holds rows is an error."""
        live = (_ROOT / "KNOWN_ISSUES.md").read_text(encoding="utf-8")
        rows = _MOD.bug_rows(live)
        assert rows is not None
        if not rows:  # the burndown has already landed; nothing to disagree
            rows_text = _bugs(_row(101))
        else:
            rows_text = live
        assert (
            _MOD.check_burndown_header_matches_rows(
                _tip_roadmap_retired(), rows_text
            )
            != []
        )


# ---------------------------------------------------------------------------
# The enumerated negative-conformance-fixture lists in CLAUDE.md and
# AGENTS.md, against the manifest that decides which fixtures are negative.
# Both files spell the set out in full and AGENTS.md also spells its size as
# an English word; nothing gated any of it, so a fixture added to the
# manifest simply never appeared in either list.
# ---------------------------------------------------------------------------


def _manifest(
    *negatives: str,
    positives: int = 2,
    compile_stage: tuple[str, ...] = (),
) -> list[dict[str, object]]:
    entries: list[dict[str, object]] = [
        {"file": f"ch01_positive_{i}.vera", "level": "verify"}
        for i in range(positives)
    ]
    entries += [
        {"file": f"{name}.vera", "level": "check", "expected_error": "E123"}
        for name in negatives
    ]
    # A compile-stage negative is still declared at level "check" — the
    # stage is where its diagnostic fires, not where its level sits.
    entries += [
        {
            "file": f"{name}.vera",
            "level": "check",
            "expected_error": "E621",
            "expected_error_stage": "compile",
        }
        for name in compile_stage
    ]
    return entries


def _fixture_doc(*names: str, word: str | None = None) -> str:
    listed = ", ".join(f"`{name}`" for name in names)
    count = f"the {word} " if word else "the "
    return (
        "Each positive program must pass its declared verification level;"
        f" {count}negative fixtures ({listed}) instead must *fail* with the"
        " E-code in their `expected_error` field.\n"
    )


class TestNegativeFixtureLists:
    def test_a_list_matching_the_manifest_is_clean(self) -> None:
        docs = {
            "CLAUDE.md": _fixture_doc("ch02_a_rejected", "ch08_b_rejected"),
            "AGENTS.md": _fixture_doc(
                "ch02_a_rejected", "ch08_b_rejected", word="two"
            ),
        }
        expected = _MOD.negative_fixture_names(
            _manifest("ch02_a_rejected", "ch08_b_rejected")
        )
        assert _MOD.check_negative_fixture_lists(docs, expected) == []

    def test_a_manifest_fixture_missing_from_the_list_is_reported(self) -> None:
        """The live drift: a negative fixture is added to the manifest and
        the two prose lists are not touched."""
        docs = {
            "CLAUDE.md": _fixture_doc("ch02_a_rejected"),
            "AGENTS.md": _fixture_doc("ch02_a_rejected", word="one"),
        }
        expected = _MOD.negative_fixture_names(
            _manifest("ch02_a_rejected", "ch08_new_rejected")
        )
        errors = _MOD.check_negative_fixture_lists(docs, expected)
        assert len(errors) == 3
        assert all("ch08_new_rejected" in e or "'one'" in e for e in errors)

    def test_a_stale_count_word_is_reported(self) -> None:
        """The names can be right while the word that counts them is not."""
        docs = {
            "AGENTS.md": _fixture_doc(
                "ch02_a_rejected", "ch08_b_rejected", word="one"
            )
        }
        expected = _MOD.negative_fixture_names(
            _manifest("ch02_a_rejected", "ch08_b_rejected")
        )
        errors = _MOD.check_negative_fixture_lists(docs, expected)
        assert len(errors) == 1
        assert "'one'" in errors[0] and "manifest has 2" in errors[0]

    def test_a_listed_fixture_the_manifest_does_not_mark_is_reported(
        self,
    ) -> None:
        """Drift runs both ways: a fixture that stops being negative — or
        is deleted — leaves a name behind."""
        docs = {
            "CLAUDE.md": _fixture_doc(
                "ch02_a_rejected", "ch09_gone", word="one"
            )
        }
        expected = _MOD.negative_fixture_names(_manifest("ch02_a_rejected"))
        errors = _MOD.check_negative_fixture_lists(docs, expected)
        assert len(errors) == 1 and "ch09_gone" in errors[0]

    def test_every_occurrence_is_checked_not_the_first(self) -> None:
        """AGENTS.md carries the list twice.  A gate reading only the
        first would let the second drift — the same one-of-two blindness
        one level down."""
        doc = _fixture_doc(
            "ch02_a_rejected", "ch08_b_rejected", word="two"
        ) + _fixture_doc("ch02_a_rejected")
        expected = _MOD.negative_fixture_names(
            _manifest("ch02_a_rejected", "ch08_b_rejected")
        )
        errors = _MOD.check_negative_fixture_lists({"AGENTS.md": doc}, expected)
        assert len(errors) == 1
        assert "list 2 of 2" in errors[0] and "ch08_b_rejected" in errors[0]

    def test_a_duplicate_name_is_reported(self) -> None:
        """A set written out by hand can name one fixture twice, which
        makes the list look longer than the set it describes."""
        docs = {
            "CLAUDE.md": _fixture_doc(
                "ch02_a_rejected", "ch02_a_rejected", word="one"
            )
        }
        expected = _MOD.negative_fixture_names(_manifest("ch02_a_rejected"))
        errors = _MOD.check_negative_fixture_lists(docs, expected)
        assert len(errors) == 1 and "twice" in errors[0]

    def test_a_reworded_sentence_is_an_error_not_a_skip(self) -> None:
        docs = {"CLAUDE.md": "The rejected programs are listed in the manifest.\n"}
        expected = _MOD.negative_fixture_names(_manifest("ch02_a_rejected"))
        errors = _MOD.check_negative_fixture_lists(docs, expected)
        assert len(errors) == 1 and "no longer gated" in errors[0]

    def test_dropping_the_count_word_everywhere_is_an_error(self) -> None:
        """The word is half the gate; rewording it away must not switch
        that half off silently."""
        docs = {
            "CLAUDE.md": _fixture_doc("ch02_a_rejected"),
            "AGENTS.md": _fixture_doc("ch02_a_rejected"),
        }
        expected = _MOD.negative_fixture_names(_manifest("ch02_a_rejected"))
        errors = _MOD.check_negative_fixture_lists(docs, expected)
        assert len(errors) == 1 and "no longer spelled out" in errors[0]

    def test_an_unparseable_count_word_is_an_error(self) -> None:
        docs = {"AGENTS.md": _fixture_doc("ch02_a_rejected", word="several")}
        expected = _MOD.negative_fixture_names(_manifest("ch02_a_rejected"))
        errors = _MOD.check_negative_fixture_lists(docs, expected)
        assert len(errors) == 1 and "several" in errors[0]

    @pytest.mark.parametrize(
        ("lead", "cue"),
        [
            pytest.param("the 3 ", "'3'", id="digits"),
            pytest.param("all four ", "'four'", id="different-determiner"),
            pytest.param("the forty three ", "'three'", id="unhyphenated"),
        ],
    )
    def test_a_count_the_pattern_did_not_expect_flags(
        self, lead: str, cue: str
    ) -> None:
        """A count in an unanticipated spelling must FLAG, not vanish.

        The slot was matched positionally as `the <word> `, so digits, a
        different determiner and an unhyphenated compound each left the
        count silently unchecked with only the global "no count anywhere"
        backstop as a net — and that backstop stops covering the moment a
        second word site exists (PR #1411 review).  Each of these three
        is stale against a two-fixture manifest, so a gate that reads the
        slot at all must say so.
        """
        listed = "`ch01_a_rejected`, `ch01_b_rejected`"
        doc = (
            f"Each positive program passes its level; {lead}negative"
            f" fixtures ({listed}) instead must *fail*.\n"
        )
        expected = _MOD.negative_fixture_names(
            _manifest("ch01_a_rejected", "ch01_b_rejected")
        )
        errors = _MOD.check_negative_fixture_lists({"D.md": doc}, expected)
        assert len(errors) == 1, errors
        assert cue in errors[0]
        assert "no longer spelled out" not in errors[0]

    def test_a_second_list_cannot_hide_a_stale_count_behind_the_first(
        self,
    ) -> None:
        """The global backstop only fires when EVERY site loses its word.
        With two sites, one carrying a good count and the other a count
        the pattern did not expect, the second went unchecked."""
        good = _fixture_doc("ch01_a_rejected", "ch01_b_rejected", word="two")
        stale = (
            "Later, all four negative fixtures"
            " (`ch01_a_rejected`, `ch01_b_rejected`) must *fail*.\n"
        )
        expected = _MOD.negative_fixture_names(
            _manifest("ch01_a_rejected", "ch01_b_rejected")
        )
        errors = _MOD.check_negative_fixture_lists(
            {"D.md": good + stale}, expected
        )
        assert len(errors) == 1 and "'four'" in errors[0]
        assert "list 2 of 2" in errors[0]

    def test_a_bare_determiner_is_not_read_as_a_count(self) -> None:
        """CLAUDE.md's list is introduced with no count at all, and the
        determiner in front of it must not be mistaken for one."""
        docs = {
            "AGENTS.md": _fixture_doc("ch01_a_rejected", word="one"),
            "CLAUDE.md": _fixture_doc("ch01_a_rejected"),
        }
        expected = _MOD.negative_fixture_names(_manifest("ch01_a_rejected"))
        assert _MOD.check_negative_fixture_lists(docs, expected) == []

    def test_the_word_parser_is_the_burndown_header_s(self) -> None:
        """One table for "how many", so the two spellings in the
        documentation cannot disagree about what a word means — a
        hyphenated compound parses here exactly as it does there."""
        docs = {
            "AGENTS.md": _fixture_doc(
                *(f"ch0{i % 9}_x{i}_rejected" for i in range(21)),
                word="twenty-one",
            )
        }
        expected = _MOD.negative_fixture_names(
            _manifest(*(f"ch0{i % 9}_x{i}_rejected" for i in range(21)))
        )
        assert _MOD.check_negative_fixture_lists(docs, expected) == []

    def test_the_manifest_reader_selects_on_expected_error(self) -> None:
        """Positives must not leak into the expected set — that would
        make the prose lists unsatisfiable rather than gated."""
        names = _MOD.negative_fixture_names(
            _manifest("ch02_a_rejected", positives=3)
        )
        assert names == ["ch02_a_rejected"]

    def test_the_reader_partitions_the_manifest_as_the_runner_does(
        self, tmp_path: Path
    ) -> None:
        """A DIFFERENTIAL against the runner, not a reading of its source.

        `check_conformance.py` selects a negative fixture on
        `entry.get("expected_error") is not None`.  A gate splitting the
        same manifest by TRUTHINESS would disagree with it on an empty
        code — describing a set of negative fixtures nothing else
        believes in, and quietly excusing that fixture from the prose
        lists while the runner still demanded it fail.

        Both sides are RUN on one manifest whose single entry carries
        `"expected_error": ""` over a program that checks CLEAN.  That
        makes the runner's two branches observable: down the negative
        branch it demands a failure and finds none, so it exits 1; down
        the positive branch the clean program passes its level and it
        exits 0.  Grepping the runner's source for the operator would
        leave it free to classify the entry the other way with this
        still green (PR #1411 review).
        """
        entry = {
            "id": "ch01_blank_code",
            "file": "ch01_blank_code.vera",
            "level": "check",
            "expected_error": "",
        }
        assert _MOD.negative_fixture_names([entry]) == ["ch01_blank_code"]

        conformance = tmp_path / "conformance"
        conformance.mkdir()
        # Checks CLEAN — that is what makes the two branches tell apart.
        (conformance / "ch01_blank_code.vera").write_text(
            "public fn answer(-> @Int)\n"
            "  requires(true)\n"
            "  ensures(@Int.result == 42)\n"
            "  effects(pure)\n"
            "{\n"
            "  42\n"
            "}\n",
            encoding="utf-8",
        )
        manifest = conformance / "manifest.json"
        manifest.write_text(json.dumps([entry]), encoding="utf-8")

        spec = importlib.util.spec_from_file_location(
            "check_conformance_probe", _ROOT / "scripts" / "check_conformance.py"
        )
        assert spec is not None and spec.loader is not None
        runner = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(runner)
        runner.CONFORMANCE_DIR = conformance
        runner.MANIFEST_PATH = manifest
        # 1 == the runner took the NEGATIVE branch and found no failure to
        # match; 0 would mean it ran the clean program's positive pipeline
        # instead, which is the disagreement this pins.
        assert runner.main() == 1

    def test_the_shipped_manifest_has_negative_fixtures(self) -> None:
        """The live manifest, so the gate cannot be checking an empty
        set: an expected set of nothing would make any prose list pass
        its membership half."""
        manifest = json.loads(
            (_ROOT / "tests/conformance/manifest.json").read_text(
                encoding="utf-8"
            )
        )
        names = _MOD.negative_fixture_names(manifest)
        assert len(names) > 20
        assert len(set(names)) == len(names)


def _level_prose(
    check_names: tuple[str, ...],
    negative_names: tuple[str, ...],
    *,
    check_word: str,
    negative_word: str,
    compile_names: tuple[str, ...] = (),
    compile_word: str = "Zero",
    negative_codes: dict[str, str] | None = None,
) -> str:
    def listed(names: tuple[str, ...]) -> str:
        return ", ".join(f"`{name}`" for name in names)

    def codes(names: tuple[str, ...], overrides: dict[str, str]) -> str:
        return ", ".join(overrides.get(n, "E123") for n in names)

    compile_codes = (
        ""
        if not compile_names
        else " beside `expected_error: "
        + codes(compile_names, {n: "E621" for n in compile_names})
        + "`"
    )
    compile_part = (
        f" {compile_word} more — {listed(compile_names)} — is a negative"
        f" at the `compile` stage rather than at `check`:{compile_codes}."
    )
    respective = (
        ""
        if not negative_names
        else " that assert a specific diagnostic ("
        + codes(negative_names, negative_codes or {})
        + " respectively)"
    )
    return (
        "Almost all programs are at the `run` level. "
        f"{check_word} programs ({listed(check_names)}) are at the `check`"
        f" level. {negative_word} of them — {listed(negative_names)} — are"
        f" **negative tests**{respective}."
        f"{compile_part}\n"
    )


class TestConformanceLevelProse:
    """TESTING.md is the THIRD document that enumerates one of these
    sets by hand, and it had drifted on the same fixture and by the same
    mechanism as the two CLAUDE.md/AGENTS.md lists.  Gating two of the
    three would have been this PR's own argument left one step short
    (PR #1411 review)."""

    def test_a_matching_pair_of_enumerations_is_clean(self) -> None:
        manifest = _manifest("ch02_a_rejected", "ch08_b_rejected", positives=3)
        text = _level_prose(
            ("ch02_a_rejected", "ch08_b_rejected"),
            ("ch02_a_rejected", "ch08_b_rejected"),
            check_word="Two",
            negative_word="Two",
        )
        assert _MOD.check_conformance_level_prose(text, manifest) == []

    def test_a_program_missing_from_the_level_list_is_reported(self) -> None:
        manifest = _manifest("ch02_a_rejected", "ch08_b_rejected", positives=3)
        text = _level_prose(
            ("ch02_a_rejected",),
            ("ch02_a_rejected", "ch08_b_rejected"),
            check_word="One",
            negative_word="Two",
        )
        errors = _MOD.check_conformance_level_prose(text, manifest)
        assert len(errors) == 2
        assert all("ch08_b_rejected" in e or "'One'" in e for e in errors)

    def test_a_program_missing_from_the_negative_subset_is_reported(
        self,
    ) -> None:
        """The two enumerations are checked independently: the level list
        can be right while the subset drawn from it is not."""
        manifest = _manifest("ch02_a_rejected", "ch08_b_rejected", positives=3)
        text = _level_prose(
            ("ch02_a_rejected", "ch08_b_rejected"),
            ("ch02_a_rejected",),
            check_word="Two",
            negative_word="One",
        )
        errors = _MOD.check_conformance_level_prose(text, manifest)
        assert len(errors) == 2
        assert all("negative test" in e for e in errors)

    def test_a_stale_level_count_word_is_reported(self) -> None:
        manifest = _manifest("ch02_a_rejected", "ch08_b_rejected", positives=3)
        text = _level_prose(
            ("ch02_a_rejected", "ch08_b_rejected"),
            ("ch02_a_rejected", "ch08_b_rejected"),
            check_word="Three",
            negative_word="Two",
        )
        errors = _MOD.check_conformance_level_prose(text, manifest)
        assert len(errors) == 1 and "'Three'" in errors[0]

    def test_a_positive_level_is_read_from_the_manifest_too(self) -> None:
        """The level is taken from the sentence, so a `verify` list is
        checked against the verify entries rather than the check ones."""
        manifest: list[dict[str, object]] = [
            {"file": "ch03_proved.vera", "level": "verify"},
            {"file": "ch01_ran.vera", "level": "run"},
        ]
        text = (
            "One programs (`ch03_proved`) are at the `verify` level."
            " Zero of them — `` — are **negative tests** that assert a"
            " diagnostic. Zero more — `` — is a negative at the `compile`"
            " stage.\n"
        )
        assert _MOD.check_conformance_level_prose(text, manifest) == []

    _COMPILE_SENTENCE = (
        " Zero more — `` — is a negative at the `compile` stage."
    )
    _NEGATIVE_SENTENCE = " Zero of them — `` — are **negative tests** that x."
    _LEVEL_SENTENCE = " Zero programs (``) are at the `check` level."

    @pytest.mark.parametrize(
        ("dropped", "cue"),
        [
            pytest.param("_LEVEL_SENTENCE", "per-level program lists",
                         id="level-sentence-reworded"),
            pytest.param("_NEGATIVE_SENTENCE", "check-stage negatives",
                         id="negative-sentence-reworded"),
            pytest.param("_COMPILE_SENTENCE", "compile-stage negatives",
                         id="compile-sentence-reworded"),
        ],
    )
    def test_a_reworded_sentence_is_an_error_not_a_skip(
        self, dropped: str, cue: str
    ) -> None:
        """Each of the three shapes is gated independently, so rewording
        any one of them must be an error rather than a silent skip."""
        text = "".join(
            getattr(self, name)
            for name in ("_LEVEL_SENTENCE", "_NEGATIVE_SENTENCE",
                         "_COMPILE_SENTENCE")
            if name != dropped
        )
        errors = _MOD.check_conformance_level_prose(text + "\n", [])
        assert len(errors) == 1 and cue in errors[0]

    def test_a_compile_stage_fixture_in_the_check_list_is_a_duplication(
        self,
    ) -> None:
        """The exact error this PR made and CodeRabbit caught: the
        compile-stage negative is introduced in its own sentence, so
        adding it to the check-stage list names one fixture twice and
        leaves the parallel E-code list one short."""
        manifest = _manifest(
            "ch02_a_rejected", compile_stage=("ch08_late_rejected",)
        )
        text = _level_prose(
            ("ch02_a_rejected", "ch08_late_rejected"),
            ("ch02_a_rejected", "ch08_late_rejected"),
            check_word="Two",
            negative_word="Two",
            compile_names=("ch08_late_rejected",),
            compile_word="One",
        )
        errors = _MOD.check_conformance_level_prose(text, manifest)
        # Three symptoms of the one duplication: the fixture is not a
        # check-stage negative, the count is one too high, and the
        # respective code the prose gives it is not its manifest code.
        assert len(errors) == 3
        assert any("ch08_late_rejected" in e and "does not hold" in e
                   for e in errors)
        assert any("'Two'" in e and "check-stage" in e for e in errors)
        assert any("position 2" in e and "E621" in e for e in errors)

    def test_the_two_stages_are_gated_as_separate_sets(self) -> None:
        """Split correctly, both sentences are clean — the compile-stage
        fixture belongs to its own sentence and to the `check` LEVEL."""
        manifest = _manifest(
            "ch02_a_rejected", compile_stage=("ch08_late_rejected",)
        )
        text = _level_prose(
            ("ch02_a_rejected", "ch08_late_rejected"),
            ("ch02_a_rejected",),
            check_word="Two",
            negative_word="One",
            compile_names=("ch08_late_rejected",),
            compile_word="One",
        )
        assert _MOD.check_conformance_level_prose(text, manifest) == []

    def test_a_missing_compile_stage_negative_is_reported(self) -> None:
        manifest = _manifest(
            "ch02_a_rejected", compile_stage=("ch08_late_rejected",)
        )
        text = _level_prose(
            ("ch02_a_rejected", "ch08_late_rejected"),
            ("ch02_a_rejected",),
            check_word="Two",
            negative_word="One",
            compile_names=(),
            compile_word="Zero",
        )
        errors = _MOD.check_conformance_level_prose(text, manifest)
        assert len(errors) == 2
        assert any("ch08_late_rejected" in e for e in errors)

    def test_a_stale_respective_code_is_reported(self) -> None:
        """"Respectively" is a positional claim, so the check is
        positional: a code that no longer matches its fixture's
        `expected_error` is caught at its position."""
        manifest = _manifest("ch02_a_rejected", "ch08_b_rejected")
        text = _level_prose(
            ("ch02_a_rejected", "ch08_b_rejected"),
            ("ch02_a_rejected", "ch08_b_rejected"),
            check_word="Two",
            negative_word="Two",
            negative_codes={"ch08_b_rejected": "E999"},
        )
        errors = _MOD.check_conformance_level_prose(text, manifest)
        assert len(errors) == 1
        assert "position 2" in errors[0]
        assert "ch08_b_rejected" in errors[0]
        assert "E123" in errors[0] and "E999" in errors[0]

    def test_a_missing_code_shifts_the_rest_and_is_reported(self) -> None:
        """The silent shape: a fixture appended to the names without a
        code slides every code after it onto the wrong fixture.  Counted
        rather than matched pairwise, because the count is what tells a
        reader the correspondence is broken at all."""
        manifest = _manifest("ch02_a_rejected", "ch08_b_rejected")
        text = _level_prose(
            ("ch02_a_rejected", "ch08_b_rejected"),
            ("ch02_a_rejected", "ch08_b_rejected"),
            check_word="Two",
            negative_word="Two",
        ).replace("diagnostic (E123, E123 ", "diagnostic (E123 ", 1)
        errors = _MOD.check_conformance_level_prose(text, manifest)
        assert len(errors) == 1
        assert "2 fixture(s)" in errors[0] and "1 diagnostic code" in errors[0]

    def test_a_removed_code_list_is_an_error_not_a_skip(self) -> None:
        manifest = _manifest("ch02_a_rejected")
        text = _level_prose(
            ("ch02_a_rejected",),
            ("ch02_a_rejected",),
            check_word="One",
            negative_word="One",
        ).replace(" that assert a specific diagnostic (E123 respectively)", "")
        errors = _MOD.check_conformance_level_prose(text, manifest)
        assert len(errors) == 1 and "no longer gated" in errors[0]

    def test_a_stale_compile_stage_code_is_reported(self) -> None:
        """The compile sentence carries its code inline rather than in a
        parenthetical, and is gated the same way."""
        manifest = _manifest(
            "ch02_a_rejected", compile_stage=("ch08_late_rejected",)
        )
        text = _level_prose(
            ("ch02_a_rejected", "ch08_late_rejected"),
            ("ch02_a_rejected",),
            check_word="Two",
            negative_word="One",
            compile_names=("ch08_late_rejected",),
            compile_word="One",
        ).replace("`expected_error: E621`", "`expected_error: E622`")
        errors = _MOD.check_conformance_level_prose(text, manifest)
        assert len(errors) == 1 and "E621" in errors[0] and "E622" in errors[0]

    def test_an_empty_list_needs_no_codes(self) -> None:
        """"Respectively" over no names is vacuous, so a stage with no
        fixtures must not be asked for a code list."""
        manifest = _manifest(positives=1, compile_stage=())
        text = _level_prose(
            (), (), check_word="Zero", negative_word="Zero"
        )
        assert _MOD.check_conformance_level_prose(text, manifest) == []

    def test_each_list_reads_its_own_codes(self) -> None:
        """The codes are read from a window after THIS list's names.

        Searching the whole document instead would have a second
        occurrence validated against the first one's parenthetical — its
        own stale code never looked at — which is the same
        one-of-two blindness the every-occurrence case pins one level up.
        """
        manifest = _manifest("ch01_a_rejected", "ch01_b_rejected")
        good = _level_prose(
            ("ch01_a_rejected", "ch01_b_rejected"),
            ("ch01_a_rejected", "ch01_b_rejected"),
            check_word="Two",
            negative_word="Two",
        )
        stale = _level_prose(
            ("ch01_a_rejected", "ch01_b_rejected"),
            ("ch01_a_rejected", "ch01_b_rejected"),
            check_word="Two",
            negative_word="Two",
            negative_codes={"ch01_b_rejected": "E999"},
        )
        errors = _MOD.check_conformance_level_prose(good + stale, manifest)
        assert len(errors) == 1
        assert "position 2" in errors[0] and "E999" in errors[0]

    def test_the_shipped_codes_match_the_manifest_in_order(self) -> None:
        """The live parenthetical, read positionally against the
        manifest — so the gate cannot be checking an empty list."""
        text = (_ROOT / "TESTING.md").read_text(encoding="utf-8")
        match = _MOD._NEGATIVE_PROSE.search(text)
        assert match is not None
        names = _MOD._FIXTURE_NAME.findall(match.group("names"))
        codes = _MOD._codes_after(text, match, _MOD._RESPECTIVE_CODES)
        assert codes is not None
        assert len(names) == len(codes) > 20

    @pytest.mark.parametrize(
        ("old", "new", "cue"),
        [
            pytest.param("Three programs (", "The programs (",
                         "per-level program list", id="level"),
            # No determiner fits this slot in English ("the of them"),
            # so the reachable shape here is the count simply gone.
            pytest.param("Two of them — ", "of them — ",
                         "check-stage negative-test subset", id="check-stage"),
            pytest.param("One more — ", "And more — ",
                         "compile-stage negative", id="compile-stage"),
        ],
    )
    def test_a_count_reworded_to_a_determiner_is_reported(
        self, old: str, new: str, cue: str
    ) -> None:
        """Each family of sentences carries its own count backstop.

        `_check_enumeration` reports nothing when the count slot holds
        only a determiner — correct for a list that never stated a size,
        and wrong as the only rule: rewording the number away would
        leave the names gated and the count silently ungated. Losing it
        in one family must not hide behind another still having one
        (PR #1411 review).
        """
        manifest = _manifest(
            "ch01_a_rejected", "ch01_b_rejected",
            compile_stage=("ch08_late_rejected",),
        )
        text = _level_prose(
            ("ch01_a_rejected", "ch01_b_rejected", "ch08_late_rejected"),
            ("ch01_a_rejected", "ch01_b_rejected"),
            check_word="Three",
            negative_word="Two",
            compile_names=("ch08_late_rejected",),
            compile_word="One",
        )
        assert old in text, old
        errors = _MOD.check_conformance_level_prose(
            text.replace(old, new, 1), manifest
        )
        assert len(errors) == 1, errors
        assert "no longer state a count" in errors[0] and cue in errors[0]

    def test_the_shipped_file_is_actually_read(self) -> None:
        """Both shapes must match the live TESTING.md, or the gate is
        silently checking nothing on the only file it reads."""
        text = (_ROOT / "TESTING.md").read_text(encoding="utf-8")
        assert _MOD._LEVEL_PROSE.search(text) is not None
        assert _MOD._NEGATIVE_PROSE.search(text) is not None
        levels = {m.group("level") for m in _MOD._LEVEL_PROSE.finditer(text)}
        assert {"check", "verify"} <= levels


class TestErrorCodesCount:
    """vera/README.md's `ERROR_CODES` figures, gated (#1330 review).

    Three numbers in one sentence and none was read by the oracle, so the
    registry could grow a code on any PR and the sentence would drift
    silently.
    """

    _SENTENCE = (
        "The `ERROR_CODES` dict in `errors.py` maps every code to a short "
        "description (160 entries — 158 `E` codes and 2 `W` warning "
        "codes)."
    )

    def _registry(self, e: int = 158, w: int = 2) -> dict[str, object]:
        codes: dict[str, object] = {f"E{n:03d}": "x" for n in range(e)}
        codes.update({f"W{n:03d}": "x" for n in range(w)})
        return codes

    def test_the_shipped_sentence_matches_the_live_registry(self) -> None:
        from vera.errors import ERROR_CODES

        text = (Path(__file__).parent.parent / "vera/README.md").read_text(
            encoding="utf-8"
        )
        assert _MOD.check_error_codes_count(text, ERROR_CODES) == []

    def test_a_stale_total_is_caught(self) -> None:
        errors = _MOD.check_error_codes_count(self._SENTENCE, self._registry(159, 2))
        assert [e for e in errors if "total" in e]

    def test_a_stale_e_count_is_caught(self) -> None:
        errors = _MOD.check_error_codes_count(
            self._SENTENCE.replace("158 `E`", "157 `E`"), self._registry()
        )
        assert [e for e in errors if "E-code count" in e]

    def test_a_stale_w_count_is_caught(self) -> None:
        """The `W` figure is a NUMBER in the sentence, gated like the other
        two.  It was prose ("the two `W` warning codes"), which made a third
        `W` code a parse failure — the gate saying it could not find the
        sentence rather than which number was wrong (#1345 added one)."""
        errors = _MOD.check_error_codes_count(self._SENTENCE, self._registry(158, 3))
        assert [e for e in errors if "W-code count" in e], errors

    def test_a_reworded_sentence_is_an_error_not_a_skip(self) -> None:
        text = "The ERROR_CODES dict has 160 entries."
        errors = _MOD.check_error_codes_count(text, self._registry())
        assert len(errors) == 1 and "could not find" in errors[0]


class TestFaqExampleCount:
    """FAQ.md's by-the-numbers example bullet (#1346 review).

    The page's conformance bullet was pinned first, then its test bullet
    after that one drifted through two releases.  The example bullet went
    stale the same way when the corpus grew to 43, so it is pinned too —
    the third instance of one lesson, and the reason the check errors on a
    MISSING pattern rather than skipping.
    """

    def _faq(self, n: str) -> str:
        return (
            "- A 14-chapter formal specification\n"
            "- 12,188 tests, including a 244-program conformance suite\n"
            f"- {n} working example programs\n"
            "- 164 built-in functions\n"
        )

    def test_matching_count_is_clean(self) -> None:
        assert _MOD.check_faq_example_count(self._faq("43"), 43) == []

    def test_stale_count_is_reported(self) -> None:
        errors = _MOD.check_faq_example_count(self._faq("42"), 43)
        assert len(errors) == 1
        assert "doc says 42" in errors[0] and "live is 43" in errors[0]

    def test_thousands_separator_is_parsed(self) -> None:
        assert _MOD.check_faq_example_count(self._faq("1,043"), 1043) == []

    def test_missing_line_is_an_error_not_a_skip(self) -> None:
        """Rewording the bullet must not silently disable the check."""
        text = "- A 14-chapter formal specification\n- 43 examples, reworded\n"
        errors = _MOD.check_faq_example_count(text, 43)
        assert len(errors) == 1
        assert "not found" in errors[0]

    def test_prose_decoy_before_the_bullet_is_ignored(self) -> None:
        """The BULLET is read, not the first matching phrase on the page.

        An unanchored search takes whichever occurrence comes first, so prose
        above the list validates instead of the bullet — and the check stays
        green while the bullet itself is stale.  Here the decoy carries the
        correct count and the bullet carries a wrong one: an unanchored
        implementation passes, an anchored one reports the bullet.
        """
        text = (
            "Vera ships 43 working example programs today, and the list "
            "below breaks the project down.\n"
            "\n"
            "- A 14-chapter formal specification\n"
            "- 42 working example programs\n"
        )
        errors = _MOD.check_faq_example_count(text, 43)
        assert len(errors) == 1, errors
        assert "doc says 42" in errors[0], errors

    def test_a_second_bullet_is_an_error(self) -> None:
        """Two bullets mean two answers; the check cannot pick one."""
        text = (
            "- 43 working example programs\n"
            "- 43 working example programs\n"
        )
        errors = _MOD.check_faq_example_count(text, 43)
        assert len(errors) == 1, errors
        assert "appears 2 times" in errors[0], errors

    def test_indented_or_inline_mention_is_not_the_bullet(self) -> None:
        """Only a top-level list item counts as the by-the-numbers bullet."""
        text = "Some prose about 43 working example programs in passing.\n"
        errors = _MOD.check_faq_example_count(text, 43)
        assert len(errors) == 1
        assert "not found" in errors[0]

    def test_an_indented_bullet_is_not_the_bullet(self) -> None:
        """A nested list item is a sub-point, not the headline figure.

        `re.MULTILINE`'s `^` anchors at the line start, so leading
        whitespace already disqualifies it — this pins that, because an
        unanchored search would happily read the indented count and report
        the page as consistent while the real bullet said something else.
        """
        text = (
            "- Project size:\n"
            "  - 43 working example programs\n"
        )
        errors = _MOD.check_faq_example_count(text, 43)
        assert len(errors) == 1, errors
        assert errors[0] == (
            "FAQ.md: example-count bullet"
            " ('- N working example programs') not found"
        ), errors

    def test_the_shipped_faq_is_consistent(self) -> None:
        """The real page, against the real corpus."""
        root = _SCRIPT.parent.parent
        faq = (root / "FAQ.md").read_text(encoding="utf-8")
        live = len(list((root / "examples").glob("*.vera")))
        assert _MOD.check_faq_example_count(faq, live) == []


# ---------------------------------------------------------------------------
# Cross-checkout import isolation (plan-file S13): a gate's `from vera...`
# imports must resolve against the SAME tree its own `root` (derived from
# `__file__`) points at — never a stale PYTHONPATH entry (or, in the real
# failure mode, a venv's `__editable__.veralang-*.pth` finder pinned to
# whatever checkout `pip install -e` last ran in) pointing at a DIFFERENT
# checkout.  That finder — and a stale PYTHONPATH entry alike — only
# resolves `vera` when nothing earlier on `sys.path` already has; a plain
# `sys.path.insert(0, root)` wins over either, which is the fix
# `check_doc_counts.py`'s `main()` now applies before its own `from
# vera...` imports run.  Distinct from the pytest-rootdir trap TESTING.md's
# "Running against ANOTHER checkout" section documents (a different
# mechanism — pytest's own rootdir detection — with a different remedy:
# relocate the test file into the target tree, not a sys.path insertion).
# ---------------------------------------------------------------------------


def _make_fake_checkout(root: Path, marker: str) -> None:
    (root / "vera").mkdir(parents=True)
    (root / "vera" / "__init__.py").write_text(
        f'MARKER = "{marker}"\n', encoding="utf-8")
    (root / "scripts").mkdir()


class TestCrossCheckoutImportIsolation:
    def test_root_insertion_wins_over_a_stale_pythonpath(
        self, tmp_path: Path,
    ) -> None:
        """The FIX: a script that inserts its own `__file__`-derived root
        at sys.path[0] before importing `vera` resolves ITS OWN
        checkout's package even when PYTHONPATH points at a different
        one — the same pattern `check_doc_counts.py`'s `main()` uses."""
        _make_fake_checkout(tmp_path / "checkout_a", "A")
        _make_fake_checkout(tmp_path / "checkout_b", "B")

        probe = tmp_path / "checkout_a" / "scripts" / "probe.py"
        probe.write_text(
            "import sys\n"
            "from pathlib import Path\n"
            "root = Path(__file__).resolve().parent.parent\n"
            "sys.path.insert(0, str(root))\n"
            "import vera\n"
            "print(vera.MARKER)\n",
            encoding="utf-8",
        )

        env = dict(os.environ)
        env["PYTHONPATH"] = str(tmp_path / "checkout_b")
        result = subprocess.run(
            [sys.executable, str(probe)],
            capture_output=True, text=True, encoding="utf-8",
            env=env, check=False,
        )
        assert result.stdout.strip() == "A", (
            f"expected checkout_a's vera (MARKER='A'), got "
            f"{result.stdout!r} (stderr: {result.stderr})"
        )

    def test_without_the_fix_a_stale_pythonpath_wins(
        self, tmp_path: Path,
    ) -> None:
        """The NEGATIVE CONTROL: without the root-insertion line, the
        identical two-checkout setup resolves the WRONG package —
        proving this is a real trap the fix actually closes, not a
        test that would pass regardless of the fix's presence."""
        _make_fake_checkout(tmp_path / "checkout_a", "A")
        _make_fake_checkout(tmp_path / "checkout_b", "B")

        probe = tmp_path / "checkout_a" / "scripts" / "probe_unfixed.py"
        probe.write_text("import vera\nprint(vera.MARKER)\n", encoding="utf-8")

        env = dict(os.environ)
        env["PYTHONPATH"] = str(tmp_path / "checkout_b")
        result = subprocess.run(
            [sys.executable, str(probe)],
            capture_output=True, text=True, encoding="utf-8",
            env=env, check=False,
        )
        assert result.stdout.strip() == "B", (
            "expected the unfixed probe to resolve checkout_b's vera via "
            f"PYTHONPATH (the trap this class exists to close), got "
            f"{result.stdout!r} (stderr: {result.stderr})"
        )

    def test_check_doc_counts_main_inserts_root_before_vera_imports(self) -> None:
        """Structural pin on the real fix: `main()` must insert `root`
        at sys.path BEFORE any `from vera` import STATEMENT runs, not
        after — inserting it after the first one already executed
        would be a no-op for that import.  Matches an actual `from
        vera.x import y` statement (line-anchored, optional leading
        whitespace) rather than a bare substring search, which would
        also match this very requirement described in a comment."""
        source = _SCRIPT.read_text(encoding="utf-8")
        main_start = source.index("\ndef main() -> int:")
        main_body = source[main_start:]
        insert_idx = main_body.index("sys.path.insert(0, str(root))")
        import_match = re.search(r"^[ \t]*from vera\.\w+ import\b", main_body, re.M)
        assert import_match is not None, (
            "main() no longer imports anything from vera — this test's "
            "premise (there is a from-vera import to race against) no "
            "longer holds; re-check whether the ordering still matters"
        )
        assert insert_idx < import_match.start(), (
            "sys.path.insert(0, str(root)) must appear before the first "
            "`from vera.<x> import ...` statement in main() — found it "
            "after instead"
        )


class TestEnglishNumberWordRejectsInvalidCompounds:
    """A hyphenated compound's tail is a units word and nothing else:
    ``twenty-ten`` and ``thirty-nineteen`` are not English numbers, and
    accepting them would let a malformed burndown header pass whenever the
    arithmetic happened to equal the live row count."""

    def test_valid_compounds_still_parse(self) -> None:
        mod = _MOD
        assert mod._english_number_word_to_int("twenty-one") == 21
        assert mod._english_number_word_to_int("Ninety-nine") == 99

    def test_invalid_compounds_are_not_numbers(self) -> None:
        mod = _MOD
        for word in ("twenty-zero", "twenty-ten", "thirty-nineteen", "forty-twenty"):
            assert mod._english_number_word_to_int(word) is None, word
