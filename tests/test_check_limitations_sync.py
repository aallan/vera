"""Tests for scripts/check_limitations_sync.py section extraction.

Covers ``extract_section_issues``, added in the June 2026 rework when
SKILL.md and LSP_SERVER.md joined the netted tiers: bounded at the next
heading, table-rows-only, and ``None`` (not empty) for a missing heading
so renamed sections fail loudly.
"""

from __future__ import annotations

import importlib.util
import os
import subprocess
import sys
from pathlib import Path
from typing import Any

_SCRIPT = (
    Path(__file__).parent.parent / "scripts" / "check_limitations_sync.py"
)


def _load() -> Any:
    spec = importlib.util.spec_from_file_location(
        "check_limitations_sync", _SCRIPT
    )
    assert spec is not None
    module = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    spec.loader.exec_module(module)
    return module


_MOD = _load()


def _link(n: int) -> str:
    return f"[#{n}](https://github.com/aallan/vera/issues/{n})"


class TestExtractSectionIssues:
    def test_extracts_table_links(self) -> None:
        text = (
            "## Known Limitations\n\n"
            "| Limitation | Issue |\n"
            "|-----------|-------|\n"
            f"| First gap | {_link(11)} |\n"
            f"| Second gap | {_link(22)} |\n"
        )
        assert _MOD.extract_section_issues(text, "Known Limitations") == {
            11,
            22,
        }

    def test_prose_links_ignored(self) -> None:
        text = (
            "## Known Bugs and Workarounds\n\n"
            "No known bugs.\n\n"
            f"Narrative prose mentioning {_link(517)} is not inventory.\n"
        )
        assert (
            _MOD.extract_section_issues(text, "Known Bugs and Workarounds")
            == set()
        )

    def test_bounded_at_next_heading(self) -> None:
        text = (
            "## Current limitations\n\n"
            f"| Only this | {_link(7)} |\n\n"
            "## Reference\n\n"
            f"| Not this | {_link(99)} |\n"
        )
        assert _MOD.extract_section_issues(text, "Current limitations") == {7}

    def test_missing_heading_returns_none(self) -> None:
        assert _MOD.extract_section_issues("# Other doc\n", "Nope") is None

    def test_subheading_does_not_match(self) -> None:
        text = f"### Known Limitations\n\n| Row | {_link(5)} |\n"
        assert _MOD.extract_section_issues(text, "Known Limitations") is None


class TestCheckStatesFailsLoud:
    """--check-states must fail loudly when issue states cannot be determined
    (gh CLI missing, auth failure, rate limit) — a state check that silently
    degrades to a no-op would leave the scheduled workflow (#852) green while
    checking nothing (PR #960 review)."""

    def test_unknown_state_is_an_error(self, tmp_path: Path) -> None:
        env = os.environ.copy()
        env["PATH"] = str(tmp_path)  # no `gh` resolvable -> every state UNKNOWN
        # The child script prints via the platform default encoding (cp1252 on
        # Windows); pin its stdio to UTF-8 so the utf-8 pipe decode is sound.
        env["PYTHONIOENCODING"] = "utf-8"
        result = subprocess.run(
            [sys.executable, str(_SCRIPT), "--check-states"],
            capture_output=True,
            text=True,
            encoding="utf-8",
            env=env,
            timeout=120,
            check=False,
        )
        assert result.returncode == 1
        # Windows: a capture pipe read by a crippled-PATH subprocess can
        # surface as None rather than "" — guard both streams.
        out = (result.stdout or "") + (result.stderr or "")
        assert "could not be determined" in out


class TestIssueColumnScoping:
    """#1337 — the state scan reads a row's Issue column, not its prose.

    ``--check-states`` asks an INVENTORY question: does this table still
    claim the issue is open?  A row's prose legitimately cites CLOSED
    issues for context ("the general disease behind #1315", "fixed in
    #1305"), and reading those as live claims failed the nightly on
    eight such citations while every row's own Issue column was correct.
    The presence checks keep the wide reading, so both widths are tested
    here — a fix that narrowed BOTH would silently drop cross-reference
    coverage from the default mode.
    """

    OPEN_N = 9001
    CLOSED_N = 9002

    def _table(self, prose_cite: bool) -> str:
        prose = f" See also {_link(self.CLOSED_N)}." if prose_cite else ""
        return (
            "## Bugs\n\n"
            "| Bug | Issue |\n"
            "|-----|-------|\n"
            f"| A defect.{prose} | {_link(self.OPEN_N)} |\n"
        )

    def test_issue_column_is_collected(self) -> None:
        """(a) A row whose Issue column cites an issue reports that issue."""
        got = _MOD.extract_limitation_table_issues(
            self._table(prose_cite=False), "## Bugs", issue_column_only=True
        )
        assert got == {self.OPEN_N}

    def test_a_closed_issue_in_the_issue_column_still_counts(self) -> None:
        """(b) The check's PURPOSE survives: an Issue column is never exempt.

        Scoping to the column must not become a way for a stale row to
        escape the state check — only prose loses its vote.
        """
        table = (
            "## Bugs\n\n"
            "| Bug | Issue |\n"
            "|-----|-------|\n"
            f"| A stale row. | {_link(self.CLOSED_N)} |\n"
        )
        got = _MOD.extract_limitation_table_issues(
            table, "## Bugs", issue_column_only=True
        )
        assert self.CLOSED_N in got

    def test_prose_citation_is_not_collected(self) -> None:
        """(c) The #1337 regression: a prose cite does not claim openness."""
        got = _MOD.extract_limitation_table_issues(
            self._table(prose_cite=True), "## Bugs", issue_column_only=True
        )
        assert got == {self.OPEN_N}
        assert self.CLOSED_N not in got

    def test_wide_form_still_sees_prose(self) -> None:
        """(d) Default mode is unchanged — it still counts cross-references."""
        got = _MOD.extract_limitation_table_issues(
            self._table(prose_cite=True), "## Bugs"
        )
        assert got == {self.OPEN_N, self.CLOSED_N}

    def test_section_extractor_scopes_too(self) -> None:
        """``extract_section_issues`` carries the same two widths."""
        text = (
            "## Known Limitations\n\n"
            "| Limitation | Issue |\n"
            "|------------|-------|\n"
            f"| Blocked by {_link(self.CLOSED_N)}. | {_link(self.OPEN_N)} |\n"
        )
        narrow = _MOD.extract_section_issues(
            text, "Known Limitations", issue_column_only=True
        )
        wide = _MOD.extract_section_issues(text, "Known Limitations")
        assert narrow == {self.OPEN_N}
        assert wide == {self.OPEN_N, self.CLOSED_N}

    def test_real_known_issues_prose_cites_are_excluded(self) -> None:
        """The live citations that failed the nightly, pinned.

        These are references to issues closed in v0.1.12 that appear ONLY
        in row prose.  The narrow scan must not see them; the wide scan
        must, so the pin fails if the scoping is applied to both.

        The set tracks the live document: #1294 dropped out when #1301's
        row was removed, that row's "Successor to #1294" having been its
        last prose citation anywhere in the file.

        #1285 was one of the eight and is no longer among them: its only
        prose citation lived in the #1298 Bugs row, which left the table
        when #1298 was fixed.  A citation is pinned here for the SCOPING
        behaviour it exercises, so one whose host row is gone is dropped
        rather than kept as a reference to text that no longer exists.

        The set tracks the FILE, which is the fixture: a row retired by a
        fix takes its citations with it.  ``#1309`` left when the three
        rows that cited it — the branch-order siblings #1316, #1321 and
        #1331 — were closed by the one resolution spine, and ``#1277`` and
        ``#1305`` left with those same rows and the #1312 row beside them.
        Five citations still carry the property,
        which is what this pins; the scoping itself is pinned
        independently on synthetic tables above, so the file's contents
        cannot make the SCAN untested.
        """
        text = (
            _SCRIPT.parent.parent / "KNOWN_ISSUES.md"
        ).read_text(encoding="utf-8")
        prose_only = {1268, 1277, 1281, 1304, 1305}
        narrow: set[int] = set()
        wide: set[int] = set()
        for header in ("## Limitations", "## Bugs"):
            narrow |= _MOD.extract_limitation_table_issues(
                text, header, issue_column_only=True
            )
            wide |= _MOD.extract_limitation_table_issues(text, header)
        assert not (narrow & prose_only), sorted(narrow & prose_only)
        assert prose_only <= wide, sorted(prose_only - wide)

    def test_done_and_open_extractor_scopes_too(self) -> None:
        """`extract_done_and_open` carries the same two widths (#1337).

        `vera/README.md`'s Current Limitations table is the third source
        the state scan reads, and it has its own extractor.  A fix that
        threaded the flag through the other two and forgot this one would
        leave the same prose-as-inventory defect live for that file, so
        both widths are pinned here as well.
        """
        text = (
            "## Current Limitations\n\n"
            "| Limitation | Issue |\n"
            "|------------|-------|\n"
            f"| Superseded by {_link(self.CLOSED_N)}. | {_link(self.OPEN_N)} |\n"
        )
        narrow_open, narrow_done = _MOD.extract_done_and_open(
            text, issue_column_only=True
        )
        wide_open, wide_done = _MOD.extract_done_and_open(text)
        assert narrow_open == {self.OPEN_N}
        assert self.CLOSED_N not in narrow_open
        assert wide_open == {self.OPEN_N, self.CLOSED_N}
        assert narrow_done == set() and wide_done == set()
