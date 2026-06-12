"""Tests for scripts/check_limitations_sync.py section extraction.

Covers ``extract_section_issues``, added for the v0.0.171 rework when
SKILL.md and LSP_SERVER.md joined the netted tiers: bounded at the next
heading, table-rows-only, and ``None`` (not empty) for a missing heading
so renamed sections fail loudly.
"""

from __future__ import annotations

import importlib.util
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
