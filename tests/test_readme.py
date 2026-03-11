"""Tests for README.md code samples — ensures all Vera blocks parse.

Mirrors scripts/check_readme_examples.py but integrates with pytest for
the regular test suite. Every ```vera code block in README.md must parse
successfully (or be in the allowlist).
"""

from __future__ import annotations

import re
from pathlib import Path

from vera.parser import parse

README = Path(__file__).parent.parent / "README.md"

# -- Allowlist: README blocks that are intentionally unparseable. ----------
# Must stay in sync with scripts/check_readme_examples.py.
# Each key is the 1-based line number of the opening ```vera fence.
ALLOWLIST: dict[int, str] = {
    # "Where this is going" — depends on #57 (Http), #61 (Inference), #147 (Markdown)
    414: "Vision example uses MdBlock, Http, Inference (issues #57, #61, #147)",
}


def _extract_vera_blocks(path: Path) -> list[tuple[int, str]]:
    """Extract all ```vera blocks from a Markdown file.

    Returns list of (line_number, content) tuples.
    """
    lines = path.read_text(encoding="utf-8").splitlines()
    blocks: list[tuple[int, str]] = []
    i = 0
    while i < len(lines):
        m = re.match(r"^```vera$", lines[i])
        if m:
            start_line = i + 1  # 1-based
            content_lines: list[str] = []
            i += 1
            while i < len(lines) and not re.match(r"^```$", lines[i]):
                content_lines.append(lines[i])
                i += 1
            blocks.append((start_line, "\n".join(content_lines)))
        i += 1
    return blocks


class TestReadmeCodeSamples:
    """Every ```vera code block in README.md should parse."""

    def test_all_vera_blocks_parse(self) -> None:
        """Extract all vera blocks and verify each one parses."""
        blocks = _extract_vera_blocks(README)
        assert len(blocks) > 0, "No vera blocks found in README.md"

        failures: list[tuple[int, str]] = []
        for line_no, content in blocks:
            if line_no in ALLOWLIST:
                continue
            try:
                parse(content, file="<readme>")
            except Exception as exc:
                failures.append((line_no, str(exc).split("\n")[0][:200]))

        if failures:
            msg_parts = [f"{len(failures)} README code block(s) failed to parse:"]
            for line_no, error in failures:
                msg_parts.append(f"  line {line_no}: {error}")
            raise AssertionError("\n".join(msg_parts))

    def test_vera_block_count(self) -> None:
        """README should have the expected number of Vera code blocks."""
        blocks = _extract_vera_blocks(README)
        # Currently: hello_world, file_io, absolute_value, safe_divide,
        # increment (State), double, research_topic (vision, allowlisted)
        assert len(blocks) == 7, (
            f"Expected 7 Vera blocks in README.md, found {len(blocks)}"
        )
