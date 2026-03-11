"""Tests for docs/index.html code samples — parse, check, and verify.

Mirrors scripts/check_html_examples.py but integrates with pytest for
the regular test suite. Every Vera code block in docs/index.html must
pass the full pipeline: parse → type-check → verify.
"""

from __future__ import annotations

import html as html_mod
import re
import subprocess
import sys
import tempfile
from pathlib import Path

from vera.parser import parse

ROOT = Path(__file__).parent.parent
INDEX_HTML = ROOT / "docs" / "index.html"

# -- Allowlist: HTML blocks that are intentionally unparseable. ---------------
# Must stay in sync with scripts/check_html_examples.py.
# Each key is the 1-based line number of the <pre> tag.
ALLOWLIST: dict[int, str] = {}

# -- Heuristic: block must START with a top-level Vera declaration. -----------
_TOP_LEVEL_RE = re.compile(
    r"\A\s*(?:--.*\n\s*)*"           # optional leading comments
    r"(?:public\s+|private\s+)?"     # optional visibility
    r"(?:fn\s|data\s|effect\s|type\s|module\s|import\s)",
)


def _extract_vera_blocks(path: Path) -> list[tuple[int, str]]:
    """Extract Vera code blocks from HTML <pre> elements.

    Strips HTML tags and decodes entities to recover plain Vera source.
    Only returns blocks that start with a top-level Vera declaration
    (skips error diagnostics, shell transcripts, install steps).

    Returns list of (line_number, content) tuples.
    """
    lines = path.read_text(encoding="utf-8").splitlines()
    blocks: list[tuple[int, str]] = []

    i = 0
    while i < len(lines):
        if "<pre>" in lines[i] or "<pre " in lines[i]:
            start_line = i + 1  # 1-based
            pre_lines: list[str] = []
            while i < len(lines):
                pre_lines.append(lines[i])
                if "</pre>" in lines[i]:
                    break
                i += 1
            raw_html = "\n".join(pre_lines)

            m = re.search(r"<pre[^>]*>(.*?)</pre>", raw_html, re.DOTALL)
            if m:
                content = m.group(1)
                content = re.sub(r"<[^>]+>", "", content)
                content = html_mod.unescape(content)
                content = content.strip()
                # Only include blocks that look like Vera source
                if _TOP_LEVEL_RE.search(content):
                    blocks.append((start_line, content))
        i += 1

    return blocks


class TestHtmlCodeSamples:
    """Every Vera code block in docs/index.html should pass the full pipeline."""

    def test_all_vera_blocks_parse(self) -> None:
        """Extract all Vera blocks and verify each one parses."""
        blocks = _extract_vera_blocks(INDEX_HTML)
        assert len(blocks) > 0, "No Vera blocks found in docs/index.html"

        failures: list[tuple[int, str]] = []
        for line_no, content in blocks:
            if line_no in ALLOWLIST:
                continue
            try:
                parse(content, file="<html>")
            except Exception as exc:
                failures.append((line_no, str(exc).split("\n")[0][:200]))

        if failures:
            msg_parts = [f"{len(failures)} HTML code block(s) failed to parse:"]
            for line_no, error in failures:
                msg_parts.append(f"  line {line_no}: {error}")
            raise AssertionError("\n".join(msg_parts))

    def test_all_vera_blocks_check(self) -> None:
        """Verify each Vera block type-checks cleanly."""
        blocks = _extract_vera_blocks(INDEX_HTML)
        assert len(blocks) > 0, "No Vera blocks found in docs/index.html"

        failures: list[tuple[int, str]] = []
        for line_no, content in blocks:
            if line_no in ALLOWLIST:
                continue
            with tempfile.NamedTemporaryFile(
                mode="w", suffix=".vera", dir=str(ROOT), delete=True
            ) as f:
                f.write(content)
                f.flush()
                result = subprocess.run(
                    [sys.executable, "-m", "vera.cli", "check", f.name],
                    capture_output=True,
                    text=True,
                    cwd=str(ROOT),
                    timeout=30,
                )
                if "OK:" not in result.stdout:
                    err = result.stderr.strip() or result.stdout.strip()
                    failures.append((line_no, err.split("\n")[0][:200]))

        if failures:
            msg_parts = [f"{len(failures)} HTML code block(s) failed type-check:"]
            for line_no, error in failures:
                msg_parts.append(f"  line {line_no}: {error}")
            raise AssertionError("\n".join(msg_parts))

    def test_all_vera_blocks_verify(self) -> None:
        """Verify each Vera block's contracts pass the verifier."""
        blocks = _extract_vera_blocks(INDEX_HTML)
        assert len(blocks) > 0, "No Vera blocks found in docs/index.html"

        failures: list[tuple[int, str]] = []
        for line_no, content in blocks:
            if line_no in ALLOWLIST:
                continue
            with tempfile.NamedTemporaryFile(
                mode="w", suffix=".vera", dir=str(ROOT), delete=True
            ) as f:
                f.write(content)
                f.flush()
                result = subprocess.run(
                    [sys.executable, "-m", "vera.cli", "verify", f.name],
                    capture_output=True,
                    text=True,
                    cwd=str(ROOT),
                    timeout=60,
                )
                if "OK:" not in result.stdout:
                    err = result.stderr.strip() or result.stdout.strip()
                    failures.append((line_no, err.split("\n")[0][:200]))

        if failures:
            msg_parts = [f"{len(failures)} HTML code block(s) failed verification:"]
            for line_no, error in failures:
                msg_parts.append(f"  line {line_no}: {error}")
            raise AssertionError("\n".join(msg_parts))

    def test_vera_block_count(self) -> None:
        """docs/index.html should have the expected number of Vera code blocks."""
        blocks = _extract_vera_blocks(INDEX_HTML)
        # Currently: safe_divide, fizzbuzz
        assert len(blocks) == 2, (
            f"Expected 2 Vera blocks in docs/index.html, found {len(blocks)}"
        )
