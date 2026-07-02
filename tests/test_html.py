"""Tests for docs/index.html code samples — parse, check, and verify.

Mirrors scripts/check_html_examples.py but integrates with pytest for
the regular test suite. Every Vera code block in docs/index.html must
pass the full pipeline: parse → type-check → verify.

A block that intentionally fails a stage carries an inline
`<!-- vera:skip-<stage> ... -->` annotation on the line before its <pre>
tag (#538; see scripts/doc_annotations.py).  Annotated blocks are still
run through the stage: one that passes it is a stale annotation and fails
the test.  All current blocks pass all stages — none is annotated today.
"""

from __future__ import annotations

import importlib.util
import re
import subprocess
import sys
import tempfile
from pathlib import Path

from vera.parser import parse

ROOT = Path(__file__).parent.parent
INDEX_HTML = ROOT / "docs" / "index.html"

# scripts/ is not a package: load the shared annotation module by file path
# (same pattern as tests/test_build_site.py).
_DOC_ANNOTATIONS = ROOT / "scripts" / "doc_annotations.py"
_spec = importlib.util.spec_from_file_location("doc_annotations", _DOC_ANNOTATIONS)
assert _spec is not None and _spec.loader is not None
doc_annotations = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(doc_annotations)

# -- Heuristic: block must START with a top-level Vera declaration. -----------
_TOP_LEVEL_RE = re.compile(
    r"\A\s*(?:--.*\n\s*)*"           # optional leading comments
    r"(?:public\s+|private\s+)?"     # optional visibility
    r"(?:fn\s|data\s|effect\s|type\s|module\s|import\s)",
)


def _extract_vera_blocks() -> list:
    """Extract Vera code blocks (with annotations) from docs/index.html.

    Only returns blocks that start with a top-level Vera declaration
    (skips error diagnostics, shell transcripts, install steps).
    """
    blocks, problems = doc_annotations.scan_html(INDEX_HTML)
    assert problems == [], f"annotation problems in docs/index.html: {problems}"
    return [b for b in blocks if _TOP_LEVEL_RE.search(b.content)]


def _skip_annotation(block, stage: str):
    return next((a for a in block.annotations if a.stage == stage), None)


def _assert_stage(
    blocks: list,
    stage: str,
    runner,
    label: str,
) -> None:
    """Unannotated blocks must pass *stage*; skip-annotated blocks must fail
    it (a passing annotated block is a stale annotation)."""
    failures: list[tuple[int, str]] = []
    for block in blocks:
        annotation = _skip_annotation(block, stage)
        error = runner(block.content)
        if annotation is None and error is not None:
            failures.append((block.line, error))
        elif annotation is not None and error is None:
            failures.append(
                (block.line, f"STALE vera:skip-{stage} annotation — block passes")
            )

    if failures:
        msg_parts = [f"{len(failures)} HTML code block(s) failed {label}:"]
        for line_no, error in failures:
            msg_parts.append(f"  line {line_no}: {error}")
        raise AssertionError("\n".join(msg_parts))


def _try_parse(content: str) -> str | None:
    try:
        parse(content, file="<html>")
        return None
    except Exception as exc:
        return str(exc).split("\n")[0][:200]


def _run_cli(content: str, command: str, timeout: int) -> str | None:
    # `delete=False` + manual unlink: on Windows you can't open a file
    # twice while one handle is still held, so the `with`-block's open
    # handle blocks the subprocess from reading it.  Closing the handle
    # before the subprocess runs (and unlinking after) is portable; on
    # Unix `delete=True` worked because Unix allows concurrent handles.
    f = tempfile.NamedTemporaryFile(
        mode="w",
        suffix=".vera",
        delete=False,
        encoding="utf-8",
    )
    try:
        f.write(content)
        f.close()
        result = subprocess.run(
            [sys.executable, "-m", "vera.cli", command, f.name],
            capture_output=True,
            text=True,
            encoding="utf-8",
            cwd=str(ROOT),
            timeout=timeout,
        )
        if "OK:" in result.stdout:
            return None
        err = result.stderr.strip() or result.stdout.strip()
        return err.split("\n")[0][:200]
    finally:
        Path(f.name).unlink(missing_ok=True)


class TestHtmlCodeSamples:
    """Every Vera code block in docs/index.html should pass the full pipeline."""

    def test_all_vera_blocks_parse(self) -> None:
        """Extract all Vera blocks and verify each one parses."""
        blocks = _extract_vera_blocks()
        assert len(blocks) > 0, "No Vera blocks found in docs/index.html"
        _assert_stage(blocks, "parse", _try_parse, "parse")

    def test_all_vera_blocks_check(self) -> None:
        """Verify each Vera block type-checks cleanly."""
        blocks = [
            b for b in _extract_vera_blocks()
            if _skip_annotation(b, "parse") is None
        ]
        assert len(blocks) > 0, "No Vera blocks found in docs/index.html"
        _assert_stage(
            blocks, "check", lambda c: _run_cli(c, "check", 30), "type-check"
        )

    def test_all_vera_blocks_verify(self) -> None:
        """Verify each Vera block's contracts pass the verifier."""
        blocks = [
            b for b in _extract_vera_blocks()
            if _skip_annotation(b, "parse") is None
            and _skip_annotation(b, "check") is None
        ]
        assert len(blocks) > 0, "No Vera blocks found in docs/index.html"
        _assert_stage(
            blocks, "verify", lambda c: _run_cli(c, "verify", 60), "verification"
        )

    def test_vera_block_count(self) -> None:
        """docs/index.html should have the expected number of Vera code blocks."""
        blocks = _extract_vera_blocks()
        # Currently: safe_divide, fizzbuzz, classify_sentiment, research_topic
        # (Count reduced from 5 to 4 in the redesign — safe_classify was folded
        # into the classify_sentiment sample.)
        assert len(blocks) == 4, (
            f"Expected 4 Vera blocks in docs/index.html, found {len(blocks)}"
        )
