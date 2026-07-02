"""Tests for README.md code samples — ensures all Vera blocks parse.

Mirrors scripts/check_readme_examples.py but integrates with pytest for
the regular test suite. Every ```vera code block in README.md must parse
successfully, or carry an inline `<!-- vera:skip-parse ... -->` annotation
on the line before its fence (#538; see scripts/doc_annotations.py).
Annotated blocks are still parsed: one that parses fine is a stale
annotation and fails the test.
"""

from __future__ import annotations

import importlib.util
from pathlib import Path

from vera.parser import parse

README = Path(__file__).parent.parent / "README.md"

# scripts/ is not a package: load the shared annotation module by file path
# (same pattern as tests/test_build_site.py).
_DOC_ANNOTATIONS = Path(__file__).parent.parent / "scripts" / "doc_annotations.py"
_spec = importlib.util.spec_from_file_location("doc_annotations", _DOC_ANNOTATIONS)
assert _spec is not None and _spec.loader is not None
doc_annotations = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(doc_annotations)


def _try_parse(content: str) -> str | None:
    try:
        parse(content, file="<readme>")
        return None
    except Exception as exc:
        return str(exc).split("\n")[0][:200]


def _vera_blocks() -> list:
    blocks, problems = doc_annotations.scan_markdown(README)
    assert problems == [], f"annotation problems in README.md: {problems}"
    return [b for b in blocks if b.lang.lower() == "vera"]


class TestReadmeCodeSamples:
    """Every ```vera code block in README.md should parse."""

    def test_all_vera_blocks_parse(self) -> None:
        """Extract all vera blocks and verify each one parses (or is
        honestly annotated — a stale annotation fails too)."""
        blocks = _vera_blocks()
        assert len(blocks) > 0, "No vera blocks found in README.md"

        failures: list[tuple[int, str]] = []
        for block in blocks:
            outcome = doc_annotations.evaluate_block(
                block, [("parse", _try_parse)]
            )[-1]
            if outcome.status == "failed":
                failures.append((block.line, outcome.error or ""))
            elif outcome.status == "stale":
                failures.append(
                    (block.line, "STALE vera:skip-parse annotation — block parses")
                )

        if failures:
            msg_parts = [f"{len(failures)} README code block(s) failed:"]
            for line_no, error in failures:
                msg_parts.append(f"  line {line_no}: {error}")
            raise AssertionError("\n".join(msg_parts))

    def test_vera_block_count(self) -> None:
        """README should have the expected number of Vera code blocks."""
        blocks = _vera_blocks()
        # Currently: safe_divide (intro), safe_divide (contracts section),
        # research_topic (effects section).
        # The error display block uses a plain ``` fence (not ```vera) by design.
        # Remaining examples live in EXAMPLES.md.
        assert len(blocks) == 3, (
            f"Expected 3 Vera blocks in README.md, found {len(blocks)}"
        )
