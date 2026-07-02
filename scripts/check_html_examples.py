#!/usr/bin/env python
"""Extract code blocks from docs/index.html and verify they parse, check, and verify.

The HTML landing page embeds Vera source inside <pre> elements within
<div class="code-block"> containers.  Syntax highlighting is applied via
<span class="kw|ty|sl|ct|num|str"> tags, which must be stripped to recover
plain Vera source.

Strategy (mirrors check_readme_examples.py with multi-stage validation):
  1. Extract all <pre> blocks inside <div class="code-block"> containers.
  2. Strip HTML tags and decode entities to recover plain Vera source.
  3. Skip non-Vera blocks (error diagnostics, shell commands).
  4. Parse, type-check, and verify each Vera block.
  5. Report failures.

A block that intentionally fails a stage carries an inline
`<!-- vera:skip-<stage> category="..." reason="..." -->` annotation on the
line immediately before its <pre> tag (#538; see scripts/doc_annotations.py).
The gate still runs the exempted stage: an annotated block that passes it is
a STALE annotation and fails the gate.  All current blocks pass all stages —
no block is annotated today.
"""

import subprocess
import sys
import tempfile
import re
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from doc_annotations import (  # noqa: E402  (scripts/ is not a package)
    evaluate_block,
    scan_html,
)

_TOP_LEVEL_RE = re.compile(
    r"\A\s*(?:--.*\n\s*)*"           # optional leading comments
    r"(?:public\s+|private\s+)?"     # optional visibility
    r"(?:fn\s|data\s|effect\s|type\s|module\s|import\s)",
)


def is_vera_block(content: str) -> bool:
    """Heuristic: does this block look like Vera source code?

    Requires a top-level Vera declaration (fn, data, effect, type, module,
    import) with optional visibility modifier.  This rejects error diagnostic
    displays (start with "Error in ..."), shell transcripts (start with "$"),
    and install steps.
    """
    return bool(_TOP_LEVEL_RE.search(content))


def try_parse(content: str) -> str | None:
    """Try to parse content as a Vera program. Returns error message or None."""
    from vera.parser import parse

    try:
        parse(content, file="<html>")
        return None
    except Exception as exc:
        return str(exc).split("\n")[0][:200]


def try_check(content: str, root: Path) -> str | None:
    """Try to type-check content. Returns error message or None."""
    # `delete=False` + manual close/unlink: on Windows a held-open temp
    # file can't be reopened by the subprocess (see TESTING.md's Test
    # Fixture Conventions and the matching pattern in tests/test_html.py).
    f = tempfile.NamedTemporaryFile(
        mode="w", suffix=".vera", delete=False, encoding="utf-8"
    )
    try:
        f.write(content)
        f.close()
        result = subprocess.run(
            [sys.executable, "-m", "vera.cli", "check", f.name],
            capture_output=True,
            text=True,
            encoding="utf-8",
            cwd=str(root),
            timeout=30,
        )
        if "OK:" in result.stdout:
            return None
        # Return first line of stderr or stdout for diagnostics
        err = result.stderr.strip() or result.stdout.strip()
        return err.split("\n")[0][:200]
    finally:
        Path(f.name).unlink(missing_ok=True)


def try_verify(content: str, root: Path) -> str | None:
    """Try to verify contracts. Returns error message or None."""
    # See try_check above for the delete=False rationale (Windows-portable).
    f = tempfile.NamedTemporaryFile(
        mode="w", suffix=".vera", delete=False, encoding="utf-8"
    )
    try:
        f.write(content)
        f.close()
        result = subprocess.run(
            [sys.executable, "-m", "vera.cli", "verify", f.name],
            capture_output=True,
            text=True,
            encoding="utf-8",
            cwd=str(root),
            timeout=60,
        )
        if "OK:" in result.stdout:
            return None
        err = result.stderr.strip() or result.stdout.strip()
        return err.split("\n")[0][:200]
    finally:
        Path(f.name).unlink(missing_ok=True)


def main() -> int:
    root = Path(__file__).resolve().parent.parent
    index_html = root / "docs/index.html"

    if not index_html.is_file():
        print("ERROR: docs/index.html not found.", file=sys.stderr)
        return 1

    blocks, problems = scan_html(index_html)

    stage_runners = [
        ("parse", try_parse),
        ("check", lambda content: try_check(content, root)),
        ("verify", lambda content: try_verify(content, root)),
    ]

    total_blocks = 0
    vera_blocks = 0
    skipped_non_vera = 0
    annotated = 0
    passed = 0
    failures: list[tuple[int, str, str]] = []  # (line, stage, error)
    stale: list[tuple[int, str, str, str]] = []  # (line, stage, cat, reason)

    for block in blocks:
        total_blocks += 1

        # Only test blocks that look like Vera source
        if not is_vera_block(block.content):
            if block.annotations:
                problems.append(
                    f"line {block.line}: vera:skip annotation on a block "
                    f"the non-Vera heuristic already skips — remove it"
                )
            skipped_non_vera += 1
            continue

        vera_blocks += 1

        outcomes = evaluate_block(block, stage_runners)
        last = outcomes[-1]
        if last.status == "failed":
            failures.append((block.line, last.stage, last.error or ""))
        elif last.status == "skipped":
            annotated += 1
        elif last.status == "stale":
            assert last.annotation is not None
            stale.append(
                (block.line, last.stage, last.annotation.category,
                 last.annotation.reason)
            )
        else:
            passed += 1

    # Report
    print(f"HTML code blocks: {total_blocks} total")
    print(f"  Skipped (non-Vera): {skipped_non_vera}")
    print(f"  Vera blocks: {vera_blocks}")
    print(f"    Passed (parse+check+verify): {passed}")
    print(f"    Annotated (vera:skip): {annotated}")
    print(f"    FAILED: {len(failures)}")

    exit_code = 0

    if problems:
        print("\nANNOTATION PROBLEMS:", file=sys.stderr)
        for problem in problems:
            print(f"  docs/index.html {problem}", file=sys.stderr)
        exit_code = 1

    if stale:
        print(
            "\nSTALE ANNOTATIONS (block passes the exempted stage — "
            "remove the annotation):",
            file=sys.stderr,
        )
        for line_no, stage, category, reason in stale:
            print(
                f"  docs/index.html line {line_no} "
                f"[vera:skip-{stage} {category}]: {reason}",
                file=sys.stderr,
            )
        exit_code = 1

    if failures:
        print("\nFAILURES:", file=sys.stderr)
        for line_no, stage, error in failures:
            print(f"\n  docs/index.html line {line_no} ({stage}):", file=sys.stderr)
            print(f"    {error}", file=sys.stderr)
        print(
            f"\n{len(failures)} HTML code block(s) failed.",
            file=sys.stderr,
        )
        print(
            "If a block is intentionally invalid, annotate it with "
            '<!-- vera:skip-<stage> category="..." reason="..." --> on the',
            file=sys.stderr,
        )
        print(
            "line before its <pre> tag (see scripts/doc_annotations.py).",
            file=sys.stderr,
        )
        exit_code = 1

    if exit_code == 0:
        print("\nAll HTML Vera code blocks pass (parse + check + verify).")

    return exit_code


if __name__ == "__main__":
    sys.exit(main())
