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
  5. Report failures.  Maintain an allowlist for known-unparseable blocks.
"""

import html
import re
import subprocess
import sys
import tempfile
from pathlib import Path


# -- Allowlist: blocks that are intentionally unparseable. -------------------
#
# Each entry is (start_line_of_pre_tag, category, reason).
# Currently empty — all blocks should pass all stages.

ALLOWLIST: dict[int, tuple[str, str]] = {}


def extract_code_blocks(path: Path) -> list[tuple[int, str]]:
    """Extract <pre> blocks from <div class="code-block"> containers.

    Returns list of (line_number, plain_text_content) tuples.
    line_number is the 1-based line of the <pre> tag.
    """
    text = path.read_text(encoding="utf-8")
    lines = text.splitlines()
    blocks: list[tuple[int, str]] = []

    i = 0
    while i < len(lines):
        # Look for a <pre> tag inside a code-block div
        if "<pre>" in lines[i] or "<pre " in lines[i]:
            start_line = i + 1  # 1-based
            # Collect everything from this line through the closing </pre>
            pre_lines: list[str] = []
            while i < len(lines):
                pre_lines.append(lines[i])
                if "</pre>" in lines[i]:
                    break
                i += 1
            raw_html = "\n".join(pre_lines)

            # Extract content between <pre> and </pre>
            m = re.search(r"<pre[^>]*>(.*?)</pre>", raw_html, re.DOTALL)
            if m:
                content = m.group(1)
                # Strip all HTML tags
                content = re.sub(r"<[^>]+>", "", content)
                # Decode HTML entities
                content = html.unescape(content)
                blocks.append((start_line, content.strip()))
        i += 1

    return blocks


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
    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".vera", dir=str(root), delete=True
    ) as f:
        f.write(content)
        f.flush()
        result = subprocess.run(
            [sys.executable, "-m", "vera.cli", "check", f.name],
            capture_output=True,
            text=True,
            cwd=str(root),
            timeout=30,
        )
        if "OK:" in result.stdout:
            return None
        # Return first line of stderr or stdout for diagnostics
        err = result.stderr.strip() or result.stdout.strip()
        return err.split("\n")[0][:200]


def try_verify(content: str, root: Path) -> str | None:
    """Try to verify contracts. Returns error message or None."""
    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".vera", dir=str(root), delete=True
    ) as f:
        f.write(content)
        f.flush()
        result = subprocess.run(
            [sys.executable, "-m", "vera.cli", "verify", f.name],
            capture_output=True,
            text=True,
            cwd=str(root),
            timeout=60,
        )
        if "OK:" in result.stdout:
            return None
        err = result.stderr.strip() or result.stdout.strip()
        return err.split("\n")[0][:200]


def main() -> int:
    root = Path(__file__).resolve().parent.parent
    index_html = root / "docs/index.html"

    if not index_html.is_file():
        print("ERROR: docs/index.html not found.", file=sys.stderr)
        return 1

    blocks = extract_code_blocks(index_html)

    total_blocks = 0
    vera_blocks = 0
    skipped_non_vera = 0
    skipped_allowlist = 0
    passed = 0
    failures: list[tuple[int, str, str]] = []  # (line, stage, error)

    # Track which allowlist entries are used
    used_allowlist: set[int] = set()

    for line_no, content in blocks:
        total_blocks += 1

        # Only test blocks that look like Vera source
        if not is_vera_block(content):
            skipped_non_vera += 1
            continue

        vera_blocks += 1

        # Check allowlist
        if line_no in ALLOWLIST:
            used_allowlist.add(line_no)
            skipped_allowlist += 1
            continue

        # Stage 1: Parse
        error = try_parse(content)
        if error is not None:
            failures.append((line_no, "parse", error))
            continue

        # Stage 2: Type-check
        error = try_check(content, root)
        if error is not None:
            failures.append((line_no, "check", error))
            continue

        # Stage 3: Verify contracts
        error = try_verify(content, root)
        if error is not None:
            failures.append((line_no, "verify", error))
            continue

        passed += 1

    # Check for stale allowlist entries
    stale_allowlist: list[tuple[int, str, str]] = []
    for line_no, (category, reason) in ALLOWLIST.items():
        if line_no not in used_allowlist:
            stale_allowlist.append((line_no, category, reason))

    # Report
    print(f"HTML code blocks: {total_blocks} total")
    print(f"  Skipped (non-Vera): {skipped_non_vera}")
    print(f"  Vera blocks: {vera_blocks}")
    print(f"    Passed (parse+check+verify): {passed}")
    print(f"    Allowlisted: {skipped_allowlist}")
    print(f"    FAILED: {len(failures)}")

    exit_code = 0

    if stale_allowlist:
        print("\nSTALE ALLOWLIST ENTRIES:", file=sys.stderr)
        for line_no, category, reason in stale_allowlist:
            print(
                f"  docs/index.html line {line_no} [{category}]: {reason}",
                file=sys.stderr,
            )
        print(
            "\nRun: python scripts/fix_allowlists.py --fix",
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
            "If a block is intentionally invalid, add it to the ALLOWLIST",
            file=sys.stderr,
        )
        print(
            "in scripts/check_html_examples.py with the appropriate category.",
            file=sys.stderr,
        )
        exit_code = 1

    if exit_code == 0:
        print("\nAll HTML Vera code blocks pass (parse + check + verify).")

    return exit_code


if __name__ == "__main__":
    sys.exit(main())
