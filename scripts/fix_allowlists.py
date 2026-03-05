#!/usr/bin/env python
"""Auto-fix allowlist line numbers after Markdown edits.

When Markdown files are edited (adding/removing lines), code block line
numbers shift and the allowlists in the validation scripts go stale.
This script detects the drift by comparing the current file against the
last committed version (git HEAD), matches blocks by content, and
rewrites the allowlists with corrected line numbers.

Usage:
    python scripts/fix_allowlists.py          # Preview changes (dry run)
    python scripts/fix_allowlists.py --fix    # Apply changes in place

The script handles all four allowlist files:
  - scripts/check_readme_examples.py   (README.md)
  - tests/test_readme.py               (README.md)
  - scripts/check_skill_examples.py    (SKILL.md)
  - scripts/check_spec_examples.py     (spec/*.md)
"""

from __future__ import annotations

import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent


# ---------------------------------------------------------------------------
# Code block extraction (mirrors the logic in the check scripts)
# ---------------------------------------------------------------------------

def extract_blocks(text: str) -> list[tuple[int, str, str]]:
    """Extract fenced code blocks from Markdown text.

    Returns list of (line_number, language_tag, content) tuples.
    line_number is 1-based (line of the opening ``` fence).
    """
    lines = text.splitlines()
    blocks: list[tuple[int, str, str]] = []
    i = 0
    while i < len(lines):
        m = re.match(r"^```(\w*)$", lines[i])
        if m:
            lang = m.group(1)
            start_line = i + 1  # 1-based
            content_lines: list[str] = []
            i += 1
            while i < len(lines) and not re.match(r"^```$", lines[i]):
                content_lines.append(lines[i])
                i += 1
            blocks.append((start_line, lang, "\n".join(content_lines)))
        i += 1
    return blocks


def git_show(path: str) -> str | None:
    """Read a file from git HEAD.  Returns None if the file is untracked."""
    try:
        result = subprocess.run(
            ["git", "show", f"HEAD:{path}"],
            capture_output=True, text=True, check=True,
            cwd=str(ROOT),
        )
        return result.stdout
    except subprocess.CalledProcessError:
        return None


# ---------------------------------------------------------------------------
# Build old→new line number mapping for a single Markdown file
# ---------------------------------------------------------------------------

def build_line_map(md_rel_path: str) -> dict[int, int]:
    """Compare git HEAD vs working tree for a Markdown file.

    Returns {old_line_no: new_line_no} for blocks whose content matches
    but whose line number shifted.  Blocks that were added or removed
    are not included.
    """
    old_text = git_show(md_rel_path)
    if old_text is None:
        return {}

    new_text = (ROOT / md_rel_path).read_text(encoding="utf-8")

    old_blocks = extract_blocks(old_text)
    new_blocks = extract_blocks(new_text)

    # Index new blocks by (lang, content) → line_no.
    # If duplicates exist, keep all of them and match by proximity.
    new_by_content: dict[tuple[str, str], list[int]] = {}
    for line_no, lang, content in new_blocks:
        new_by_content.setdefault((lang, content), []).append(line_no)

    mapping: dict[int, int] = {}
    for old_line, lang, content in old_blocks:
        candidates = new_by_content.get((lang, content))
        if candidates:
            # Pick the closest candidate (handles duplicate content)
            best = min(candidates, key=lambda n: abs(n - old_line))
            if best != old_line:
                mapping[old_line] = best

    return mapping


# ---------------------------------------------------------------------------
# Rewrite allowlist entries in a Python source file
# ---------------------------------------------------------------------------

def rewrite_simple_allowlist(
    py_path: Path,
    line_map: dict[int, int],
) -> tuple[str, list[tuple[int, int]]]:
    """Rewrite ``  NNN:`` dict keys in a Python file using line_map.

    Returns (new_source, [(old, new), ...]) listing applied changes.
    """
    source = py_path.read_text(encoding="utf-8")
    changes: list[tuple[int, int]] = []

    def replace_key(m: re.Match[str]) -> str:
        indent = m.group(1)
        old = int(m.group(2))
        rest = m.group(3)
        if old in line_map:
            new = line_map[old]
            changes.append((old, new))
            return f"{indent}{new}{rest}"
        return m.group(0)

    # Match lines like "    370: ..." where 370 is a dict key.
    # Careful: only match inside dict literals (indented, followed by colon).
    new_source = re.sub(
        r"^(\s+)(\d+)(:.*)",
        replace_key,
        source,
        flags=re.MULTILINE,
    )
    return new_source, changes


def rewrite_tuple_allowlist(
    py_path: Path,
    line_maps: dict[str, dict[int, int]],
) -> tuple[str, list[tuple[str, int, int]]]:
    """Rewrite ``("filename.md", NNN):`` dict keys in a Python file.

    line_maps maps filename → {old_line: new_line}.
    Returns (new_source, [(filename, old, new), ...]).
    """
    source = py_path.read_text(encoding="utf-8")
    changes: list[tuple[str, int, int]] = []

    def replace_tuple_key(m: re.Match[str]) -> str:
        prefix = m.group(1)
        filename = m.group(2)
        old = int(m.group(3))
        suffix = m.group(4)
        lm = line_maps.get(filename, {})
        if old in lm:
            new = lm[old]
            changes.append((filename, old, new))
            return f'{prefix}{filename}", {new}{suffix}'
        return m.group(0)

    # Match lines like:  ("09-standard-library.md", 290): "FUTURE",
    new_source = re.sub(
        r'([(]\s*")([\w.-]+)",\s*(\d+)(\))',
        replace_tuple_key,
        source,
    )
    return new_source, changes


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main() -> int:
    fix = "--fix" in sys.argv

    total_changes = 0

    # ---- README.md ---------------------------------------------------------
    readme_map = build_line_map("README.md")
    if readme_map:
        for py_path in [
            ROOT / "scripts" / "check_readme_examples.py",
            ROOT / "tests" / "test_readme.py",
        ]:
            new_source, changes = rewrite_simple_allowlist(py_path, readme_map)
            if changes:
                total_changes += len(changes)
                rel = py_path.relative_to(ROOT)
                for old, new in changes:
                    print(f"  {rel}: README.md line {old} → {new}")
                if fix:
                    py_path.write_text(new_source, encoding="utf-8")

    # ---- SKILL.md ----------------------------------------------------------
    skill_map = build_line_map("SKILL.md")
    if skill_map:
        py_path = ROOT / "scripts" / "check_skill_examples.py"
        new_source, changes = rewrite_simple_allowlist(py_path, skill_map)
        if changes:
            total_changes += len(changes)
            rel = py_path.relative_to(ROOT)
            for old, new in changes:
                print(f"  {rel}: SKILL.md line {old} → {new}")
            if fix:
                py_path.write_text(new_source, encoding="utf-8")

    # ---- spec/*.md ---------------------------------------------------------
    spec_dir = ROOT / "spec"
    spec_files = sorted(spec_dir.glob("*.md"))
    spec_maps: dict[str, dict[int, int]] = {}
    for spec_file in spec_files:
        rel = f"spec/{spec_file.name}"
        lm = build_line_map(rel)
        if lm:
            spec_maps[spec_file.name] = lm

    if spec_maps:
        py_path = ROOT / "scripts" / "check_spec_examples.py"
        new_source, changes = rewrite_tuple_allowlist(py_path, spec_maps)
        if changes:
            total_changes += len(changes)
            rel = py_path.relative_to(ROOT)
            for filename, old, new in changes:
                print(f"  {rel}: {filename} line {old} → {new}")
            if fix:
                py_path.write_text(new_source, encoding="utf-8")

    # ---- Summary -----------------------------------------------------------
    if total_changes == 0:
        print("All allowlist entries are up to date.")
        return 0

    print(f"\n{total_changes} allowlist entry/entries need updating.")
    if fix:
        print("Fixed.  Re-stage the modified files and commit.")
    else:
        print("Run with --fix to apply changes:")
        print("  python scripts/fix_allowlists.py --fix")
    return 0 if fix else 1


if __name__ == "__main__":
    sys.exit(main())
