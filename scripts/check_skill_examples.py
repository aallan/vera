#!/usr/bin/env python
"""Extract code blocks from SKILL.md and verify parseable ones still parse.

Strategy mirrors check_readme_examples.py:
  1. Extract all fenced code blocks tagged as `vera` from SKILL.md.
  2. Skip blocks tagged as non-Vera (```bash, ```python, etc.).
  3. Try to parse each Vera block with the Vera parser.
  4. Report failures. Maintain an allowlist for known-unparseable blocks.

The allowlist uses line_number tuples so failures are stable across edits.
"""

import re
import sys
from pathlib import Path


# -- Allowlist: SKILL.md blocks that are intentionally unparseable. --------
#
# Each entry is (start_line_of_code_fence, category, reason).

ALLOWLIST: dict[int, tuple[str, str]] = {
    # =================================================================
    # FRAGMENT — snippets used as examples/illustrations, not full
    # function declarations or programs.
    # =================================================================

    # Types section — bare type expressions, not declarations
    284: ("FRAGMENT", "Composite type examples, bare expressions"),
    296: ("FRAGMENT", "Type alias examples"),

    # Control flow — bare expressions
    366: ("FRAGMENT", "If/else expression example"),
    380: ("FRAGMENT", "Block expression example"),

    # Array operations — bare function calls
    395: ("FRAGMENT", "Array built-in examples, bare calls"),

    # String operations — bare function calls
    404: ("FRAGMENT", "String built-in examples, bare calls"),

    # String interpolation — bare expressions
    426: ("FRAGMENT", "String interpolation examples, bare expressions"),

    # String search — bare function calls
    438: ("FRAGMENT", "String search built-in examples, bare calls"),

    # String transformation — bare function calls
    449: ("FRAGMENT", "String transformation built-in examples, bare calls"),

    # Numeric operations — bare function calls
    463: ("FRAGMENT", "Numeric built-in examples, bare calls"),

    # Contracts section — requires/ensures fragments
    520: ("FRAGMENT", "Requires clause example, not full function"),
    529: ("FRAGMENT", "Ensures clause example, not full function"),
    556: ("FRAGMENT", "Quantified requires clause, not full function"),

    # Effects section — bare effect rows
    574: ("FRAGMENT", "Effect row examples, bare annotations"),

    # Effect handler syntax template
    711: ("FRAGMENT", "Handler syntax template, not real code"),

    # Qualified calls and handler fragments — bare expressions
    723: ("FRAGMENT", "Handler with clause, bare expression"),
    733: ("FRAGMENT", "Qualified call examples, bare expressions"),

    # Module declaration and import syntax
    771: ("FRAGMENT", "Module declaration and import example"),

    # Line comments — bare comments
    822: ("FRAGMENT", "Comment syntax example"),

    # Type conversions — bare function calls
    478: ("FRAGMENT", "Type conversion examples, bare calls"),

    # Float64 predicates — bare function calls
    491: ("FRAGMENT", "Float64 predicate examples, bare calls"),

    # Common mistakes section — intentionally wrong code
    850: ("FRAGMENT", "Wrong: missing contracts"),
    857: ("FRAGMENT", "Wrong: incorrect contract syntax"),
    870: ("FRAGMENT", "Wrong: missing requires"),
    857: ("FRAGMENT", "Wrong: missing effects clause"),
    870: ("FRAGMENT", "Wrong: wrong effect declared"),
    904: ("FRAGMENT", "Wrong: bare expression without indices"),
    917: ("FRAGMENT", "Wrong: bare expression no indices"),
    922: ("FRAGMENT", "Correct: expression with indices (not full fn)"),
    988: ("FRAGMENT", "Wrong: match arm with incorrect return"),
    1012: ("FRAGMENT", "Wrong: non-exhaustive match"),
    1019: ("FRAGMENT", "Correct: match arm example"),
    1029: ("FRAGMENT", "Wrong: if/else without braces (bare expression)"),
    1034: ("FRAGMENT", "Correct: if/else with braces"),

    # Import syntax — intentionally unsupported
    1045: ("FRAGMENT", "Wrong: import aliasing not supported"),
    1050: ("FRAGMENT", "Correct: import syntax example"),
    1060: ("FRAGMENT", "Wrong: import hiding not supported"),
    1065: ("FRAGMENT", "Correct: multi-import syntax"),

    # String escapes — bare expression
    1079: ("FRAGMENT", "String escape example"),

    # =================================================================
    # MISMATCH — uses syntax the parser doesn't handle in isolation.
    # =================================================================

    # Function template with placeholders
    96: ("MISMATCH", "Function signature template with @ParamType placeholders"),
}


def extract_code_blocks(path: Path) -> list[tuple[int, str, str]]:
    """Extract fenced code blocks from a Markdown file.

    Returns list of (line_number, language_tag, content) tuples.
    line_number is the 1-based line of the opening ``` fence.
    """
    lines = path.read_text(encoding="utf-8").splitlines()
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


def try_parse(content: str) -> str | None:
    """Try to parse content as a Vera program. Returns error message or None."""
    from vera.parser import parse

    try:
        parse(content, file="<skill>")
        return None
    except Exception as exc:
        return str(exc).split("\n")[0][:200]


def main() -> int:
    root = Path(__file__).resolve().parent.parent
    skill = root / "SKILL.md"

    if not skill.is_file():
        print("ERROR: SKILL.md not found.", file=sys.stderr)
        return 1

    # Non-Vera language tags to skip entirely
    skip_langs = {"bash", "python", "json", "toml", "yaml", "shell", "sh", ""}

    blocks = extract_code_blocks(skill)

    total_blocks = 0
    vera_blocks = 0
    skipped_lang = 0
    skipped_allowlist = 0
    passed = 0
    failures: list[tuple[int, str]] = []

    # Track which allowlist entries are used
    used_allowlist: set[int] = set()

    for line_no, lang, content in blocks:
        total_blocks += 1

        # Only test vera-tagged blocks
        if lang.lower() != "vera":
            skipped_lang += 1
            continue

        vera_blocks += 1

        # Check allowlist
        if line_no in ALLOWLIST:
            used_allowlist.add(line_no)
            skipped_allowlist += 1
            continue

        # Try to parse
        error = try_parse(content)
        if error is None:
            passed += 1
        else:
            failures.append((line_no, error))

    # Check for stale allowlist entries
    stale_allowlist: list[tuple[int, str, str]] = []
    for line_no, (category, reason) in ALLOWLIST.items():
        if line_no not in used_allowlist:
            stale_allowlist.append((line_no, category, reason))

    # Report
    print(f"SKILL.md code blocks: {total_blocks} total")
    print(f"  Skipped (non-Vera language): {skipped_lang}")
    print(f"  Vera blocks: {vera_blocks}")
    print(f"    Parsed OK: {passed}")
    print(f"    Allowlisted: {skipped_allowlist}")
    print(f"    FAILED: {len(failures)}")

    exit_code = 0

    if stale_allowlist:
        print("\nSTALE ALLOWLIST ENTRIES:", file=sys.stderr)
        for line_no, category, reason in stale_allowlist:
            print(
                f"  SKILL.md line {line_no} [{category}]: {reason}",
                file=sys.stderr,
            )
        print(
            "\nRun: python scripts/fix_allowlists.py --fix",
            file=sys.stderr,
        )
        exit_code = 1

    if failures:
        print("\nFAILURES:", file=sys.stderr)
        for line_no, error in failures:
            print(f"\n  SKILL.md line {line_no}:", file=sys.stderr)
            print(f"    {error}", file=sys.stderr)
        print(
            f"\n{len(failures)} SKILL.md code block(s) failed to parse.",
            file=sys.stderr,
        )
        print(
            "If a block is intentionally unparseable, add it to the ALLOWLIST",
            file=sys.stderr,
        )
        print(
            "in scripts/check_skill_examples.py with the appropriate category.",
            file=sys.stderr,
        )
        exit_code = 1

    if exit_code == 0:
        print("\nAll SKILL.md Vera code blocks parse successfully.")

    return exit_code


if __name__ == "__main__":
    sys.exit(main())
