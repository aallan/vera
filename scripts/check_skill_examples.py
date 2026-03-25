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

    # Option/Result combinator examples — bare function calls
    461: ("FRAGMENT", "Option/Result combinator usage examples, bare calls"),

    # Types section — bare type expressions, not declarations
    304: ("FRAGMENT", "Composite type examples, bare expressions"),
    320: ("FRAGMENT", "Type alias examples"),

    # Control flow — bare expressions
    392: ("FRAGMENT", "If/else expression example"),
    406: ("FRAGMENT", "Block expression example"),

    # Array operations — bare function calls
    498: ("FRAGMENT", "Array built-in examples, bare calls"),

    # Map operations — bare function calls
    516: ("FRAGMENT", "Map built-in examples, bare calls"),

    # Handler syntax — pseudocode template
    1007: ("FRAGMENT", "Effect handler syntax template"),

    # Common mistake: bare if/else expression
    1414: ("FRAGMENT", "Common mistake example, bare if/else"),

    # String operations — bare function calls
    598: ("FRAGMENT", "String built-in examples, bare calls"),

    # Set operations — bare function calls
    533: ("FRAGMENT", "Set built-in examples, bare calls"),

    # Decimal operations — bare function calls
    547: ("FRAGMENT", "Decimal built-in examples, bare calls"),

    # JSON operations — bare function calls
    570: ("FRAGMENT", "JSON built-in examples, bare calls"),
    583: ("FRAGMENT", "JSON match expression example, bare expression"),

    # Markdown operations — bare function calls
    674: ("FRAGMENT", "Markdown built-in examples, bare calls"),

    # Regex operations — bare function calls
    708: ("FRAGMENT", "Regex built-in examples, bare calls"),
    719: ("FRAGMENT", "Regex Result matching example, bare expression"),

    # String interpolation — bare expressions
    637: ("FRAGMENT", "String interpolation examples, bare expressions"),

    # String search — bare function calls
    649: ("FRAGMENT", "String search built-in examples, bare calls"),

    # String transformation — bare function calls
    660: ("FRAGMENT", "String transformation built-in examples, bare calls"),

    # Numeric operations — bare function calls
    731: ("FRAGMENT", "Numeric built-in examples, bare calls"),

    # Contracts section — requires/ensures fragments
    788: ("FRAGMENT", "Requires clause example, not full function"),
    797: ("FRAGMENT", "Ensures clause example, not full function"),

    # Quantified expressions — bare forall/exists calls
    824: ("FRAGMENT", "Quantified expression examples, bare calls"),

    # Effects section — bare effect rows
    # (old entry at 580 removed — block shifted to 582 with Async addition)

    # Effect handler syntax template
    990: ("FRAGMENT", "Handler syntax template, not real code"),

    # Effect declarations — bare effects(...) clauses
    842: ("FRAGMENT", "Effect declarations list"),
    945: ("FRAGMENT", "Async effect declarations list"),
    965: ("FRAGMENT", "Async effect declarations, bare clauses"),

    # Qualified calls and handler fragments — bare expressions
    1019: ("FRAGMENT", "Handler with clause, bare expression"),

    # Module declaration and import syntax
    1067: ("FRAGMENT", "Module declaration and import example"),

    # Line comments — bare comments
    1172: ("FRAGMENT", "Comment syntax example"),

    # Type conversions — bare function calls
    759: ("FRAGMENT", "Float64 predicate and constant examples, bare calls"),

    # Float64 predicates — bare function calls
    746: ("FRAGMENT", "Float64 predicate examples, bare calls"),

    # Common mistakes section — intentionally wrong code
    1235: ("FRAGMENT", "Wrong: missing contracts"),
    1242: ("FRAGMENT", "Wrong: missing effects clause"),
    1255: ("FRAGMENT", "Wrong: missing effects clause (with contracts)"),
    1289: ("FRAGMENT", "Wrong: bare expression without indices"),
    1302: ("FRAGMENT", "Wrong: missing index on slot reference"),
    1307: ("FRAGMENT", "Correct: expression with indices (not full fn)"),
    1359: ("FRAGMENT", "Wrong: match arm with incorrect return"),
    1384: ("FRAGMENT", "Wrong: non-exhaustive match (missing None)"),
    1397: ("FRAGMENT", "Wrong: non-exhaustive match (missing arm)"),

    # Import syntax — intentionally unsupported
    1430: ("FRAGMENT", "Wrong: import aliasing not supported"),
    1435: ("FRAGMENT", "Correct: import syntax example"),
    1445: ("FRAGMENT", "Wrong: import hiding not supported"),
    1450: ("FRAGMENT", "Correct: multi-import syntax"),

    # Match arm fragment — bare match body
    1404: ("FRAGMENT", "Match arm bare expression"),
    1419: ("FRAGMENT", "Correct: if/else with braces (common mistakes)"),

    # String escapes — bare expression
    1464: ("FRAGMENT", "String escape backslash examples"),

    # Map/Set common mistakes — bare let bindings
    1472: ("FRAGMENT", "Wrong: standalone map_new/set_new without type context"),
    1478: ("FRAGMENT", "Correct: map_new/set_new with type context"),

    # Effect disambiguation — qualified calls
    1029: ("FRAGMENT", "Qualified effect calls (State.put, Logger.put)"),

    # =================================================================
    # MISMATCH — uses syntax the parser doesn't handle in isolation.
    # =================================================================

    # Function template with placeholders
    116: ("MISMATCH", "Function signature template with @ParamType placeholders"),
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
