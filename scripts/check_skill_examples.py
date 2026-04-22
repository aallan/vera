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
    572: ("FRAGMENT", "Option/Result combinator usage examples, bare calls"),

    # Types section — bare type expressions, not declarations
    353: ("FRAGMENT", "Composite type examples, bare expressions"),
    370: ("FRAGMENT", "Type alias examples"),

    # Control flow — bare expressions
    442: ("FRAGMENT", "If/else expression example"),
    456: ("FRAGMENT", "Block expression example"),

    # Array operations — bare function calls
    600: ("FRAGMENT", "Array built-in examples, bare calls"),

    # Map operations — bare function calls
    630: ("FRAGMENT", "Map built-in examples, bare calls"),

    # Handler syntax — pseudocode template
    1321: ("FRAGMENT", "Effect handler syntax template"),

    # String operations — bare function calls
    712: ("FRAGMENT", "String built-in examples, bare calls"),

    # HTML operations — bare function calls and match expression
    829: ("FRAGMENT", "HTML built-in examples, bare calls"),
    845: ("FRAGMENT", "HTML match expression example, bare expression"),

    # Set operations — bare function calls
    647: ("FRAGMENT", "Set built-in examples, bare calls"),

    # Decimal operations — bare function calls
    661: ("FRAGMENT", "Decimal built-in examples, bare calls"),

    # JSON operations — bare function calls
    684: ("FRAGMENT", "JSON built-in examples, bare calls"),
    697: ("FRAGMENT", "JSON match expression example, bare expression"),

    # Markdown operations — bare function calls
    793: ("FRAGMENT", "Markdown built-in examples, bare calls"),

    # Regex operations — bare function calls
    860: ("FRAGMENT", "Regex built-in examples, bare calls"),
    871: ("FRAGMENT", "Regex Result matching example, bare expression"),

    # String interpolation — bare expressions
    756: ("FRAGMENT", "String interpolation examples, bare expressions"),

    # String search — bare function calls
    768: ("FRAGMENT", "String search built-in examples, bare calls"),

    # String transformation — bare function calls
    779: ("FRAGMENT", "String transformation built-in examples, bare calls"),

    # Numeric operations — bare function calls
    883: ("FRAGMENT", "Numeric built-in examples, bare calls"),

    # Math built-ins (#467) — bare function calls (log/trig/pi/clamp)
    898: ("FRAGMENT", "Math built-in examples: log/trig/constants/clamp, bare calls"),

    # Contracts section — requires/ensures fragments
    962: ("FRAGMENT", "Requires clause example, not full function"),
    971: ("FRAGMENT", "Ensures clause example, not full function"),

    # Quantified expressions — bare forall/exists calls
    1021: ("FRAGMENT", "Quantified expression examples, bare calls"),

    # Effects section — bare effect rows
    # (old entry at 580 removed — block shifted to 582 with Async addition)

    # Effect handler syntax template
    1304: ("FRAGMENT", "Handler syntax template, not real code"),

    # Effect declarations — bare effects(...) clauses
    1039: ("FRAGMENT", "Effect declarations list"),
    1148: ("FRAGMENT", "Async effect declarations list"),
    1198: ("FRAGMENT", "Http effect declarations list"),
    1229: ("FRAGMENT", "Inference effect declarations list"),

    # Qualified calls and handler fragments — bare expressions
    1237: ("FRAGMENT", "Handler with clause, bare expression"),

    # Line comments — bare comments
    1537: ("FRAGMENT", "Comment syntax example"),

    # Type conversions — bare function calls
    920: ("FRAGMENT", "Type conversions, bare calls"),

    # Common mistakes section — intentionally wrong code
    1616: ("FRAGMENT", "Wrong: missing contracts"),
    1636: ("FRAGMENT", "Wrong: missing effects clause (with contracts)"),
    1683: ("FRAGMENT", "Wrong: missing index on slot reference"),
    1688: ("FRAGMENT", "Correct: expression with indices (not full fn)"),
    1800: ("FRAGMENT", "Wrong: non-exhaustive match (missing None)"),
    1778: ("FRAGMENT", "Wrong: non-exhaustive match (missing arm)"),

    # Import syntax — intentionally unsupported
    1811: ("FRAGMENT", "Wrong: import aliasing not supported"),
    1816: ("FRAGMENT", "Correct: import syntax example"),
    1826: ("FRAGMENT", "Wrong: import hiding not supported"),

    # Match arm fragment — bare match body
    1785: ("FRAGMENT", "Correct: match expression example (bare)"),
    1795: ("FRAGMENT", "Common mistake example, bare if/else"),
    1765: ("FRAGMENT", "Correct: if/else with braces (common mistakes)"),

    # String escapes — bare expression
    1845: ("FRAGMENT", "Correct escape sequence examples, bare strings"),

    # Map/Set common mistakes — bare let bindings
    1853: ("FRAGMENT", "Wrong: standalone map_new/set_new without type context"),
    1859: ("FRAGMENT", "Correct: map_new/set_new with type context"),

    # Effect disambiguation — qualified calls
    1343: ("FRAGMENT", "Qualified effect calls (State.put, Logger.put)"),

    # Typed holes section — expression fragments and handler clause fragment
    510: ("FRAGMENT", "Typed hole fill-in example, bare if/else expression"),
    1168: ("FRAGMENT", "Async effect row declarations, bare clauses"),
    1333: ("FRAGMENT", "Handler with-clause, bare put arm expression"),

    # Float64 predicates — bare function calls (shifted by De Bruijn section additions)
    933: ("FRAGMENT", "Float64 predicate and constant examples, bare calls"),

    # Contracts incremental workflow — placeholder scaffolding, not a full function
    1001: ("FRAGMENT", "Contracts scaffolding template: requires(true) ensures(true)"),

    # =================================================================
    # MISMATCH — uses syntax the parser doesn't handle in isolation.
    # =================================================================

    # Function template with placeholders
    127: ("MISMATCH", "Function signature template with @ParamType placeholders"),
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
    skip_langs = {"bash", "python", "json", "toml", "yaml", "shell", "sh", "text", ""}

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
