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
    643: ("FRAGMENT", "Option/Result combinator usage examples, bare calls"),

    # Types section — bare type expressions, not declarations
    353: ("FRAGMENT", "Composite type examples, bare expressions"),
    386: ("FRAGMENT", "Type alias examples"),

    # Control flow — bare expressions
    458: ("FRAGMENT", "If/else expression example"),
    472: ("FRAGMENT", "Block expression example"),

    # Array operations — bare function calls
    671: ("FRAGMENT", "Array built-in examples, bare calls"),

    # Map operations — bare function calls
    701: ("FRAGMENT", "Map built-in examples, bare calls"),

    # Handler syntax — pseudocode template
    1459: ("FRAGMENT", "Effect handler syntax template"),

    # String operations — bare function calls
    816: ("FRAGMENT", "String built-in examples, bare calls"),

    # HTML operations — bare function calls and match expression
    967: ("FRAGMENT", "HTML built-in examples, bare calls"),
    983: ("FRAGMENT", "HTML match expression example, bare expression"),

    # Set operations — bare function calls
    718: ("FRAGMENT", "Set built-in examples, bare calls"),

    # Decimal operations — bare function calls
    732: ("FRAGMENT", "Decimal built-in examples, bare calls"),

    # JSON operations — bare function calls
    755: ("FRAGMENT", "JSON built-in examples, bare calls"),
    768: ("FRAGMENT", "JSON match expression example, bare expression"),

    # Markdown operations — bare function calls
    860: ("FRAGMENT", "Markdown built-in examples, bare calls"),

    # Regex operations — bare function calls
    998: ("FRAGMENT", "Regex built-in examples, bare calls"),
    1009: ("FRAGMENT", "Regex Result matching example, bare expression"),

    # String interpolation — bare expressions
    860: ("FRAGMENT", "String interpolation examples, bare expressions"),

    # String search — bare function calls
    872: ("FRAGMENT", "String search built-in examples, bare calls"),

    # String transformation — bare function calls
    883: ("FRAGMENT", "String transformation built-in examples, bare calls"),

    # Numeric operations — bare function calls
    1021: ("FRAGMENT", "Numeric built-in examples, bare calls"),

    # Math built-ins (#467) — bare function calls (log/trig/pi/clamp)
    1036: ("FRAGMENT", "Math built-in examples: log/trig/constants/clamp, bare calls"),

    # Contracts section — requires/ensures fragments
    1100: ("FRAGMENT", "Requires clause example, not full function"),
    1109: ("FRAGMENT", "Ensures clause example, not full function"),

    # Quantified expressions — bare forall/exists calls
    1159: ("FRAGMENT", "Quantified expression examples, bare calls"),

    # Effects section — bare effect rows
    # (old entry at 580 removed — block shifted to 582 with Async addition)

    # Effect handler syntax template
    1442: ("FRAGMENT", "Handler syntax template, not real code"),

    # Effect declarations — bare effects(...) clauses
    1177: ("FRAGMENT", "Effect declarations list"),
    1286: ("FRAGMENT", "Async effect declarations list"),
    1336: ("FRAGMENT", "Http effect declarations list"),
    1367: ("FRAGMENT", "Inference effect declarations list"),

    # Qualified calls and handler fragments — bare expressions
    1375: ("FRAGMENT", "Handler with clause, bare expression"),

    # Line comments — bare comments
    1675: ("FRAGMENT", "Comment syntax example"),

    # Type conversions — bare function calls
    1058: ("FRAGMENT", "Type conversions, bare calls"),

    # Common mistakes section — intentionally wrong code
    1754: ("FRAGMENT", "Wrong: missing contracts"),
    1774: ("FRAGMENT", "Wrong: missing effects clause (with contracts)"),
    1821: ("FRAGMENT", "Wrong: missing index on slot reference"),
    1826: ("FRAGMENT", "Correct: expression with indices (not full fn)"),
    1938: ("FRAGMENT", "Wrong: non-exhaustive match (missing None)"),
    1916: ("FRAGMENT", "Wrong: non-exhaustive match (missing arm)"),

    # Import syntax — intentionally unsupported.  The four match/import
    # Common-Mistakes blocks live at four distinct line numbers (1845,
    # 1878, 1883, 1893) in the current SKILL.md, each with its own
    # explicit entry here.  Prior versions of the ALLOWLIST mis-used
    # the same key (1845, 1893) for two different blocks each, which
    # silently shadowed half the entries via dict last-write-wins.
    # Fixed in PR #511 after CR caught the duplicate-key pattern.
    1949: ("FRAGMENT", "Wrong: import aliasing not supported"),
    1954: ("FRAGMENT", "Correct: import syntax example"),
    1964: ("FRAGMENT", "Wrong: import hiding not supported"),

    # Match arm fragment — bare match body
    1923: ("FRAGMENT", "Correct: match expression example (bare)"),
    1933: ("FRAGMENT", "Common mistake example, bare if/else"),
    1903: ("FRAGMENT", "Correct: if/else with braces (common mistakes)"),

    # String escapes — bare expression
    1983: ("FRAGMENT", "Correct escape sequence examples, bare strings"),

    # Map/Set common mistakes — bare let bindings
    1991: ("FRAGMENT", "Wrong: standalone map_new/set_new without type context"),
    1997: ("FRAGMENT", "Correct: map_new/set_new with type context"),

    # Effect disambiguation — qualified calls
    1481: ("FRAGMENT", "Qualified effect calls (State.put, Logger.put)"),

    # Typed holes section — expression fragments and handler clause fragment
    526: ("FRAGMENT", "Typed hole fill-in example, bare if/else expression"),
    1306: ("FRAGMENT", "Async effect row declarations, bare clauses"),
    1471: ("FRAGMENT", "Handler with-clause, bare put arm expression"),

    # Float64 predicates — bare function calls (shifted by De Bruijn section additions)
    1071: ("FRAGMENT", "Float64 predicate and constant examples, bare calls"),

    # Contracts incremental workflow — placeholder scaffolding, not a full function
    1139: ("FRAGMENT", "Contracts scaffolding template: requires(true) ensures(true)"),

    # String utilities and character classification — bare function-call signatures
    895: ("FRAGMENT", "String utility / classifier signatures, bare function calls"),

    # JSON typed accessors (#366) — bare function-call signatures
    785: ("FRAGMENT", "JSON Layer 1 accessor signatures, bare function calls"),

    # Array literals (#513) — bare let-binding examples
    372: ("FRAGMENT", "Array literal examples, bare let bindings"),

    # Closures section (#513) — bare array_map + fold examples using closures
    571: ("FRAGMENT", "Closure example, bare let bindings with array_map call"),

    # Markdown built-ins — bare function-call signatures (shifted by #513)
    931: ("FRAGMENT", "md_parse / md_render / md_has_heading signatures, bare calls"),
    804: ("FRAGMENT", "JSON Layer 2 accessor signatures, bare function calls"),

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
