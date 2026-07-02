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
    # function declarations or programs.  Each entry maps a unique
    # opening-```vera fence line number to a (category, reason) pair.
    # Duplicate keys silently shadow via dict last-write-wins, so the
    # file has an AST-level dup check applied during PR review
    # (see #511 and memory/feedback_spec_allowlist.md for history).
    # =================================================================

    # Type aliases + type expressions
    191: ("FRAGMENT", "Type alias (Fn type) in apply_fn docs, bare declaration"),
    409: ("FRAGMENT", "Composite type examples, bare type expressions"),
    428: ("FRAGMENT", "Array literal examples, bare let bindings (#513)"),
    444: ("FRAGMENT", "Tuple construction + destructuring example, bare let + match"),
    455: ("FRAGMENT", "Type alias examples"),

    # Control flow — bare expressions
    533: ("FRAGMENT", "If/else expression example"),
    547: ("FRAGMENT", "Block expression example"),
    601: ("FRAGMENT", "Typed hole fill-in example, bare if/else expression"),

    # Closures and combinators
    646: ("FRAGMENT", "Closure example, bare let bindings with array_map (#513)"),
    696: ("FRAGMENT", "Pair-type capture example (post-#535), bare let-in-closure"),
    # Note: the prior "BROKEN/WORKING fill_row workaround" entry at line 721
    # was removed in v0.0.121 along with the SKILL "Known limitation: nested
    # closures" subsection — nested closures now work end-to-end (#514).
    # The pair-type capture example was reframed in v0.0.134 from "BROKEN"
    # to "this works as expected" once #535 closed; the underlying bare-
    # let-in-closure shape stays a FRAGMENT either way.

    # Option/Result combinator examples — bare function calls
    768: ("FRAGMENT", "Option/Result combinator usage examples, bare calls"),

    # Built-in usage examples — bare function calls grouped by domain
    796: ("FRAGMENT", "Array built-in examples, bare calls"),
    826: ("FRAGMENT", "Map built-in examples, bare calls"),
    843: ("FRAGMENT", "Set built-in examples, bare calls"),
    857: ("FRAGMENT", "Decimal built-in examples, bare calls"),
    880: ("FRAGMENT", "JSON parse/stringify/get examples, bare calls"),
    893: ("FRAGMENT", "JSON match expression example, bare expression"),
    910: ("FRAGMENT", "JSON typed accessor examples (#366), bare calls"),
    929: ("FRAGMENT", "JSON Layer-2 compound accessor example, bare match"),
    941: ("FRAGMENT", "String built-in examples, bare calls"),
    985: ("FRAGMENT", "String interpolation examples, bare expressions"),
    997: ("FRAGMENT", "String search built-in examples, bare calls"),
    1008: ("FRAGMENT", "String transformation built-in examples, bare calls"),
    1020: ("FRAGMENT", "String utility / classifier signatures (#470, #471), bare calls"),

    # Markdown / HTML / Regex built-in usage examples
    1056: ("FRAGMENT", "md_parse / md_render signatures, bare calls"),
    1092: ("FRAGMENT", "HTML built-in examples (html_parse/html_query/etc.), bare calls"),
    1108: ("FRAGMENT", "HTML constructor match expression, bare expression"),
    1123: ("FRAGMENT", "Regex built-in examples, bare calls"),
    1134: ("FRAGMENT", "Regex Result matching example, bare expression"),

    # Numeric + math built-ins
    1146: ("FRAGMENT", "Numeric built-in examples, bare calls"),
    1161: ("FRAGMENT", "Math built-in examples (log/trig/constants/clamp), bare calls"),
    1183: ("FRAGMENT", "Type conversions, bare calls"),
    1198: ("FRAGMENT", "Float64 predicate and constant examples, bare calls"),

    # Contracts
    1227: ("FRAGMENT", "Requires clause example, not full function"),
    1236: ("FRAGMENT", "Ensures clause example, not full function"),
    1266: ("FRAGMENT", "Contracts scaffolding template"),
    1286: ("FRAGMENT", "Quantified expression examples, bare calls"),

    # Effect declarations and handlers
    1304: ("FRAGMENT", "Effect declarations list"),
    1437: ("FRAGMENT", "Async effect row declarations, bare clauses"),
    1500: ("FRAGMENT", "Http effect declarations list"),
    1531: ("FRAGMENT", "Inference effect declarations list"),
    1623: ("FRAGMENT", "Handler with-clause pseudocode, bare expression"),
    1635: ("FRAGMENT", "Handler with-clause, bare put arm expression"),
    1645: ("FRAGMENT", "Qualified effect calls (State.put, Logger.put)"),

    # Escape sequences and string construction
    1849: ("FRAGMENT", "ANSI cursor-home via string_from_char_code (#513)"),
    1862: ("FRAGMENT", "Comment syntax example"),

    # Common mistakes section — intentionally wrong code
    1941: ("FRAGMENT", "Wrong: missing contracts"),
    1961: ("FRAGMENT", "Wrong: missing effects clause (with contracts)"),
    # Note: line 1905 is the CORRECT add-with-effects full function (parses OK,
    # not allowlisted).  The "Wrong: bare @Int + @Int without indices" entry
    # used to be parked here by mistake; the bare-add code is actually at 1942.
    2008: ("FRAGMENT", "Wrong: bare @Int + @Int without indices"),
    2013: ("FRAGMENT", "Correct: indexed slot arithmetic"),
    1995: ("FRAGMENT", "Correct: bare @Int + @Int (common mistakes)"),
    2103: ("FRAGMENT", "Wrong: non-exhaustive match (missing arm)"),
    2110: ("FRAGMENT", "Correct: match with Option arms (bare)"),
    2120: ("FRAGMENT", "Wrong: missing braces on if/else branches"),
    2125: ("FRAGMENT", "Correct: if/else with braces (common mistakes)"),

    # Import syntax — intentionally unsupported
    2136: ("FRAGMENT", "Wrong: import aliasing not supported"),
    2141: ("FRAGMENT", "Correct: import syntax example"),
    2151: ("FRAGMENT", "Wrong: import hiding not supported"),
    2170: ("FRAGMENT", "Correct escape sequence examples, bare strings"),
    2178: ("FRAGMENT", "Wrong: standalone map_new/set_new without type context"),
    2184: ("FRAGMENT", "Correct: map_new/set_new with type context"),

    # =================================================================
    # MISMATCH — uses syntax the parser doesn't handle in isolation.
    # =================================================================

    # Function template with placeholders
    154: ("MISMATCH", "Function signature template with @ParamType placeholders"),
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
