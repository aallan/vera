#!/usr/bin/env python
"""Extract code blocks from spec Markdown and verify parseable ones still parse.

Strategy:
  1. Extract all fenced code blocks from spec/*.md files.
  2. Skip blocks tagged as non-Vera (```ebnf, ```bash, ```python, etc.).
  3. Classify remaining blocks:
     - "parseable": starts with a top-level keyword (fn, data, effect, type, forall,
       module, import, public, private) or a comment (--) followed by one.
     - "fragment": everything else (type annotations, expressions, partial syntax).
  4. Try to parse each "parseable" block with the Vera parser.
  5. Report failures. Maintain an allowlist for known-unparseable blocks.

The allowlist uses (filename, line_number) tuples so failures are stable
across spec edits. When a spec is updated and line numbers shift, the
allowlist must be updated too — this is intentional, it forces you to
re-examine whether the block should still be skipped.

Categories:
  FUTURE   — design proposals using syntax not yet in the parser
  MISMATCH — spec uses @T notation in data/effect declarations but parser
             expects bare types; tracked for reconciliation
  FRAGMENT — heuristic false positive (looks like a declaration but isn't)
"""

import re
import sys
from pathlib import Path

# -- Allowlist: spec blocks that are intentionally unparseable. ----------
#
# Each entry is (spec_filename, start_line_of_code_fence, category).
#
# Update this list when:
#   - A spec edit shifts line numbers (CI will tell you).
#   - A parser improvement makes a previously-unparseable block parseable
#     (remove it from the list — this is progress!).
#   - A new design note adds intentionally-unparseable code (add it).

ALLOWLIST: dict[tuple[str, int], str] = {
    # =================================================================
    # FUTURE — design notes using syntax not yet in the parser
    # =================================================================

    # Chapter 0 — Section 0.8 design notes (abilities, async, inference)
    ("00-introduction.md", 158): "FUTURE",   # JSON ADT
    ("00-introduction.md", 175): "FUTURE",   # fetch_both async example
    # Note: 00-introduction.md abilities block (~line 203) starts with
    # "ability" keyword, which the heuristic correctly skips as a fragment
    # since abilities aren't in the parser yet.
    ("00-introduction.md", 238): "FUTURE",   # effect Inference + fn classify

    # Chapter 2 — type constraint syntax (post-v0.1)
    ("02-types.md", 250): "FUTURE",          # forall<T where Ord<T>> fn sort

    # =================================================================
    # MISMATCH — spec uses @T in data/effect ops, parser expects bare T
    # These are tracked for reconciliation. When the spec or parser is
    # updated to match, remove the entry and the block should parse.
    # =================================================================

    # Chapter 2 — data declarations with @T constructor params
    ("02-types.md", 62): "MISMATCH",    # data Option<T> { Some(@T), None }
    ("02-types.md", 79): "MISMATCH",    # data Result<T, E> { Ok(@T), Err(@E) }
    ("02-types.md", 92): "MISMATCH",    # data List<T> { Cons(@T, @List<T>), Nil }
    ("02-types.md", 99): "MISMATCH",    # data Tree<T> { Leaf(@T), Node(...) }
    ("02-types.md", 106): "MISMATCH",   # data Color { Red, Green, Blue }
    ("02-types.md", 129): "MISMATCH",   # data SortedList<T> invariant(...)
    ("02-types.md", 215): "MISMATCH",   # type aliases with refinements

    # Chapter 3 — functions using non-canonical generic syntax or @T ops
    ("03-slot-references.md", 238): "MISMATCH",  # fn map_array<A,B> (non-canonical)
    ("03-slot-references.md", 253): "MISMATCH",  # data + fn list_head<T> (non-canonical)
    ("03-slot-references.md", 327): "MISMATCH",  # type alias + fn apply_to_array
    ("03-slot-references.md", 343): "MISMATCH",  # type alias + anonymous fn

    # Chapter 5 — closures and effect-polymorphic functions
    ("05-functions.md", 203): "MISMATCH",   # fn make_adder returning closure
    ("05-functions.md", 219): "MISMATCH",   # type alias + fn filter_positive
    ("05-functions.md", 277): "MISMATCH",   # forall<A,B> fn map_option effects(<E>)

    # Chapter 6 — data with invariant, type alias + fn
    ("06-contracts.md", 48): "MISMATCH",    # data SortedArray invariant(...)
    ("06-contracts.md", 308): "MISMATCH",   # type SafeDiv = Fn(...) + fn apply_div

    # Chapter 7 — effect declarations and handlers
    ("07-effects.md", 18): "MISMATCH",    # effect State<T> { op get(@Unit -> @T) }
    ("07-effects.md", 25): "MISMATCH",    # effect Exn<E> { op throw(@E -> @Never) }
    ("07-effects.md", 31): "MISMATCH",    # effect IO { op print(@String -> @Unit) }
    ("07-effects.md", 38): "MISMATCH",    # effect Choice { op choose(...) }
    ("07-effects.md", 117): "MISMATCH",   # effect Logger + qualified ops
    ("07-effects.md", 182): "MISMATCH",   # fn run_stateful handle[State<Int>]
    ("07-effects.md", 204): "MISMATCH",   # fn safe_parse handle[Exn<String>]
    ("07-effects.md", 224): "MISMATCH",   # fn all_choices handle[Choice]
    ("07-effects.md", 251): "MISMATCH",   # forall<A,B> fn map_option effects(<E>)
    ("07-effects.md", 270): "MISMATCH",   # forall<A> fn with_logging effects(<IO,E>)
    ("07-effects.md", 289): "MISMATCH",   # effect IO (extended, with file ops)
    ("07-effects.md", 302): "MISMATCH",   # effect Exn<E> (duplicate)
    ("07-effects.md", 312): "MISMATCH",   # effect Diverge {}
    ("07-effects.md", 320): "MISMATCH",   # effect Alloc {}

    # =================================================================
    # FRAGMENT — heuristic false positives (look like declarations but
    # are templates, keyword listings, or partial syntax)
    # =================================================================

    # Chapter 1 — keyword listing table
    ("01-lexical-structure.md", 45): "FRAGMENT",  # "fn  let  if  then ..."

    # Chapter 4 — type alias + bare let statement (not top-level)
    ("04-expressions.md", 130): "FRAGMENT",  # type alias + let @PosInt = 42

    # Chapter 5 — template with metavariable placeholders
    ("05-functions.md", 19): "FRAGMENT",  # fn function_name(@ParamType1 ...)
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


# Keywords that begin a top-level Vera declaration.
_TOP_LEVEL_RE = re.compile(
    r"^\s*(?:--.*\n\s*)*"  # optional leading comments
    r"(?:public\s+|private\s+)?"  # optional visibility
    r"(?:fn\s|data\s|effect\s|type\s|forall\s*<|module\s|import\s)"
)


def is_parseable_block(content: str) -> bool:
    """Heuristic: does this block look like it contains top-level declarations?"""
    # Must have substance
    stripped = content.strip()
    if not stripped:
        return False

    # Check if any line starts with a top-level keyword
    return bool(_TOP_LEVEL_RE.search(stripped))


def try_parse(content: str) -> str | None:
    """Try to parse content as a Vera program. Returns error message or None."""
    from vera.parser import parse

    try:
        parse(content, file="<spec>")
        return None
    except Exception as exc:
        # Return just the first line of the error
        return str(exc).split("\n")[0][:200]


def main() -> int:
    root = Path(__file__).resolve().parent.parent
    spec_dir = root / "spec"

    if not spec_dir.is_dir():
        print("ERROR: spec/ directory not found.", file=sys.stderr)
        return 1

    spec_files = sorted(spec_dir.glob("*.md"))
    if not spec_files:
        print("ERROR: No spec files found.", file=sys.stderr)
        return 1

    # Non-Vera language tags to skip entirely
    skip_langs = {"ebnf", "bash", "python", "json", "toml", "yaml", "shell", "sh"}

    total_blocks = 0
    parseable_blocks = 0
    skipped_fragments = 0
    skipped_lang = 0
    skipped_future = 0
    skipped_mismatch = 0
    skipped_fragment_allowlist = 0
    passed = 0
    stale_allowlist: list[tuple[str, int, str]] = []
    failures: list[tuple[str, int, str]] = []

    # Track which allowlist entries are used
    used_allowlist: set[tuple[str, int]] = set()

    for spec_file in spec_files:
        filename = spec_file.name
        blocks = extract_code_blocks(spec_file)

        for line_no, lang, content in blocks:
            total_blocks += 1

            # Skip non-Vera languages
            if lang.lower() in skip_langs:
                skipped_lang += 1
                continue

            # Skip fragments (expressions, type annotations, etc.)
            if not is_parseable_block(content):
                skipped_fragments += 1
                continue

            parseable_blocks += 1

            # Check allowlist
            key = (filename, line_no)
            if key in ALLOWLIST:
                used_allowlist.add(key)
                category = ALLOWLIST[key]
                if category == "FUTURE":
                    skipped_future += 1
                elif category == "MISMATCH":
                    skipped_mismatch += 1
                elif category == "FRAGMENT":
                    skipped_fragment_allowlist += 1
                continue

            # Try to parse
            error = try_parse(content)
            if error is None:
                passed += 1
            else:
                failures.append((filename, line_no, error))

    # Check for stale allowlist entries (entries that no longer correspond
    # to a code block at that line — means spec was edited)
    for key, category in ALLOWLIST.items():
        if key not in used_allowlist:
            stale_allowlist.append((key[0], key[1], category))

    # Report
    print(f"Spec code blocks: {total_blocks} total")
    print(f"  Skipped (non-Vera language): {skipped_lang}")
    print(f"  Skipped (fragments, heuristic): {skipped_fragments}")
    print(f"  Parseable: {parseable_blocks}")
    print(f"    Parsed OK: {passed}")
    print(f"    Allowlisted (future syntax): {skipped_future}")
    print(f"    Allowlisted (spec/parser mismatch): {skipped_mismatch}")
    print(f"    Allowlisted (fragment override): {skipped_fragment_allowlist}")
    print(f"    FAILED: {len(failures)}")

    exit_code = 0

    if stale_allowlist:
        print("\nSTALE ALLOWLIST ENTRIES:", file=sys.stderr)
        print(
            "These entries no longer match a code block (spec was edited?):",
            file=sys.stderr,
        )
        for filename, line_no, category in stale_allowlist:
            print(
                f"  spec/{filename} line {line_no} [{category}]", file=sys.stderr
            )
        print(
            "\nUpdate the ALLOWLIST in scripts/check_spec_examples.py.",
            file=sys.stderr,
        )
        exit_code = 1

    if failures:
        print("\nFAILURES:", file=sys.stderr)
        for filename, line_no, error in failures:
            print(f"\n  spec/{filename} line {line_no}:", file=sys.stderr)
            print(f"    {error}", file=sys.stderr)
        print(
            f"\n{len(failures)} spec code block(s) failed to parse.",
            file=sys.stderr,
        )
        print(
            "If a block is intentionally unparseable, add it to the ALLOWLIST",
            file=sys.stderr,
        )
        print(
            "in scripts/check_spec_examples.py with the appropriate category.",
            file=sys.stderr,
        )
        exit_code = 1

    if exit_code == 0:
        print("\nAll parseable spec code blocks pass.")

    return exit_code


if __name__ == "__main__":
    sys.exit(main())
