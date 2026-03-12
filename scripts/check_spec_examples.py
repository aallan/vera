#!/usr/bin/env python
"""Extract code blocks from spec Markdown and validate them through the compiler pipeline.

Strategy:
  1. Extract all fenced code blocks from spec/*.md files.
  2. Skip blocks tagged as non-Vera (```ebnf, ```bash, ```python, etc.).
  3. Classify remaining blocks:
     - "parseable": starts with a top-level keyword (fn, data, effect, type, forall,
       module, import, public, private) or a comment (--) followed by one.
     - "fragment": everything else (type annotations, expressions, partial syntax).
  4. Try to parse each "parseable" block with the Vera parser.
  5. Try to type-check each block that parsed successfully.
  6. Try to verify contracts on each block that type-checked successfully.
  7. Report failures. Maintain allowlists for known failures at each stage.

The allowlists use (filename, line_number) tuples so failures are stable
across spec edits. When a spec is updated and line numbers shift, the
allowlists must be updated too — this is intentional, it forces you to
re-examine whether the block should still be skipped.

Parse allowlist categories:
  FUTURE   — design proposals using syntax not yet in the parser
  MISMATCH — spec uses @T notation in data/effect declarations but parser
             expects bare types; tracked for reconciliation
  FRAGMENT — heuristic false positive (looks like a declaration but isn't)

Check allowlist categories:
  INCOMPLETE  — references functions/types not defined in the block
  FUTURE      — uses checker features not yet implemented
  ILLUSTRATIVE — demonstrates a concept but isn't a complete checkable program

Verify allowlist categories:
  INCOMPLETE — contracts reference undefined functions
  EXPECTED   — verification errors that are intentional in the spec context
"""

import re
import sys
from pathlib import Path

# -- Parse allowlist: spec blocks that are intentionally unparseable. ------
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

    # Chapter 2 — type constraint syntax (post-v0.1)
    ("02-types.md", 250): "FUTURE",          # forall<T where Ord<T>> fn sort

    # Chapter 9 — future stdlib features and signature-only blocks
    ("09-standard-library.md", 417): "FUTURE",   # fn classify — uses ++ (string concat)

    # Chapter 9 — Array builtin signatures (no body)
    ("09-standard-library.md", 431): "FRAGMENT",  # array_length signature (no body)
    ("09-standard-library.md", 451): "FRAGMENT",  # array_append signature (no body)
    ("09-standard-library.md", 469): "FRAGMENT",  # array_range signature (no body)
    ("09-standard-library.md", 487): "FRAGMENT",  # array_concat signature (no body)

    # Chapter 9 — Numeric/string/encoding builtin signatures (no body)
    ("09-standard-library.md", 594): "FRAGMENT",  # round signature (no body)
    ("09-standard-library.md", 611): "FRAGMENT",  # sqrt signature (no body)
    ("09-standard-library.md", 628): "FRAGMENT",  # pow signature (no body)
    # (byte_to_int moved to line 679, now in the type conversion group below)
    ("09-standard-library.md", 853): "FRAGMENT",  # ends_with signature (no body)
    ("09-standard-library.md", 1116): "FRAGMENT",  # base64_decode signature (no body)
    ("09-standard-library.md", 1245): "FRAGMENT",  # regex_match signature (no body)
    ("09-standard-library.md", 1261): "FRAGMENT",  # regex_find signature (no body)
    ("09-standard-library.md", 1277): "FRAGMENT",  # regex_find_all signature (no body)
    ("09-standard-library.md", 1293): "FRAGMENT",  # regex_replace signature (no body)

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

    # =================================================================
    # FRAGMENT — spec examples using syntax the parser doesn't support
    # (generics without forall, empty effects, anonymous top-level
    # functions, inline function types in params)
    # =================================================================

    # Chapter 3 — generic functions without forall keyword
    ("03-slot-references.md", 238): "FRAGMENT",  # fn map_array<A,B>(...) — needs forall
    ("03-slot-references.md", 253): "FRAGMENT",  # fn list_head<T>(...) — needs forall

    # Chapter 3 — anonymous function at top level
    ("03-slot-references.md", 343): "FRAGMENT",  # fn(@PosInt, @Int -> @Int) — no name

    # Chapter 5 — inline function types in return/param position
    ("05-functions.md", 211): "FRAGMENT",   # fn make_adder returns fn(...) inline
    ("05-functions.md", 324): "FRAGMENT",   # fn(A -> B) in param position

    # Chapter 6 — inline function type in type alias
    ("06-contracts.md", 312): "FRAGMENT",   # type SafeDiv = fn(...) + fn apply_div

    # Chapter 7 — anonymous function at top level
    ("07-effects.md", 116): "FRAGMENT",     # effect Logger + anonymous fn body

    # Chapter 7 — multi-shot resume + array_concat (future)
    ("07-effects.md", 222): "FUTURE",       # handle[Choice] multi-shot resume + array_concat

    # Chapter 7 — inline function types in generic params
    ("07-effects.md", 249): "FRAGMENT",     # fn(A -> B) in param position
    ("07-effects.md", 268): "FRAGMENT",     # fn(Unit -> A) in param position

    # Chapter 7 — empty effect bodies (parser requires op_decl+)
    ("07-effects.md", 315): "FRAGMENT",     # effect Diverge {} — no operations

    # Chapter 9 — Async builtin signatures (no body)
    ("09-standard-library.md", 367): "FRAGMENT",  # async/await signatures (no body)

    # Chapter 9 — Numeric builtin signatures (no body)
    ("09-standard-library.md", 509): "FRAGMENT",  # abs signature (no body)
    ("09-standard-library.md", 526): "FRAGMENT",  # min signature (no body)
    ("09-standard-library.md", 543): "FRAGMENT",  # max signature (no body)
    ("09-standard-library.md", 560): "FRAGMENT",  # floor signature (no body)
    ("09-standard-library.md", 577): "FRAGMENT",  # ceil signature (no body)

    # Chapter 9 — Numeric type conversion signatures (no body)
    ("09-standard-library.md", 649): "FRAGMENT",  # to_float signature (no body)
    ("09-standard-library.md", 664): "FRAGMENT",  # nat_to_int signature (no body)
    ("09-standard-library.md", 679): "FRAGMENT",  # byte_to_int signature (no body)
    ("09-standard-library.md", 694): "FRAGMENT",  # float_to_int signature (no body)
    ("09-standard-library.md", 709): "FRAGMENT",  # int_to_nat signature (no body)
    ("09-standard-library.md", 727): "FRAGMENT",  # int_to_byte signature (no body)

    # Chapter 9 — Float64 predicates (signatures, no body)
    ("09-standard-library.md", 751): "FRAGMENT",  # is_nan signature (no body)
    ("09-standard-library.md", 768): "FRAGMENT",  # is_infinite signature (no body)
    ("09-standard-library.md", 787): "FRAGMENT",  # nan signature (no body)
    ("09-standard-library.md", 802): "FRAGMENT",  # infinity signature (no body)

    # Chapter 9 — String search signatures (no body)
    ("09-standard-library.md", 823): "FRAGMENT",  # string_contains signature (no body)
    ("09-standard-library.md", 838): "FRAGMENT",  # starts_with signature (no body)
    ("09-standard-library.md", 868): "FRAGMENT",  # index_of signature (no body)

    # Chapter 9 — String transformation signatures (no body)
    ("09-standard-library.md", 889): "FRAGMENT",  # to_upper signature (no body)
    ("09-standard-library.md", 904): "FRAGMENT",  # to_lower signature (no body)
    ("09-standard-library.md", 919): "FRAGMENT",  # replace signature (no body)
    ("09-standard-library.md", 935): "FRAGMENT",  # split signature (no body)
    ("09-standard-library.md", 950): "FRAGMENT",  # join signature (no body)
    ("09-standard-library.md", 964): "FRAGMENT",  # from_char_code signature (no body)
    ("09-standard-library.md", 979): "FRAGMENT",  # string_repeat signature (no body)

    # Chapter 9 — Parsing function signatures (no body)
    ("09-standard-library.md", 1007): "FRAGMENT",  # parse_nat signature (no body)
    ("09-standard-library.md", 1029): "FRAGMENT",  # parse_int signature (no body)
    ("09-standard-library.md", 1052): "FRAGMENT",  # parse_float64 signature (no body)
    ("09-standard-library.md", 1074): "FRAGMENT",  # parse_bool signature (no body)

    # Chapter 9 — Base64 builtin signatures (no body)
    ("09-standard-library.md", 1097): "FRAGMENT",  # base64_encode signature (no body)

    # Chapter 9 — URL encoding builtin signatures (no body)
    ("09-standard-library.md", 1143): "FRAGMENT",  # url_encode signature (no body)
    ("09-standard-library.md", 1162): "FRAGMENT",  # url_decode signature (no body)

    # Chapter 9 — URL parsing builtin signatures (no body)
    ("09-standard-library.md", 1188): "FRAGMENT",  # url_parse signature (no body)
    ("09-standard-library.md", 1208): "FRAGMENT",  # url_join signature (no body)

    # Chapter 9 — ML/vector builtin signatures (no body)
    ("09-standard-library.md", 1228): "FRAGMENT",  # similarity signature (no body)

    # Chapter 9 — Markdown stdlib type (future, uses MdBlock/MdInline types)
    ("09-standard-library.md", 1400): "FUTURE",   # md_parse
    ("09-standard-library.md", 1409): "FUTURE",   # md_render
    ("09-standard-library.md", 1420): "FUTURE",   # md_has_heading
    ("09-standard-library.md", 1429): "FUTURE",   # md_has_code_block
    ("09-standard-library.md", 1438): "FUTURE",   # md_extract_code_blocks
    ("09-standard-library.md", 1462): "FUTURE",   # convert_to_markdown
}


# -- Check allowlist: blocks that parse OK but fail type-checking. ---------
#
# Populated by running with --discover-check to find blocks that parse
# but don't type-check. Each entry documents why the block is expected
# to fail the checker.

CHECK_ALLOWLIST: dict[tuple[str, int], str] = {
    # =================================================================
    # INCOMPLETE — references functions, types, or effects not defined
    # in the block. These are illustrative snippets that depend on
    # external definitions (stdlib, other modules, etc.).
    # =================================================================

    # Chapter 2 — ADT invariant referencing undefined predicate
    ("02-types.md", 129): "INCOMPLETE",      # is_sorted in SortedList invariant

    # Chapter 2 — Tuple constructor (not a built-in ADT)
    ("02-types.md", 230): "INCOMPLETE",      # forall<A,B> fn swap uses Tuple

    # Chapter 3 — undefined stdlib function array_map
    ("03-slot-references.md", 327): "INCOMPLETE",  # array_map in apply_to_array

    # Chapter 5 — undefined stdlib function array_filter
    ("05-functions.md", 227): "INCOMPLETE",  # array_filter in filter_positive

    # Chapter 5 — Tuple constructor (not a built-in ADT)
    ("05-functions.md", 308): "INCOMPLETE",  # forall<A,B> fn pair uses Tuple

    # Chapter 6 — undefined predicate in data invariant
    ("06-contracts.md", 52): "INCOMPLETE",   # is_sorted_impl in SortedArray

    # Chapter 7 — effect composition referencing undefined functions
    ("07-effects.md", 367): "INCOMPLETE",    # fn foo calls undefined bar/baz

    # Chapter 8 — cross-module imports (imported modules don't exist)
    ("08-modules.md", 151): "INCOMPLETE",    # import vera.math(abs, max)
    ("08-modules.md", 322): "INCOMPLETE",    # import vera.math(abs)
    ("08-modules.md", 415): "INCOMPLETE",    # import vera.math + vera.collections

    # =================================================================
    # FUTURE — uses features not yet implemented in the checker
    # =================================================================

    # Chapter 7 — Exn handler references parse_int (not defined in block)
    ("07-effects.md", 202): "INCOMPLETE",    # handle[Exn<String>] + parse_int

    # Chapter 9 — Http + Async composition example (Http not yet implemented)
    ("09-standard-library.md", 347): "INCOMPLETE",  # fetch_both uses Http.get (future)

    # Chapter 9 — Future<T> type definition (standalone, no visibility)
    ("09-standard-library.md", 103): "INCOMPLETE",  # data Future<T> (no visibility keyword)

    # Chapter 9 — UrlParts type definition (standalone, no visibility)
    ("09-standard-library.md", 88): "INCOMPLETE",  # data UrlParts (no visibility keyword)
}


# -- Verify allowlist: blocks that type-check but fail verification. -------
#
# Populated by running with --discover-verify to find blocks that
# type-check but don't verify cleanly.

VERIFY_ALLOWLIST: dict[tuple[str, int], str] = {
    # =================================================================
    # ILLUSTRATIVE — spec example demonstrating syntax; the contract
    # is intentionally loose and Z3 cannot prove it.
    # =================================================================

    # Chapter 5 — multiple postconditions example; @Int.result <= @Int.0
    # doesn't hold for all valid inputs under integer division semantics.
    # The block demonstrates multiple requires/ensures syntax, not
    # contract correctness.
    ("05-functions.md", 49): "ILLUSTRATIVE",  # safe_divide with imprecise ensures
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


def try_check(content: str) -> str | None:
    """Parse, transform, and type-check. Returns error message or None."""
    from vera.parser import parse
    from vera.transform import transform
    from vera.checker import typecheck

    try:
        tree = parse(content, file="<spec>")
        program = transform(tree)
        errors = typecheck(program, source=content, file="<spec>")
        if errors:
            return errors[0].description[:200]
        return None
    except Exception as exc:
        return str(exc).split("\n")[0][:200]


def try_verify(content: str) -> str | None:
    """Parse, transform, type-check, and verify. Returns error message or None."""
    from vera.parser import parse
    from vera.transform import transform
    from vera.checker import typecheck
    from vera.verifier import verify

    try:
        tree = parse(content, file="<spec>")
        program = transform(tree)
        errors = typecheck(program, source=content, file="<spec>")
        if errors:
            return errors[0].description[:200]
        result = verify(program, source=content, file="<spec>")
        errs = [d for d in result.diagnostics if d.severity == "error"]
        if errs:
            return errs[0].description[:200]
        return None
    except Exception as exc:
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
    skip_langs = {"ebnf", "bash", "python", "json", "toml", "yaml", "shell", "sh", "javascript"}

    # -- Parse stage counters --
    total_blocks = 0
    parseable_blocks = 0
    skipped_fragments = 0
    skipped_lang = 0
    skipped_future = 0
    skipped_mismatch = 0
    skipped_fragment_allowlist = 0
    parse_passed = 0
    parse_failures: list[tuple[str, int, str]] = []

    # -- Check stage counters --
    check_passed = 0
    check_allowlisted = 0
    check_failures: list[tuple[str, int, str]] = []

    # -- Verify stage counters --
    verify_passed = 0
    verify_allowlisted = 0
    verify_failures: list[tuple[str, int, str]] = []

    # Track which allowlist entries are used
    used_allowlist: set[tuple[str, int]] = set()
    used_check_allowlist: set[tuple[str, int]] = set()
    used_verify_allowlist: set[tuple[str, int]] = set()

    # Collect blocks that parsed OK for the check stage
    parsed_ok: list[tuple[str, int, str]] = []  # (filename, line_no, content)

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

            # Check parse allowlist
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
                parse_passed += 1
                parsed_ok.append((filename, line_no, content))
            else:
                parse_failures.append((filename, line_no, error))

    # -- Check stage: type-check blocks that parsed OK --
    checked_ok: list[tuple[str, int, str]] = []  # (filename, line_no, content)

    for filename, line_no, content in parsed_ok:
        key = (filename, line_no)
        if key in CHECK_ALLOWLIST:
            used_check_allowlist.add(key)
            check_allowlisted += 1
            continue

        error = try_check(content)
        if error is None:
            check_passed += 1
            checked_ok.append((filename, line_no, content))
        else:
            check_failures.append((filename, line_no, error))

    # -- Verify stage: verify blocks that type-checked OK --
    for filename, line_no, content in checked_ok:
        key = (filename, line_no)
        if key in VERIFY_ALLOWLIST:
            used_verify_allowlist.add(key)
            verify_allowlisted += 1
            continue

        error = try_verify(content)
        if error is None:
            verify_passed += 1
        else:
            verify_failures.append((filename, line_no, error))

    # -- Stale allowlist detection --
    stale_entries: list[tuple[str, int, str, str]] = []  # (file, line, cat, stage)

    for key, category in ALLOWLIST.items():
        if key not in used_allowlist:
            stale_entries.append((key[0], key[1], category, "parse"))

    for key, category in CHECK_ALLOWLIST.items():
        if key not in used_check_allowlist:
            stale_entries.append((key[0], key[1], category, "check"))

    for key, category in VERIFY_ALLOWLIST.items():
        if key not in used_verify_allowlist:
            stale_entries.append((key[0], key[1], category, "verify"))

    # -- Report --
    print(f"Spec code blocks: {total_blocks} total")
    print(f"  Skipped (non-Vera language): {skipped_lang}")
    print(f"  Skipped (fragments, heuristic): {skipped_fragments}")
    print(f"  Parseable: {parseable_blocks}")
    print(f"    Parsed OK: {parse_passed}")
    print(f"    Allowlisted (future syntax): {skipped_future}")
    print(f"    Allowlisted (spec/parser mismatch): {skipped_mismatch}")
    print(f"    Allowlisted (fragment override): {skipped_fragment_allowlist}")
    print(f"    PARSE FAILED: {len(parse_failures)}")
    print(f"  Type-checked: {parse_passed}")
    print(f"    Check OK: {check_passed}")
    print(f"    Allowlisted (check): {check_allowlisted}")
    print(f"    CHECK FAILED: {len(check_failures)}")
    print(f"  Verified: {check_passed}")
    print(f"    Verify OK: {verify_passed}")
    print(f"    Allowlisted (verify): {verify_allowlisted}")
    print(f"    VERIFY FAILED: {len(verify_failures)}")

    exit_code = 0

    if stale_entries:
        print("\nSTALE ALLOWLIST ENTRIES:", file=sys.stderr)
        print(
            "These entries no longer match a code block (spec was edited?):",
            file=sys.stderr,
        )
        for filename, line_no, category, stage in stale_entries:
            print(
                f"  spec/{filename} line {line_no} [{category}] ({stage} stage)",
                file=sys.stderr,
            )
        print(
            "\nRun: python scripts/fix_allowlists.py --fix",
            file=sys.stderr,
        )
        exit_code = 1

    if parse_failures:
        print("\nPARSE FAILURES:", file=sys.stderr)
        for filename, line_no, error in parse_failures:
            print(f"\n  spec/{filename} line {line_no}:", file=sys.stderr)
            print(f"    {error}", file=sys.stderr)
        print(
            f"\n{len(parse_failures)} spec code block(s) failed to parse.",
            file=sys.stderr,
        )
        exit_code = 1

    if check_failures:
        print("\nCHECK FAILURES:", file=sys.stderr)
        for filename, line_no, error in check_failures:
            print(f"\n  spec/{filename} line {line_no}:", file=sys.stderr)
            print(f"    {error}", file=sys.stderr)
        print(
            f"\n{len(check_failures)} spec code block(s) failed to type-check.",
            file=sys.stderr,
        )
        exit_code = 1

    if verify_failures:
        print("\nVERIFY FAILURES:", file=sys.stderr)
        for filename, line_no, error in verify_failures:
            print(f"\n  spec/{filename} line {line_no}:", file=sys.stderr)
            print(f"    {error}", file=sys.stderr)
        print(
            f"\n{len(verify_failures)} spec code block(s) failed to verify.",
            file=sys.stderr,
        )
        exit_code = 1

    if exit_code == 0:
        print("\nAll parseable spec code blocks pass (parse + check + verify).")

    return exit_code


if __name__ == "__main__":
    sys.exit(main())
