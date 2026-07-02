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
  7. Report failures.

Blocks that intentionally fail a stage carry an inline annotation on the
line immediately before the fence (#538; see scripts/doc_annotations.py):

    <!-- vera:skip-parse category="FUTURE" reason="post-v0.1 syntax" -->
    <!-- vera:skip-check category="INCOMPLETE" reason="uses external fn" -->
    <!-- vera:skip-verify category="ILLUSTRATIVE" reason="loose contract" -->

The annotation travels with the fence through spec edits, so there are no
line numbers to maintain.  The gate still runs the exempted stage: an
annotated block that PASSES that stage is a STALE annotation and fails the
gate (remove the annotation — this is progress!).  Malformed or dangling
annotations fail the gate too.

Annotation categories in use:
  FUTURE       — design proposals using syntax/features not yet implemented
  MISMATCH     — spec uses @T notation in data/effect declarations but parser
                 expects bare types; tracked for reconciliation
  FRAGMENT     — looks like a declaration to the heuristic but isn't a
                 complete parseable program (signatures without bodies, etc.)
  INCOMPLETE   — parses, but references functions/types not defined in the
                 block (stdlib signatures, cross-module imports, etc.)
  ILLUSTRATIVE — demonstrates syntax; the contract is intentionally loose
                 and Z3 cannot prove it
"""

import sys
import re
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from doc_annotations import (  # noqa: E402  (scripts/ is not a package)
    evaluate_block,
    scan_markdown,
)


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
        diags = typecheck(program, source=content, file="<spec>")
        # Warnings (e.g. W001 for a typed hole) are not check failures — the
        # CLI `vera check` exits 0 on them, and try_verify already filters to
        # error severity.  Only error-severity diagnostics fail the check stage.
        errors = [d for d in diags if d.severity == "error"]
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
        diags = typecheck(program, source=content, file="<spec>")
        # Same warning-filter as try_check: a W001 typed-hole warning is not a
        # type error and must not fail the verify stage's type-check sub-step.
        type_errors = [d for d in diags if d.severity == "error"]
        if type_errors:
            return type_errors[0].description[:200]
        result = verify(program, source=content, file="<spec>")
        errs = [d for d in result.diagnostics if d.severity == "error"]
        if errs:
            return errs[0].description[:200]
        return None
    except Exception as exc:
        return str(exc).split("\n")[0][:200]


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
    skip_langs = {"ebnf", "bash", "python", "json", "toml", "yaml", "shell", "sh", "javascript", "text"}

    stage_runners = [
        ("parse", try_parse),
        ("check", try_check),
        ("verify", try_verify),
    ]

    # -- Counters --
    total_blocks = 0
    parseable_blocks = 0
    skipped_fragments = 0
    skipped_lang = 0
    skipped_annotated = {"parse": 0, "check": 0, "verify": 0}
    passed = {"parse": 0, "check": 0, "verify": 0}
    failures: dict[str, list[tuple[str, int, str]]] = {
        "parse": [],
        "check": [],
        "verify": [],
    }
    # (file, line, stage, category, reason)
    stale: list[tuple[str, int, str, str, str]] = []
    all_problems: list[str] = []

    for spec_file in spec_files:
        filename = spec_file.name
        blocks, problems = scan_markdown(spec_file)
        all_problems.extend(f"spec/{filename} {p}" for p in problems)

        for block in blocks:
            total_blocks += 1

            # Skip non-Vera languages
            if block.lang.lower() in skip_langs:
                if block.annotations:
                    all_problems.append(
                        f"spec/{filename} line {block.line}: vera:skip "
                        f"annotation on a non-Vera block "
                        f"(language {block.lang!r}) — remove it"
                    )
                skipped_lang += 1
                continue

            # Skip fragments (expressions, type annotations, etc.)
            if not is_parseable_block(block.content):
                if block.annotations:
                    all_problems.append(
                        f"spec/{filename} line {block.line}: vera:skip "
                        f"annotation on a block the fragment heuristic "
                        f"already skips — remove it"
                    )
                skipped_fragments += 1
                continue

            parseable_blocks += 1

            outcomes = evaluate_block(block, stage_runners)
            for outcome in outcomes:
                if outcome.status == "ok":
                    passed[outcome.stage] += 1
                elif outcome.status == "skipped":
                    skipped_annotated[outcome.stage] += 1
                elif outcome.status == "stale":
                    assert outcome.annotation is not None
                    stale.append(
                        (
                            filename,
                            block.line,
                            outcome.stage,
                            outcome.annotation.category,
                            outcome.annotation.reason,
                        )
                    )
                else:
                    failures[outcome.stage].append(
                        (filename, block.line, outcome.error or "")
                    )

    # -- Report --
    print(f"Spec code blocks: {total_blocks} total")
    print(f"  Skipped (non-Vera language): {skipped_lang}")
    print(f"  Skipped (fragments, heuristic): {skipped_fragments}")
    print(f"  Parseable: {parseable_blocks}")
    print(f"    Parsed OK: {passed['parse']}")
    print(f"    Annotated (vera:skip-parse): {skipped_annotated['parse']}")
    print(f"    PARSE FAILED: {len(failures['parse'])}")
    print(f"  Type-checked: {passed['parse']}")
    print(f"    Check OK: {passed['check']}")
    print(f"    Annotated (vera:skip-check): {skipped_annotated['check']}")
    print(f"    CHECK FAILED: {len(failures['check'])}")
    print(f"  Verified: {passed['check']}")
    print(f"    Verify OK: {passed['verify']}")
    print(f"    Annotated (vera:skip-verify): {skipped_annotated['verify']}")
    print(f"    VERIFY FAILED: {len(failures['verify'])}")

    exit_code = 0

    if all_problems:
        print("\nANNOTATION PROBLEMS:", file=sys.stderr)
        for problem in all_problems:
            print(f"  {problem}", file=sys.stderr)
        exit_code = 1

    if stale:
        print("\nSTALE ANNOTATIONS:", file=sys.stderr)
        print(
            "These blocks now pass the stage they are exempted from — "
            "remove the annotation (this is progress!):",
            file=sys.stderr,
        )
        for filename, line_no, stage, category, reason in stale:
            print(
                f"  spec/{filename} line {line_no} "
                f"[vera:skip-{stage} {category}]: {reason}",
                file=sys.stderr,
            )
        exit_code = 1

    for stage in ("parse", "check", "verify"):
        if failures[stage]:
            print(f"\n{stage.upper()} FAILURES:", file=sys.stderr)
            for filename, line_no, error in failures[stage]:
                print(f"\n  spec/{filename} line {line_no}:", file=sys.stderr)
                print(f"    {error}", file=sys.stderr)
            print(
                f"\n{len(failures[stage])} spec code block(s) failed to "
                f"{stage}.  If intentional, annotate the fence with "
                f'<!-- vera:skip-{stage} category="..." reason="..." --> '
                f"(see scripts/doc_annotations.py).",
                file=sys.stderr,
            )
            exit_code = 1

    if exit_code == 0:
        print("\nAll parseable spec code blocks pass (parse + check + verify).")

    return exit_code


if __name__ == "__main__":
    sys.exit(main())
