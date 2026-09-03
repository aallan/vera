#!/usr/bin/env python
"""Replay `vera:diagnostic`-annotated ```text fences against live output (#1291).

The doc-example gates (`check_debruijn_examples.py` and siblings) parse
```vera fences only, so a ```text fence carrying RENDERED COMPILER
OUTPUT — a diagnostic block, a fix text, a trap message — is validated by
nothing: DE_BRUIJN.md's §6.2 E130 example is the instance that motivated
this (it went stale the moment #1262 extended E130's fix text, and every
```vera-fence gate stayed green throughout, since parsing Vera source was
never what that block needed checked).

For each `<!-- vera:diagnostic file="..." [stage="check"]
[error_code="..."] -->` ... `<!-- /vera:diagnostic -->` annotated program
immediately followed by a ```text fence, this script re-parses and
re-checks the program and asserts the fence is byte-identical to the live
`Diagnostic.format()` output — the same replay-not-trust shape the ```vera
fence gates already use, applied to rendered TEXT instead of source.

Scope: this is the "marker-annotated subset" #1291 asks for first, not a
sweep of every ```text fence that happens to look like diagnostic output.
Widening to more documents is future work — add the document's path to
DOCS below once it carries a `vera:diagnostic` annotation.
"""

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from doc_annotations import replay_diagnostic_examples, scan_diagnostic_examples

ROOT = Path(__file__).resolve().parent.parent

# Documents scanned for `vera:diagnostic` annotations.  A document with no
# annotated examples is silently fine (zero found, zero replayed) — this
# list only need grow as more mirrors gain the annotation, not as a
# precondition for adding one.
DOCS = (
    ROOT / "DE_BRUIJN.md",
)


def main() -> int:
    total_examples = 0
    all_problems: list[str] = []
    all_failures: list[str] = []

    for doc in DOCS:
        rel = doc.relative_to(ROOT).as_posix()
        if not doc.is_file():
            all_problems.append(f"{rel}: file not found")
            continue
        examples, problems = scan_diagnostic_examples(doc)
        all_problems.extend(f"{rel} {p}" for p in problems)
        total_examples += len(examples)
        failures = replay_diagnostic_examples(examples)
        all_failures.extend(f"{rel} {f}" for f in failures)

    print(f"vera:diagnostic examples found: {total_examples} "
          f"(across {len(DOCS)} document(s))")

    exit_code = 0

    if all_problems:
        print("\nANNOTATION PROBLEMS:", file=sys.stderr)
        for problem in all_problems:
            print(f"  {problem}", file=sys.stderr)
        exit_code = 1

    if all_failures:
        print("\nREPLAY FAILURES:", file=sys.stderr)
        for failure in all_failures:
            print(f"\n  {failure}", file=sys.stderr)
        exit_code = 1

    if exit_code == 0:
        print(f"All {total_examples} vera:diagnostic example(s) match live output.")

    return exit_code


if __name__ == "__main__":
    sys.exit(main())
