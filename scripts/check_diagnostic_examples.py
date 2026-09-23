#!/usr/bin/env python
"""Replay `vera:diagnostic`-annotated ```text fences against live output (#1291).

The doc example gate (`check_doc_examples.py`) reads ```vera fences
only, so a ```text fence carrying RENDERED COMPILER OUTPUT — a diagnostic
block, a fix text, a trap message — is validated by nothing else: DE_BRUIJN.md's §6.2 E130 example is the instance that motivated
this (it went stale the moment #1262 extended E130's fix text, and every
```vera-fence gate stayed green throughout, since parsing Vera source was
never what that block needed checked).

For each `<!-- vera:diagnostic file="..." [stage="check"]
[error_code="..."] -->` ... `<!-- /vera:diagnostic -->` annotated program
immediately followed by a ```text fence, this script re-parses and
re-checks the program and asserts the fence is byte-identical to the live
`Diagnostic.format()` output — the same replay-not-trust shape the ```vera
fence gate already uses, applied to rendered TEXT instead of source.

Scope: this is the "marker-annotated subset" #1291 asks for first, not a
sweep of every ```text fence that happens to look like diagnostic output.
Every gated document is scanned, so a pair added anywhere the example gate
reads is replayed here.
"""

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from check_doc_examples import diagnostic_documents
from doc_annotations import replay_diagnostic_examples, scan_diagnostic_examples

ROOT = Path(__file__).resolve().parent.parent

# Documents scanned for `vera:diagnostic` annotations: every gated document
# that is not HTML, from the one list the example gate reads
# (`check_doc_examples.diagnostic_documents`).  The example gate honours a
# pair as an expected failure, so every pair it can honour must be replayed
# here; one list keeps the two from drifting apart.  A document with no
# annotated examples is fine (zero found, zero replayed).
DOCS = tuple(ROOT / doc for doc in diagnostic_documents(ROOT))


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
