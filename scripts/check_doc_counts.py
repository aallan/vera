#!/usr/bin/env python
"""Verify that counts cited in documentation match the live codebase.

Checks filesystem-derivable counts (conformance programs, examples, test
files, pre-commit hooks, CI jobs) and pytest-collection counts (total tests,
per-file test counts and line counts) against the numbers written in
TESTING.md and CONTRIBUTING.md.

Runs in under 1 second — fast enough for a pre-commit hook.
"""

import json
import re
import subprocess
import sys
from pathlib import Path


def main() -> int:
    root = Path(__file__).resolve().parent.parent
    errors: list[str] = []

    # ------------------------------------------------------------------
    # 1. Derive live counts from the filesystem + pytest collection
    # ------------------------------------------------------------------

    # Conformance programs: count manifest entries
    manifest = json.loads((root / "tests/conformance/manifest.json").read_text())
    live_conformance = len(manifest)

    # Conformance level breakdown
    level_counts: dict[str, int] = {}
    for entry in manifest:
        lvl = entry["level"]
        level_counts[lvl] = level_counts.get(lvl, 0) + 1

    # Examples: count .vera files
    live_examples = len(list((root / "examples").glob("*.vera")))

    # Test files: count test_*.py
    test_files = sorted((root / "tests").glob("test_*.py"))
    live_test_files = len(test_files)

    # Per-file line counts
    file_lines: dict[str, int] = {}
    for f in test_files:
        file_lines[f.name] = len(f.read_text().splitlines())

    # Pre-commit hooks: parse YAML manually (avoid PyYAML dependency)
    precommit_text = (root / ".pre-commit-config.yaml").read_text()
    live_hooks = len(re.findall(r"^\s+- id:\s", precommit_text, re.MULTILINE))

    # CI jobs: count top-level keys under "jobs:"
    ci_text = (root / ".github/workflows/ci.yml").read_text()
    in_jobs = False
    live_ci_jobs = 0
    for line in ci_text.splitlines():
        if line.rstrip() == "jobs:":
            in_jobs = True
            continue
        if in_jobs:
            # A top-level job is a line with exactly 2-space indent + name + colon
            if re.match(r"^  [a-zA-Z_-]+:", line):
                live_ci_jobs += 1
            # Stop at next top-level key
            elif re.match(r"^[a-z]", line):
                break

    # Pytest collection: total tests + per-file counts
    pytest_bin = root / ".venv/bin/pytest"
    if not pytest_bin.exists():
        pytest_bin = Path("pytest")  # fall back to PATH
    result = subprocess.run(
        [str(pytest_bin), "--co", "-q"],
        capture_output=True,
        text=True,
        cwd=str(root),
        timeout=30,
    )
    if result.returncode != 0:
        print(
            f"ERROR: pytest collection failed:\n{result.stderr}",
            file=sys.stderr,
        )
        return 1

    # Parse "N tests collected"
    m = re.search(r"(\d+) tests? collected", result.stdout)
    live_total_tests = int(m.group(1)) if m else 0

    # Per-file test counts from collection output
    file_tests: dict[str, int] = {}
    for line in result.stdout.splitlines():
        if "::" in line:
            fname = line.split("::")[0].replace("tests/", "")
            file_tests[fname] = file_tests.get(fname, 0) + 1

    # ------------------------------------------------------------------
    # 2. Check TESTING.md overview table
    # ------------------------------------------------------------------

    testing_md = (root / "TESTING.md").read_text()

    def check_testing(pattern: str, expected: int, label: str) -> None:
        m = re.search(pattern, testing_md)
        if not m:
            errors.append(f"TESTING.md: could not find {label} pattern")
            return
        doc_val = int(m.group(1).replace(",", ""))
        if doc_val != expected:
            errors.append(
                f"TESTING.md {label}: doc says {doc_val}, live is {expected}"
            )

    check_testing(
        r"\*\*Tests\*\*\s*\|\s*([\d,]+)\s+across",
        live_total_tests,
        "total tests",
    )
    check_testing(
        r"\*\*Tests\*\*\s*\|.*across\s+(\d+)\s+files",
        live_test_files,
        "test file count",
    )
    check_testing(
        r"\*\*Conformance programs\*\*\s*\|\s*(\d+)",
        live_conformance,
        "conformance programs",
    )
    check_testing(
        r"\*\*Example programs\*\*\s*\|\s*(\d+)",
        live_examples,
        "example programs",
    )

    # ------------------------------------------------------------------
    # 3. Check TESTING.md per-file test table
    # ------------------------------------------------------------------

    for m in re.finditer(
        r"\| `(test_\w+\.py)` \| ([\d,]+) \| ([\d,]+) \|", testing_md
    ):
        name = m.group(1)
        doc_tests = int(m.group(2).replace(",", ""))
        doc_lines = int(m.group(3).replace(",", ""))

        live_t = file_tests.get(name)
        live_l = file_lines.get(name)

        if live_t is None:
            errors.append(
                f"TESTING.md table: lists {name} but file not found in tests/"
            )
            continue
        if doc_tests != live_t:
            errors.append(
                f"TESTING.md table: {name} tests: doc says {doc_tests},"
                f" live is {live_t}"
            )
        if live_l is not None and doc_lines != live_l:
            errors.append(
                f"TESTING.md table: {name} lines: doc says {doc_lines},"
                f" live is {live_l}"
            )

    # Check all test files appear in the table
    doc_files = set(re.findall(r"\| `(test_\w+\.py)` \|", testing_md))
    live_files = {f.name for f in test_files}
    for missing in sorted(live_files - doc_files):
        errors.append(f"TESTING.md table: missing row for {missing}")

    # ------------------------------------------------------------------
    # 4. Check TESTING.md conformance level table
    # ------------------------------------------------------------------

    for m in re.finditer(
        r"\| `(\w+)` \|[^|]+\| (\d+) \|", testing_md
    ):
        level = m.group(1)
        doc_count = int(m.group(2))
        live_count = level_counts.get(level, 0)
        if doc_count != live_count:
            errors.append(
                f"TESTING.md level table: {level}: doc says {doc_count},"
                f" live is {live_count}"
            )

    # ------------------------------------------------------------------
    # 5. Check TESTING.md hooks and CI counts
    # ------------------------------------------------------------------

    check_testing(
        r"checked by (\d+) hooks",
        live_hooks,
        "pre-commit hook count",
    )
    # CI job count — may be written as a digit ("4") or word ("four")
    _WORD_TO_INT = {
        "one": 1, "two": 2, "three": 3, "four": 4, "five": 5,
        "six": 6, "seven": 7, "eight": 8, "nine": 9, "ten": 10,
    }
    m = re.search(r"runs (\w+) parallel jobs", testing_md)
    if m:
        raw = m.group(1)
        doc_ci = _WORD_TO_INT.get(raw.lower()) or int(raw)
        if doc_ci != live_ci_jobs:
            errors.append(
                f"TESTING.md CI job count: doc says {doc_ci},"
                f" live is {live_ci_jobs}"
            )

    # ------------------------------------------------------------------
    # 6. Check inline conformance/example counts in TESTING.md body
    # ------------------------------------------------------------------

    # "52 programs" in conformance section
    for m in re.finditer(r"(\d+) programs", testing_md):
        n = int(m.group(1))
        # Only flag if it looks like a conformance count (> 10, < 200)
        if 10 < n < 200 and n != live_conformance:
            # Find line number for context
            pos = m.start()
            line_no = testing_md[:pos].count("\n") + 1
            errors.append(
                f"TESTING.md line {line_no}: says {n} programs,"
                f" live conformance is {live_conformance}"
            )

    # ------------------------------------------------------------------
    # 7. Check CONTRIBUTING.md
    # ------------------------------------------------------------------

    contrib_md = (root / "CONTRIBUTING.md").read_text()

    m = re.search(r"checked by (\d+) hooks", contrib_md)
    if m:
        doc_hooks = int(m.group(1))
        if doc_hooks != live_hooks:
            errors.append(
                f"CONTRIBUTING.md: hook count: doc says {doc_hooks},"
                f" live is {live_hooks}"
            )

    for m_iter in re.finditer(
        r"All (\d+) conformance programs", contrib_md
    ):
        doc_conf = int(m_iter.group(1))
        if doc_conf != live_conformance:
            errors.append(
                f"CONTRIBUTING.md: conformance count: doc says {doc_conf},"
                f" live is {live_conformance}"
            )

    for m_iter in re.finditer(
        r"All (\d+) [`.]*vera[`.]* examples", contrib_md
    ):
        doc_ex = int(m_iter.group(1))
        if doc_ex != live_examples:
            errors.append(
                f"CONTRIBUTING.md: example count: doc says {doc_ex},"
                f" live is {live_examples}"
            )

    # "verify all NN conformance" / "verify all NN .vera examples" in
    # validation script comments
    for m_iter in re.finditer(
        r"verify all (\d+) conformance", contrib_md
    ):
        doc_conf = int(m_iter.group(1))
        if doc_conf != live_conformance:
            errors.append(
                f"CONTRIBUTING.md: conformance script comment:"
                f" doc says {doc_conf}, live is {live_conformance}"
            )
    for m_iter in re.finditer(
        r"verify all (\d+) \.vera examples", contrib_md
    ):
        doc_ex = int(m_iter.group(1))
        if doc_ex != live_examples:
            errors.append(
                f"CONTRIBUTING.md: example script comment:"
                f" doc says {doc_ex}, live is {live_examples}"
            )

    # ------------------------------------------------------------------
    # 8. Check CLAUDE.md
    # ------------------------------------------------------------------

    claude_md = (root / "CLAUDE.md").read_text()

    for m_iter in re.finditer(r"All (\d+) conformance", claude_md):
        doc_conf = int(m_iter.group(1))
        if doc_conf != live_conformance:
            errors.append(
                f"CLAUDE.md: conformance count: doc says {doc_conf},"
                f" live is {live_conformance}"
            )

    for m_iter in re.finditer(r"All (\d+) examples", claude_md):
        doc_ex = int(m_iter.group(1))
        if doc_ex != live_examples:
            errors.append(
                f"CLAUDE.md: example count: doc says {doc_ex},"
                f" live is {live_examples}"
            )

    m = re.search(r"(\d+) conformance programs", claude_md)
    if m:
        doc_conf = int(m.group(1))
        if doc_conf != live_conformance:
            errors.append(
                f"CLAUDE.md: conformance programs: doc says {doc_conf},"
                f" live is {live_conformance}"
            )

    # ------------------------------------------------------------------
    # Report
    # ------------------------------------------------------------------

    if errors:
        print(
            f"ERROR: {len(errors)} stale count(s) in documentation:",
            file=sys.stderr,
        )
        for err in errors:
            print(f"  {err}", file=sys.stderr)
        return 1

    print(
        f"Documentation counts are consistent"
        f" ({live_total_tests} tests, {live_test_files} files,"
        f" {live_conformance} conformance, {live_examples} examples,"
        f" {live_hooks} hooks, {live_ci_jobs} CI jobs)."
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
