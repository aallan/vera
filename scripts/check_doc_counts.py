#!/usr/bin/env python
"""Verify that counts cited in documentation match the live codebase.

Checks filesystem-derivable counts (conformance programs, examples, test
files, pre-commit hooks, CI jobs) and pytest-collection counts (total tests,
per-file test counts and line counts) against the numbers written in
TESTING.md, CONTRIBUTING.md, CLAUDE.md, README.md, SKILL.md, AGENTS.md,
FAQ.md, and ROADMAP.md.  Also checks the KNOWN_ISSUES.md "Refactoring
needed" line counts (±10% tolerance), the HISTORY.md version-row format
(one issue link max, no " — " separator per row), the vera/README.md
module map (#1150), the project facts hardcoded on the landing page
(#528), and the cited corpus-program count.

Intentionally excludes CHANGELOG.md: its counts are historical records
(e.g. "64 programs, was 63") that are frozen snapshots of the project state
at each release. Validating them would cause false positives on every new
conformance addition, because the old entries are supposed to stay unchanged.

Runs in a couple of seconds — fast enough for a pre-commit hook.
"""

import json
import re
import subprocess
import sys
from pathlib import Path


def check_refactoring_counts(known_issues_text: str, root: Path) -> list[str]:
    """Compare KNOWN_ISSUES.md "Refactoring needed" line counts to disk.

    Uses a ±10% tolerance band rather than exact equality: the cited
    counts exist to convey scale, and exact pinning would tax every PR
    that touches one of the named files with a doc edit.  When the gate
    trips, the fix is re-citing the measured number.
    """
    errors: list[str] = []
    section = re.search(
        r"## Refactoring needed\n(.*?)(?=\n## |\Z)",
        known_issues_text,
        re.DOTALL,
    )
    if not section:
        return ["KNOWN_ISSUES.md: could not find '## Refactoring needed' section"]
    rows = re.findall(r"\| `([\w./-]+)` \| ([\d,]+) \|", section.group(1))
    if not rows:
        # Empty-section convention (mirrors "No known bugs."): when the last
        # oversized file is split, the table is replaced by this sentence.
        if "No files currently need decomposition." in section.group(1):
            return []
        return ["KNOWN_ISSUES.md: refactoring table has no `file` | count rows"]
    for rel, cited_s in rows:
        cited = int(cited_s.replace(",", ""))
        path = root / rel
        if not path.exists():
            errors.append(
                f"KNOWN_ISSUES.md refactoring table: {rel} does not exist"
            )
            continue
        live = len(path.read_text(encoding="utf-8").splitlines())
        if live == 0:
            if cited != 0:
                errors.append(
                    f"KNOWN_ISSUES.md refactoring table: {rel} cites"
                    f" {cited:,} lines, measured 0"
                )
            continue
        if abs(cited - live) / live > 0.10:
            errors.append(
                f"KNOWN_ISSUES.md refactoring table: {rel} cites"
                f" {cited:,} lines, measured {live:,} (>10% drift)"
            )
    return errors


_HISTORY_VERSION_ROW = re.compile(r"^\| v\d+\.\d+\.[\d.]")


def check_history_row_format(history_text: str) -> list[str]:
    """Enforce the HISTORY.md version-row template.

    Each `| vX.Y.N |` table row carries at most one issue link and at
    most one " — " separator (the optional **bold lead-in** dash, the
    v0.1.x-era template) — CHANGELOG.md is the per-release log of
    record, so secondary links and multi-clause rows belong there,
    not here.
    """
    errors: list[str] = []
    for lineno, line in enumerate(history_text.splitlines(), 1):
        if not _HISTORY_VERSION_ROW.match(line):
            continue
        links = len(re.findall(r"issues/\d+", line))
        if links > 1:
            errors.append(
                f"HISTORY.md line {lineno}: version row has {links}"
                f" issue links (max 1; secondary links live in CHANGELOG.md)"
            )
        dashes = line.count(" — ")
        if dashes > 1:
            errors.append(
                f"HISTORY.md line {lineno}: version row contains {dashes}"
                f" ' — ' separators (max 1 — the bold lead-in dash;"
                f" multi-clause rows belong in CHANGELOG.md)"
            )
    return errors


def check_corpus_count(root: Path) -> list[str]:
    """Gate the cited corpus-program count wherever TESTING.md states it.

    The corpus is every ``*.vera`` under ``examples/`` and
    ``tests/conformance/`` **recursively** — the set
    ``scripts/check_corpus_canonical.py`` sweeps.  It is not derivable from
    the conformance and example counts this script already checks: those are
    top-level ``glob``s, while the corpus includes the imported modules under
    ``examples/vera/`` and ``tests/conformance/vera/``.

    Ungated, this number went stale the moment a conformance fixture landed
    (#1160), and a phrasing-specific ``grep`` missed one of the two rows that
    cite it — the two are worded differently ("All N corpus programs" vs
    "All N ``examples/`` + ..."), so the pattern here keys on the script name
    that anchors both rows, not on the prose around the number.
    """
    errors: list[str] = []
    live = sum(
        len(list((root / d).rglob("*.vera")))
        for d in ("examples", "tests/conformance")
    )
    testing = (root / "TESTING.md").read_text(encoding="utf-8")
    rows = re.findall(
        r"`check_corpus_canonical\.py`[^|\n]*\|[^|\n]*?All (\d+)\b", testing
    )
    if not rows:
        errors.append(
            "TESTING.md: no `check_corpus_canonical.py` row states a corpus"
            " count — the rows moved or were reworded, so they are no longer gated"
        )
    for cited in rows:
        if int(cited) != live:
            errors.append(
                f"TESTING.md corpus count: doc says {cited}, live is {live}"
            )
    return errors


_NUMBER_WORDS = {
    1: "one", 2: "two", 3: "three", 4: "four", 5: "five", 6: "six",
    7: "seven", 8: "eight", 9: "nine", 10: "ten", 11: "eleven",
    12: "twelve", 13: "thirteen", 14: "fourteen", 15: "fifteen",
}

# The page calls the `Exn` effect "Exceptions" in prose.
_HOMEPAGE_EFFECT_ALIASES = {"Exn": "Exceptions"}


def check_homepage_facts(
    html: str, root: Path, live_conformance: int, live_examples: int
) -> list[str]:
    """Gate the project facts hardcoded in docs/index.html (#528).

    The landing page states counts in prose — built-ins, effects, spec
    chapters, conformance programs, examples — that drift silently as the
    codebase moves.  Two were already stale before anyone noticed ("six
    algebraic effects" when there were seven; a 77-program suite when there
    were 80).

    Gating rather than templating, per the issue: the HTML stays
    hand-edited, which is the convention for this file.

    A pattern that matches *nothing* is an error in its own right — a
    reworded sentence would otherwise silently switch its check off, which
    is the failure mode the gate exists to prevent.  Effects are checked as
    a count *and* a membership list, since the historical drift was a name
    missing from the list rather than a wrong total.  The version string is
    deliberately not checked here: `scripts/check_version_sync.py` already
    owns docs/index.html for that.
    """
    from vera.environment import TypeEnv
    from vera.introspect import effects_payload

    errors: list[str] = []
    effects = [i for i in effects_payload()["items"] if i.get("kind") != "ability"]
    effect_names = {
        _HOMEPAGE_EFFECT_ALIASES.get(str(i["name"]), str(i["name"])) for i in effects
    }

    numeric: list[tuple[str, str, int]] = [
        ("built-in functions", r"(\d+) built-in functions", len(TypeEnv().functions)),
        ("spec chapters", r"(\d+)-chapter specification", len(list((root / "spec").glob("*.md")))),
        ("conformance programs", r"(\d+)-program conformance suite", live_conformance),
        ("worked examples", r"(\d+) worked examples", live_examples),
    ]
    for label, pattern, live in numeric:
        found = re.search(pattern, html)
        if found is None:
            errors.append(
                f"docs/index.html: no '{label}' claim matched /{pattern}/ —"
                f" the sentence moved or was reworded, so it is no longer gated"
            )
        elif int(found.group(1)) != live:
            errors.append(
                f"docs/index.html {label}: page says {found.group(1)},"
                f" live is {live}"
            )

    # Effects: the count is spelled as a word in the status paragraph, and the
    # names are enumerated TWICE — there and again in the reference card, which
    # is a second hand-maintained mirror of the same fact.  Both are checked;
    # the historical drift (#526) was a name missing from a list, not a wrong
    # total, so a count-only check would not have caught it.
    spelled = re.search(r"(\w+) algebraic effects \(([^)]*)\)", html)
    if spelled is None:
        errors.append(
            "docs/index.html: no 'N algebraic effects (…)' claim found —"
            " the sentence moved or was reworded, so it is no longer gated"
        )
    else:
        want_word = _NUMBER_WORDS.get(len(effect_names), str(len(effect_names)))
        if spelled.group(1) != want_word:
            errors.append(
                f"docs/index.html effects count: page says"
                f" '{spelled.group(1)}', live is '{want_word}'"
                f" ({len(effect_names)})"
            )

    card = re.search(
        r'>Algebraic effects</div><div class="desc">([^&<]*)', html
    )
    lists: list[tuple[str, str]] = []
    if spelled is not None:
        lists.append(("status paragraph", spelled.group(2)))
    if card is not None:
        lists.append(("reference card", card.group(1)))
    else:
        errors.append(
            "docs/index.html: no 'Algebraic effects' reference card found —"
            " the card moved or was reworded, so it is no longer gated"
        )
    for where, raw in lists:
        listed = {n.strip() for n in raw.split(",") if n.strip()}
        if listed != effect_names:
            missing = sorted(effect_names - listed)
            extra = sorted(listed - effect_names)
            errors.append(
                f"docs/index.html effects list ({where}) drifted —"
                f" missing: {missing or 'none'}; not a live effect: {extra or 'none'}"
            )
    return errors


_MODULE_MAP_ROW = re.compile(
    r"^\| `(?P<label>[^`]+)`(?P<suffix>[^|]*)\| (?P<lines>[\d,]+) \|", re.M
)


def _line_count(path: Path) -> int | None:
    try:
        return len(path.read_text(encoding="utf-8").splitlines())
    except OSError:
        return None


def check_module_map(readme_text: str, root: Path) -> list[str]:
    """Check the vera/README.md "Module Map" table against the source tree.

    Two independent assertions, because they fail differently (#1150):

    * **Counts** — each row's cited line count against the file on disk,
      with the same ±10% band `check_refactoring_counts` uses.  The
      numbers exist to convey relative scale when navigating the
      compiler, so exact pinning would tax every PR that touches a
      compiler file with a doc edit; a band still catches the drift that
      makes the table misleading (`checker/calls.py` had reached 155%).
    * **Coverage** — every module on disk has a row.  This is exact, and
      it is the half a count check cannot do: `checker/sql.py` (#309) and
      `runtime/db.py` (#229) shipped without rows, so there was no cited
      number to be wrong.

    A `pkg/` row aggregates that package's ``*.py``.  A row suffixed
    ``×N`` (the per-effect host-binding families) aggregates every
    ``*.py`` in the current package that no other row names, and pins N
    to how many that is — so adding an effect family trips the gate.
    """
    errors: list[str] = []
    section = re.search(r"## Module Map\n(.*?)(?=\n## |\Z)", readme_text, re.DOTALL)
    if section is None:
        return ["vera/README.md: no '## Module Map' section found"]

    body = section.group(1)
    table_rows = [
        line
        for line in body.splitlines()
        if line.startswith("| ") and not line.startswith(("|---", "| Module"))
    ]
    parsed = list(_MODULE_MAP_ROW.finditer(body))
    if len(parsed) != len(table_rows):
        errors.append(
            f"vera/README.md module map: {len(table_rows) - len(parsed)} row(s)"
            f" did not parse — every row must be `| \\`name\\` | count | ...`"
        )

    named: set[Path] = set()          # files a row names, for the coverage pass
    deferred: list[tuple[str, str, int, str]] = []  # ×N rows: label, suffix, cited, pkg
    package = ""

    for match in parsed:
        label = match.group("label")
        cited = int(match.group("lines").replace(",", ""))
        stem = label.strip(" ├└│─")
        is_child = label != label.lstrip(" ├└│")

        if stem.endswith("/"):
            package = stem.rstrip("/")
            directory = root / "vera" / package
            if not directory.is_dir():
                errors.append(
                    f"vera/README.md module map: package `{stem}` does not exist"
                )
                continue
            live = sum(_line_count(f) or 0 for f in directory.glob("*.py"))
        elif "×" in match.group("suffix"):
            deferred.append((label, match.group("suffix"), cited, package))
            continue
        else:
            path = root / "vera" / (package if is_child else "") / stem
            live = _line_count(path)  # type: ignore[assignment]
            if live is None:
                errors.append(
                    f"vera/README.md module map: `{stem}` cites {cited:,} lines"
                    f" but the file does not exist"
                )
                continue
            named.add(path.resolve())

        if live and abs(cited - live) / live > 0.10:
            errors.append(
                f"vera/README.md module map: `{stem}` cites {cited:,} lines,"
                f" measured {live:,} (>10% drift)"
            )

    # ``×N`` rows stand for the files no other row named, so they can only
    # be resolved once every explicit row has been collected.
    for label, suffix, cited, pkg in deferred:
        directory = root / "vera" / pkg
        rest = sorted(
            f
            for f in directory.glob("*.py")
            if f.name != "__init__.py" and f.resolve() not in named
        )
        named.update(f.resolve() for f in rest)
        shown = f"{label.strip()}{suffix.strip()}"

        declared = re.search(r"×(\d+)", suffix)
        if declared is None:
            errors.append(
                f"vera/README.md module map: `{shown}` has no ×N multiplicity"
            )
        elif int(declared.group(1)) != len(rest):
            errors.append(
                f"vera/README.md module map: `{shown}` declares"
                f" ×{declared.group(1)} but {pkg}/ has {len(rest)} such"
                f" module(s): {', '.join(f.name for f in rest)}"
            )

        live = sum(_line_count(f) or 0 for f in rest)
        if live and abs(cited - live) / live > 0.10:
            errors.append(
                f"vera/README.md module map: `{shown}` cites {cited:,}"
                f" lines, measured {live:,} (>10% drift)"
            )

    # Coverage: exact, no tolerance.
    for source in sorted((root / "vera").rglob("*.py")):
        if source.name == "__init__.py" or "__pycache__" in source.parts:
            continue
        if source.resolve() not in named:
            errors.append(
                f"vera/README.md module map: {source.relative_to(root)} has no row"
            )
    return errors


def main() -> int:
    root = Path(__file__).resolve().parent.parent
    errors: list[str] = []

    # ------------------------------------------------------------------
    # 1. Derive live counts from the filesystem + pytest collection
    # ------------------------------------------------------------------

    # Conformance programs: count manifest entries
    manifest = json.loads(
        (root / "tests/conformance/manifest.json").read_text(encoding="utf-8")
    )
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
        file_lines[f.name] = len(f.read_text(encoding="utf-8").splitlines())

    # Pre-commit hooks: parse YAML manually (avoid PyYAML dependency)
    precommit_text = (root / ".pre-commit-config.yaml").read_text(encoding="utf-8")
    live_hooks = len(re.findall(r"^\s+- id:\s", precommit_text, re.MULTILINE))

    # CI jobs: count top-level keys under "jobs:"
    ci_text = (root / ".github/workflows/ci.yml").read_text(encoding="utf-8")
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

    # Pytest collection: total tests + per-file counts.
    # `-o addopts=""` overrides the default `-m 'not stress'`
    # from pyproject.toml (#596 stress-marker registration) so
    # the collection sees every test file including
    # `test_stress.py`.  Without this override the per-file
    # counter wouldn't see stress tests and would report them
    # as a missing row in TESTING.md.
    pytest_bin = root / ".venv/bin/pytest"
    if not pytest_bin.exists():
        pytest_bin = Path("pytest")  # fall back to PATH
    result = subprocess.run(
        [str(pytest_bin), "--co", "-q", "-o", "addopts="],
        capture_output=True,
        text=True,
        encoding="utf-8",
        cwd=str(root),
        timeout=30,
        check=False,
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

    testing_md = (root / "TESTING.md").read_text(encoding="utf-8")

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
        r"checked by (\d+) (?:configured )?hooks",
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

    # Prose forms the `(\d+) programs` pattern above cannot reach: an
    # adjective intervenes ("N small, focused programs") or the noun differs
    # ("All N conformance entries").  These three sites drifted silently to a
    # stale 148 (PR #982 review); pin them so the whole class dies, not just
    # the individual instances.
    for pat, label in (
        (r"(\d+) small, focused programs", "small-focused programs prose"),
        (r"All (\d+) conformance entries", "conformance-entries prose"),
    ):
        for m in re.finditer(pat, testing_md):
            n = int(m.group(1))
            if n != live_conformance:
                pos = m.start()
                line_no = testing_md[:pos].count("\n") + 1
                errors.append(
                    f"TESTING.md line {line_no} ({label}): says {n},"
                    f" live conformance is {live_conformance}"
                )

    # ------------------------------------------------------------------
    # 7. Check CONTRIBUTING.md
    # ------------------------------------------------------------------

    contrib_md = (root / "CONTRIBUTING.md").read_text(encoding="utf-8")

    m = re.search(r"checked by (\d+) (?:configured )?hooks", contrib_md)
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

    claude_md = (root / "CLAUDE.md").read_text(encoding="utf-8")

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
    # 9. Check README.md
    # ------------------------------------------------------------------

    readme_md = (root / "README.md").read_text(encoding="utf-8")

    def check_readme(pattern: str, expected: int, label: str) -> None:
        m = re.search(pattern, readme_md)
        if not m:
            return  # Pattern absent from README is OK — not all counts appear
        doc_val = int(m.group(1).replace(",", ""))
        if doc_val != expected:
            errors.append(
                f"README.md {label}: doc says {doc_val}, live is {expected}"
            )

    check_readme(
        r"([\d,]+) tests across",
        live_total_tests,
        "total tests",
    )
    check_readme(
        r"([\d,]+) tests, \d+% Python code coverage",
        live_total_tests,
        "project-status tests",
    )
    check_readme(
        r"tests across (\d+) files",
        live_test_files,
        "test file count",
    )
    check_readme(
        r"(\d+) programs across \d+ spec",
        live_conformance,
        "conformance programs",
    )
    check_readme(
        r"(\d+) end-to-end",
        live_examples,
        "example count",
    )

    # ------------------------------------------------------------------
    # 10. Check SKILL.md
    # ------------------------------------------------------------------

    skill_md = (root / "SKILL.md").read_text(encoding="utf-8")

    m = re.search(r"contains (\d+) small programs", skill_md)
    if m:
        doc_conf = int(m.group(1))
        if doc_conf != live_conformance:
            errors.append(
                f"SKILL.md: conformance count: doc says {doc_conf},"
                f" live is {live_conformance}"
            )

    # ------------------------------------------------------------------
    # 11. Check AGENTS.md
    # ------------------------------------------------------------------

    agents_md = (root / "AGENTS.md").read_text(encoding="utf-8")

    m = re.search(r"contains (\d+) small, self-contained programs", agents_md)
    if m:
        doc_conf = int(m.group(1))
        if doc_conf != live_conformance:
            errors.append(
                f"AGENTS.md: conformance count: doc says {doc_conf},"
                f" live is {live_conformance}"
            )

    for m_iter in re.finditer(r"All (\d+) conformance programs", agents_md):
        doc_conf = int(m_iter.group(1))
        if doc_conf != live_conformance:
            errors.append(
                f"AGENTS.md: conformance count: doc says {doc_conf},"
                f" live is {live_conformance}"
            )

    for m_iter in re.finditer(r"All (\d+) examples", agents_md):
        doc_ex = int(m_iter.group(1))
        if doc_ex != live_examples:
            errors.append(
                f"AGENTS.md: example count: doc says {doc_ex},"
                f" live is {live_examples}"
            )

    for m_iter in re.finditer(
        r"check_conformance\.py\s+# All (\d+) conformance", agents_md
    ):
        doc_conf = int(m_iter.group(1))
        if doc_conf != live_conformance:
            errors.append(
                f"AGENTS.md: script comment conformance count:"
                f" doc says {doc_conf}, live is {live_conformance}"
            )

    for m_iter in re.finditer(
        r"check_examples\.py\s+# All (\d+) examples", agents_md
    ):
        doc_ex = int(m_iter.group(1))
        if doc_ex != live_examples:
            errors.append(
                f"AGENTS.md: script comment example count:"
                f" doc says {doc_ex}, live is {live_examples}"
            )

    # ------------------------------------------------------------------
    # 12. Check FAQ.md
    # ------------------------------------------------------------------

    faq_md = (root / "FAQ.md").read_text(encoding="utf-8")

    for m_iter in re.finditer(
        r"conformance test suite \((\d+) programs", faq_md
    ):
        doc_conf = int(m_iter.group(1))
        if doc_conf != live_conformance:
            errors.append(
                f"FAQ.md: conformance count: doc says {doc_conf},"
                f" live is {live_conformance}"
            )

    for m_iter in re.finditer(r"(\d+)-program conformance suite", faq_md):
        doc_conf = int(m_iter.group(1))
        if doc_conf != live_conformance:
            errors.append(
                f"FAQ.md: conformance suite size: doc says {doc_conf},"
                f" live is {live_conformance}"
            )

    # The by-the-numbers test count ("8,840 tests, including a ...").
    # This line drifted silently through two releases because only the
    # conformance half of the sentence was pinned.  A missing pattern is
    # an error, not a skip — otherwise rewording the line disables the
    # check and reopens the same blind spot one level up.
    m = re.search(r"([\d,]+) tests, including", faq_md)
    if not m:
        errors.append(
            "FAQ.md: headline test-count line"
            " ('N tests, including ...') not found"
        )
    else:
        doc_tests = int(m.group(1).replace(",", ""))
        if doc_tests != live_total_tests:
            errors.append(
                f"FAQ.md: tests count: doc says {doc_tests},"
                f" live is {live_total_tests}"
            )

    # ------------------------------------------------------------------
    # 13. Check docs/index.html status block
    # ------------------------------------------------------------------
    # The site landing page has a one-paragraph status block summarising
    # conformance and example counts.  It's static HTML (not generated
    # from any other source) so it drifts silently: at the time this
    # check was added it had been stuck at 81 / 32 for several
    # conformance and example additions.  Pinning it here keeps it
    # honest.

    index_html = (root / "docs/index.html").read_text(encoding="utf-8")

    # Accept "A" or "An" — the article depends on how the number reads
    # ("an 89-program" but "a 90-program"), so don't force one form.
    m = re.search(r"An? (\d+)-program conformance suite", index_html)
    if not m:
        errors.append(
            "docs/index.html: could not find conformance count pattern"
            " (`A[n] NN-program conformance suite`)"
        )
    else:
        doc_conf = int(m.group(1))
        if doc_conf != live_conformance:
            errors.append(
                f"docs/index.html: conformance count: doc says {doc_conf},"
                f" live is {live_conformance}"
            )

    m = re.search(r"and (\d+) worked examples", index_html)
    if not m:
        errors.append(
            "docs/index.html: could not find example count pattern"
            " (`and NN worked examples`)"
        )
    else:
        doc_ex = int(m.group(1))
        if doc_ex != live_examples:
            errors.append(
                f"docs/index.html: example count: doc says {doc_ex},"
                f" live is {live_examples}"
            )

    # ------------------------------------------------------------------
    # 14. Check ROADMAP.md "Where we are" summary
    # ------------------------------------------------------------------
    # Scope the search to the "Where we are" section only — ROADMAP.md
    # also contains historical per-release snapshots with older counts
    # (e.g. "3,121 tests, 65 conformance programs" for v0.0.102) that
    # would produce false positives if the whole file were searched.

    roadmap_md = (root / "ROADMAP.md").read_text(encoding="utf-8")

    where_m = re.search(
        r"## Where we are\n(.*?)(?=\n##|\Z)", roadmap_md, re.DOTALL
    )
    if not where_m:
        errors.append(
            "ROADMAP.md: could not find '## Where we are' section"
        )
    else:
        where_section = where_m.group(1)
        m = re.search(
            r"([\d,]+) tests,.*?(\d+) conformance programs",
            where_section,
            re.DOTALL,
        )
        if not m:
            errors.append(
                "ROADMAP.md: could not find test/conformance count"
                " pattern in 'Where we are' section"
            )
        else:
            doc_tests = int(m.group(1).replace(",", ""))
            doc_conf = int(m.group(2))
            if doc_tests != live_total_tests:
                errors.append(
                    f"ROADMAP.md: test count: doc says {doc_tests},"
                    f" live is {live_total_tests}"
                )
            if doc_conf != live_conformance:
                errors.append(
                    f"ROADMAP.md: conformance count: doc says {doc_conf},"
                    f" live is {live_conformance}"
                )

    # ------------------------------------------------------------------
    # 15. Check KNOWN_ISSUES.md refactoring line counts (±10%)
    # ------------------------------------------------------------------

    known_issues_md = (root / "KNOWN_ISSUES.md").read_text(encoding="utf-8")
    errors.extend(check_refactoring_counts(known_issues_md, root))

    # ------------------------------------------------------------------
    # 16. Check HISTORY.md version-row format
    # ------------------------------------------------------------------

    history_md = (root / "HISTORY.md").read_text(encoding="utf-8")
    errors.extend(check_history_row_format(history_md))

    # README's status row and HISTORY's "By the numbers" total are the
    # same hand-maintained release count in two places; a release bumps
    # both.  They disagreed for two releases (204/203, then 205/203)
    # before this cross-check existed.
    m_readme = re.search(r"(\d+) releases,", readme_md)
    m_history = re.search(r"(\d+) tagged releases", history_md)
    if not m_readme:
        errors.append("README.md: release count ('N releases,') not found")
    if not m_history:
        errors.append(
            "HISTORY.md: release count ('N tagged releases') not found"
        )
    if m_readme and m_history and m_readme.group(1) != m_history.group(1):
        errors.append(
            f"release count mismatch: README.md says {m_readme.group(1)},"
            f" HISTORY.md says {m_history.group(1)} tagged releases"
        )

    # ------------------------------------------------------------------
    # 17. Check the vera/README.md module map against the source tree
    # ------------------------------------------------------------------

    vera_readme_md = (root / "vera/README.md").read_text(encoding="utf-8")
    errors.extend(check_module_map(vera_readme_md, root))

    # ------------------------------------------------------------------
    # 18. Check the hardcoded project facts on the landing page
    # ------------------------------------------------------------------

    index_html = (root / "docs/index.html").read_text(encoding="utf-8")
    errors.extend(
        check_homepage_facts(index_html, root, live_conformance, live_examples)
    )

    # ------------------------------------------------------------------
    # 19. Check the cited corpus-program count (#1160 review)
    # ------------------------------------------------------------------

    errors.extend(check_corpus_count(root))

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
