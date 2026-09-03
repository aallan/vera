#!/usr/bin/env python
"""Verify that counts cited in documentation match the live codebase.

Checks filesystem-derivable counts (conformance programs, examples, test
files, pre-commit hooks, CI jobs) and pytest-collection counts (total tests,
per-file test counts and line counts) against the numbers written in
TESTING.md, CONTRIBUTING.md, CLAUDE.md, README.md, SKILL.md, AGENTS.md,
FAQ.md, and ROADMAP.md.  Also checks TESTING.md's passed/stress-deselected/skipped
breakdown against the collected total, the KNOWN_ISSUES.md "Refactoring
needed" line counts (±10% tolerance), the HISTORY.md version-row format
(one issue link max, no " — " separator per row), the vera/README.md
module map (#1150) and its Test Suite paragraph's four counts, the project
facts hardcoded on the landing page (#528), and the cited corpus-program
count.  Three more were added for #1290: every figure on README's
project-status line rather than only its test count; TESTING.md's dual-target
conformance row, whose split and category counts come from a live run of the
differential itself; and the shape of KNOWN_ISSUES.md's Bugs table.

Intentionally excludes CHANGELOG.md: its counts are historical records
(e.g. "64 programs, was 63") that are frozen snapshots of the project state
at each release. Validating them would cause false positives on every new
conformance addition, because the old entries are supposed to stay unchanged.

Runs in a few seconds — fast enough for a pre-commit hook.  Everything it
does is local: the one check that needs the GitHub API, the Bugs table
against the open `bug`-labelled issues, is opt-in behind --check-bug-issues,
for the release PR.  A commit hook must not depend on a network call.
"""

import argparse
import json
import os
import re
import subprocess
import sys
import tomllib
from pathlib import Path
from typing import NamedTuple
from urllib.request import Request, urlopen


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


_TESTS_BREAKDOWN = re.compile(
    r"\*\*Tests\*\*\s*\|\s*[\d,]+\s+across.*?;\s*([\d,]+) passed"
    r"\s*\+\s*([\d,]+) stress-deselected,\s*([\d,]+) skipped"
)


def check_tests_breakdown(testing_text: str, live_total: int) -> list[str]:
    """Check that TESTING.md's tests breakdown sums to the gated total.

    All three parts name a pytest *disposition*, which is what makes the
    sum readable: the 26 are deselected before the run by
    ``addopts = "-m 'not stress'"``, so they are disjoint from the passed
    count rather than a subset of it.  Naming the marker alone — "26
    stress" beside "passed" and "skipped" — invited reading them as
    stress tests that passed, which would make the sentence's arithmetic
    wrong (PR #1329 review).

    The overview row states the total *and* its parts, in the shape
    "1,306 across 40 files (…; 1,234 passed + 5 stress-deselected, 67
    skipped)" —
    illustrative numbers, so this docstring does not itself become a
    citation to keep in sync.  Pinning the total alone leaves the parts
    free to drift, so a release that moves the parts without moving the
    sum, or moves the sum and refreshes only the number the gate reads,
    leaves an arithmetically impossible sentence behind.  Both halves are
    checked: each part against nothing (they are not independently
    derivable without running the suite three ways) and their sum against
    the collected total, which is exactly the internal consistency a
    reader would check by hand.

    A pattern that matches nothing is an error in its own right — rewording
    the parenthetical would otherwise silently switch the check off, which
    is the failure mode the gate exists to prevent.
    """
    m = _TESTS_BREAKDOWN.search(testing_text)
    if m is None:
        return [
            "TESTING.md: no tests breakdown matched"
            " ('N passed + N stress-deselected, N skipped') — the row"
            " moved or was"
            " reworded, so the breakdown is no longer gated"
        ]
    parts = [int(g.replace(",", "")) for g in m.groups()]
    total = sum(parts)
    if total != live_total:
        passed, stress, skipped = parts
        return [
            f"TESTING.md tests breakdown: {passed:,} passed"
            f" + {stress:,} stress-deselected + {skipped:,} skipped"
            f" = {total:,},"
            f" but the collected total is {live_total:,}"
        ]
    return []


_VERA_README_TESTS = re.compile(
    r"\*\*pytest suite\*\* of ([\d,]+) tests across ([\d,]+) files.*?"
    r"\(([\d,]+) programs in `tests/conformance/`.*?"
    r"\(([\d,]+) end-to-end demos\)",
    re.DOTALL,
)

_TEST_SUITE_HEADING = re.compile(r"^## Test Suite[ \t]*$", re.M)


def _test_suite_section(readme_text: str) -> str | None:
    """The body of vera/README.md's "## Test Suite" section, or ``None``.

    The counts are spread over one long sentence, so the pattern above
    spans them with ``DOTALL``.  Searched against the whole file that lets
    the paragraph's head pair with digits from any LATER section: the
    paragraph can be reworded until it no longer states the counts and the
    check still greens off a decoy elsewhere in the file — the silent skip
    this gate exists to prevent.  Slicing to the section first is what
    keeps a rewording (or a renamed heading, which yields ``None``) loud.
    """
    m = _TEST_SUITE_HEADING.search(readme_text)
    if m is None:
        return None
    rest = readme_text[m.end():]
    nxt = re.search(r"^## ", rest, re.M)
    return rest if nxt is None else rest[: nxt.start()]


def check_vera_readme_test_counts(
    readme_text: str,
    live_total_tests: int,
    live_test_files: int,
    live_conformance: int,
    live_examples: int,
) -> list[str]:
    """Pin the four counts in vera/README.md's "Test Suite" paragraph.

    Only the module map is otherwise gated in that file, which leaves this
    sentence free to drift release after release — the same class as
    FAQ.md's headline line, and the same remedy: read the numbers the way
    the oracle reads every other citation of them.  The counts are read
    from the "## Test Suite" section alone (see :func:`_test_suite_section`),
    never from the file at large.  A missing heading or a missing pattern
    is an error, not a skip.
    """
    section = _test_suite_section(readme_text)
    m = None if section is None else _VERA_README_TESTS.search(section)
    if m is None:
        return [
            "vera/README.md: the Test Suite paragraph's counts did not match"
            " ('N tests across N files … (N programs in `tests/conformance/`"
            " …) … (N end-to-end demos)') under a '## Test Suite' heading —"
            " the heading or the sentence moved or was reworded, so it is"
            " no longer gated"
        ]
    errors: list[str] = []
    for label, cited_s, live in (
        ("total tests", m.group(1), live_total_tests),
        ("test file count", m.group(2), live_test_files),
        ("conformance programs", m.group(3), live_conformance),
        ("example programs", m.group(4), live_examples),
    ):
        cited = int(cited_s.replace(",", ""))
        if cited != live:
            errors.append(
                f"vera/README.md Test Suite {label}: doc says {cited:,},"
                f" live is {live:,}"
            )
    return errors


def check_contributing_hook_count(
    contrib_text: str, live_hooks: int
) -> list[str]:
    """CONTRIBUTING.md's pre-commit hook count, against the live config.

    One sentence is the whole tie between the documented number and
    `.pre-commit-config.yaml`, so a rewording the pattern no longer matches
    would take the check offline without saying so — the silent-skip failure
    this script exists to prevent, and the one its TESTING.md twin already
    reports.  A sentence that cannot be found is therefore an error, not a
    pass.
    """
    m = re.search(r"configures (\d+) hooks", contrib_text)
    if not m:
        return [
            "CONTRIBUTING.md: could not find the hook-count sentence"
            " (`configures N hooks`) — reword the check with the prose"
        ]
    doc_hooks = int(m.group(1))
    if doc_hooks != live_hooks:
        return [
            f"CONTRIBUTING.md: hook count: doc says {doc_hooks},"
            f" live is {live_hooks}"
        ]
    return []


_CI_LINT_STEP = re.compile(
    r"^\s+run:\s+(?:python\s+)?scripts/(\w+\.py)", re.MULTILINE
)


def _ci_lint_job(ci_text: str) -> str | None:
    """The body of ci.yml's ``lint`` job, or ``None`` if it is not there.

    Scoped to the one job rather than scanned whole-file: every other job
    runs scripts too, and a whole-file scan would report them all as
    undocumented.  Entry is gated on the ``jobs:`` key first, because
    ``on:`` has two-space-indented children (``push:``, ``pull_request:``)
    that are not jobs.
    """
    body: list[str] | None = None
    in_jobs = False
    for line in ci_text.splitlines():
        if line.rstrip() == "jobs:":
            in_jobs = True
            continue
        if not in_jobs:
            continue
        if re.match(r"^[a-z]", line):  # next top-level key ends `jobs:`
            break
        job = re.match(r"^  ([A-Za-z0-9_-]+):", line)
        if job:
            if job.group(1) == "lint":
                body = []
                continue
            if body is not None:  # the next job ends lint's body
                break
        if body is not None:
            body.append(line)
    return "\n".join(body) if body is not None else None


def check_ci_lint_scripts(testing_text: str, ci_text: str) -> list[str]:
    """TESTING.md's CI-pipeline lint row against the workflow it describes.

    The row hand-enumerates the scripts the lint job runs, in the job's own
    order, and nothing tied the two together: a lint step added to
    `.github/workflows/ci.yml` without a matching row entry left the
    documentation describing 22 of the 23 scripts the job invokes, with
    every gate green (found by hand on PR #1257, whose own script was the
    omission).  It is the same hand-enumerated-list drift that PR's gate
    exists to prevent, one layer out.

    Order is compared, not just membership: the row reads as the sequence
    the job runs, so a set-only comparison would let a reordered row lie.
    A row or job that cannot be found is an error rather than a pass —
    rewording either side must not switch the check off in silence.
    """
    body = _ci_lint_job(ci_text)
    if body is None:
        return [
            "ci.yml: could not find the `lint` job under `jobs:`"
            " — reword the check with the workflow"
        ]
    live = _CI_LINT_STEP.findall(body)
    if not live:
        return ["ci.yml: the `lint` job runs no `scripts/*.py` steps"]

    rows = [
        line for line in testing_text.splitlines()
        if line.startswith("| **lint**")
    ]
    if len(rows) != 1:
        return [
            "TESTING.md: could not find the CI-pipeline `| **lint** |` row"
            f" (matched {len(rows)}) — reword the check with the table"
        ]
    doc = re.findall(r"`(\w+\.py)`", rows[0])

    if doc == live:
        return []

    errors = [
        f"TESTING.md lint row: {name} runs in ci.yml's lint job but is"
        " not listed"
        for name in sorted(set(live) - set(doc))
    ]
    errors += [
        f"TESTING.md lint row: {name} is listed but ci.yml's lint job"
        " does not run it"
        for name in sorted(set(doc) - set(live))
    ]
    if not errors:
        errors.append(
            "TESTING.md lint row: names the same scripts as ci.yml's lint"
            " job but not in the same order, so the row cannot be read as"
            f" the job's sequence — doc {doc}, workflow {live}"
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


def project_version(root: Path) -> str:
    """The `[project] version` in pyproject.toml.

    `check_version_sync.py` is what pins this to the other four places
    it appears, so reading the one file is enough here.
    """
    with (root / "pyproject.toml").open("rb") as handle:
        return str(tomllib.load(handle)["project"]["version"])


_RELEASE_TAG = re.compile(r"^v\d+\.\d+\.\d+(?:\.\d+)?$")

# git reads the repository to operate on from the environment before it
# reads `-C`, so these have to be cleared for `root` to mean `root`.
# pre-commit sets them: this script runs as a hook, and inside that hook
# `git -C <anywhere> tag` answers for the repository being committed to.
GIT_REPO_ENV_VARS = (
    "GIT_DIR",
    "GIT_WORK_TREE",
    "GIT_INDEX_FILE",
    "GIT_COMMON_DIR",
    "GIT_OBJECT_DIRECTORY",
    "GIT_ALTERNATE_OBJECT_DIRECTORIES",
)


def git_env() -> dict[str, str]:
    """The ambient environment with git's repository selectors removed."""
    return {
        k: v for k, v in os.environ.items() if k not in GIT_REPO_ENV_VARS
    }


def release_tags(root: Path) -> list[str] | None:
    """Every release tag in this checkout, or ``None`` if git can't say.

    ``None`` means "no evidence", NOT "zero releases" — a checkout whose
    tags were never fetched must stand the check down rather than report
    every documented count as wrong.  The `lint` job that runs this
    script checks out with `fetch-depth: 0` (it needs full history for
    `check_changelog_updated.py`'s `origin/main` diff), so the tags are
    there in CI; this is the guard for anywhere they are not.
    """
    try:
        result = subprocess.run(
            ["git", "-C", str(root), "tag", "--list"],
            capture_output=True,
            text=True,
            encoding="utf-8",
            timeout=30,
            check=False,
            env=git_env(),
        )
    except (OSError, subprocess.SubprocessError):
        return None
    if result.returncode != 0:
        return None
    tags = [t for t in result.stdout.split() if _RELEASE_TAG.match(t)]
    return tags or None


def check_release_count(
    readme_text: str,
    history_text: str,
    tags: list[str] | None,
    version: str,
) -> list[str]:
    """The release count in README.md and HISTORY.md, against the tags.

    The same hand-maintained number appears in two places — README's
    status line and HISTORY's "By the numbers" total — so they can
    disagree, and did (204/203, then 205/203).  Cross-checking them
    against each other closed that, and nothing else: from v0.1.8 both
    said 206 while the repository held 207 tags, agreeing with each
    other the whole way down.  Two documents can be consistently wrong,
    so the tags themselves are the oracle here.

    The one permitted gap is the release being cut: `release.yml`
    creates `vX.Y.Z` only after the merge, so on the PR that bumps
    `version` to an untagged release the documented count is one ahead
    of `git tag` — that is the convention (a release bumps both), not
    drift.  Once the version IS tagged, the counts must match exactly.
    """
    errors: list[str] = []
    m_readme = re.search(r"(\d+) releases,", readme_text)
    m_history = re.search(r"(\d+) tagged releases", history_text)
    if not m_readme:
        errors.append(
            "README.md: release count ('N releases,') not found"
            " — the status line was reworded and is no longer gated"
        )
    if not m_history:
        errors.append(
            "HISTORY.md: release count ('N tagged releases') not found"
            " — the totals line was reworded and is no longer gated"
        )
    if m_readme and m_history and m_readme.group(1) != m_history.group(1):
        errors.append(
            f"release count mismatch: README.md says {m_readme.group(1)},"
            f" HISTORY.md says {m_history.group(1)} tagged releases"
        )
    if tags is None:
        return errors

    pending = 0 if f"v{version}" in set(tags) else 1
    expected = len(tags) + pending
    for label, match in (("README.md", m_readme), ("HISTORY.md", m_history)):
        if match is None or int(match.group(1)) == expected:
            continue
        errors.append(
            f"{label}: release count says {match.group(1)}, live is"
            f" {expected} ({len(tags)} tags"
            + (f" + v{version} pending" if pending else "")
            + ")"
        )
    return errors


def check_conformance_skip_total(root: Path) -> list[str]:
    """Gate TESTING.md's conformance-stage skip total against its table.

    The "Skipped tests" section states a total and then enumerates every
    skipped stage, one row each — two statements of the same number, so
    they can disagree.  They did: three check-level conformance programs
    added six rows and the total stayed at 85 while the table said 91
    (PR #1282 review).  Nothing read either number, which is the same
    blind spot the corpus counts had.

    Checked against the ROW COUNT rather than by running pytest: the
    rows are what a reader is counting, the comparison is free, and the
    suite already proves the rows match reality (a wrong row is a
    skipped test that does not exist).  A reworded total is an error,
    not a skip.
    """
    errors: list[str] = []
    text = (root / "TESTING.md").read_text(encoding="utf-8")
    lines = text.splitlines()
    try:
        start = next(i for i, ln in enumerate(lines)
                     if ln.startswith("### Skipped tests"))
    except StopIteration:
        return ["TESTING.md: no '### Skipped tests' section — it moved or"
                " was renamed, so its total is no longer gated"]
    end = next(
        (i for i, ln in enumerate(lines[start + 1:], start + 1)
         if ln.startswith("## ")),
        len(lines),
    )
    section = lines[start:end]
    rows = [ln for ln in section if ln.startswith("| `test_")]

    m = re.search(
        r"skips ([\d,]+) conformance-stage tests", "\n".join(section))
    if not m:
        errors.append(
            "TESTING.md: the 'skips N conformance-stage tests' sentence was"
            " not found — it moved or was reworded, so it is no longer gated"
        )
    else:
        cited = int(m.group(1).replace(",", ""))
        if cited != len(rows):
            errors.append(
                f"TESTING.md conformance-stage skips: doc says {cited},"
                f" the table below it lists {len(rows)}"
            )
    return errors


def check_corpus_count(root: Path) -> list[str]:
    """Gate the cited corpus-program count in every document that states it.

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

    TESTING.md was the only document gated, and CLAUDE.md and AGENTS.md then
    went stale for exactly that reason: both cite the count in the comment on
    the command that runs the script, and a fix driven by this script's own
    output could not see them (adversarial review of PR C.6).  All three are
    read here, each keyed on the script name.  Every pattern is anchored on
    surrounding TEXT rather than on a bare numeral: a document-wide numeric
    substitution is not safe, `E207` being a live example of a token this
    count's own digits sit inside.

    A citation that is reworded away is an ERROR, not a skip — a silent skip
    is the failure mode the gate exists to prevent.  That is checked PER ROW,
    not per document: TESTING.md cites the count twice, and a
    "at least one row still matches" test greened while one of the two was
    reworded into invisibility (PR #1282 review).  Each document therefore
    declares how many citations it is expected to carry, and a mismatch in
    either direction is reported — a citation lost to rewording, or a new one
    added without being counted here.
    """
    errors: list[str] = []
    live = sum(
        len(list((root / d).rglob("*.vera")))
        for d in ("examples", "tests/conformance")
    )
    # (document, pattern, expected number of citations, what it anchors on)
    sites = (
        # Two table rows: | `check_corpus_canonical.py` | All N ... |
        ("TESTING.md",
         r"`check_corpus_canonical\.py`[^|\n]*\|[^|\n]*?All (\d+)\b",
         2, "table row"),
        # A command-block comment: python scripts/check_corpus_canonical.py
        # # Verify all N corpus programs ... / # All N corpus programs ...
        ("CLAUDE.md",
         r"check_corpus_canonical\.py[^\n]*?\ball (\d+) corpus programs",
         1, "command comment"),
        ("AGENTS.md",
         r"check_corpus_canonical\.py[^\n]*?\ball (\d+) corpus programs",
         1, "command comment"),
    )
    for doc, pattern, expected, anchor in sites:
        text = (root / doc).read_text(encoding="utf-8")
        rows = re.findall(pattern, text, re.IGNORECASE)
        if len(rows) != expected:
            errors.append(
                f"{doc}: expected {expected} `check_corpus_canonical.py`"
                f" {anchor}(s) stating a corpus count, found {len(rows)} —"
                f" one moved or was reworded (so it is no longer gated), or"
                f" a new citation needs adding to check_corpus_count's"
                f" expected count"
            )
        for cited in rows:
            if int(cited) != live:
                errors.append(
                    f"{doc} corpus count: doc says {cited}, live is {live}"
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


# ---------------------------------------------------------------------------
# README's project-status line
#
# One sentence carries six live figures and the oracle read one of them.  The
# `check_readme` closure it used returned silently when a pattern matched
# nothing, and four of its five patterns matched nothing at all — so the
# conformance count beside the gated tests count drifted through two rebases
# unseen.  Every figure on the line is gated here, and a figure that has gone
# missing is an error rather than a skip.
# ---------------------------------------------------------------------------

_STATUS_LINE = re.compile(r"^.*?\btests, \d+% Python code coverage.*$", re.M)
_STATUS_FIGURES = (
    (r"([\d,]+) tests,", "tests"),
    (r"([\d,]+) conformance programs", "conformance programs"),
    (r"([\d,]+) examples", "examples"),
    (r"(\d+)-chapter specification", "spec chapters"),
)


def check_project_status(
    readme_text: str,
    live_tests: int,
    live_conformance: int,
    live_examples: int,
    live_chapters: int,
) -> list[str]:
    """Check every count on README.md's project-status line."""
    line = _STATUS_LINE.search(readme_text)
    if line is None:
        return [
            "README.md: could not find the project-status line "
            "(`… tests, N% Python code coverage …`)"
        ]
    expected = (live_tests, live_conformance, live_examples, live_chapters)
    errors: list[str] = []
    for (pattern, label), live in zip(_STATUS_FIGURES, expected, strict=True):
        found = re.search(pattern, line.group(0))
        if found is None:
            errors.append(
                f"README.md project-status line: could not find the {label} count"
            )
            continue
        cited = int(found.group(1).replace(",", ""))
        if cited != live:
            errors.append(
                f"README.md project-status {label}: doc says {cited}, live is {live}"
            )
    return errors


# ---------------------------------------------------------------------------
# TESTING.md's dual-target conformance row
#
# The row states a run-level total, a tested/skipped split and three category
# counts.  The total has an oracle in the conformance manifest; the rest had
# none, and the row explicitly claims the excluded set is "defined by those
# three properties rather than by a filename list, so it stays accurate as
# programs are added" — a claim that only holds if something measures it.  The
# split comes from a live `-rs` run of the differential, about three seconds.
# ---------------------------------------------------------------------------


class DualTargetSplit(NamedTuple):
    """What a live run of the dual-target differential actually did."""

    tested: int
    skipped: int
    families: int
    no_main: int
    nondeterministic: int


_DUAL_TARGET_TEST = "tests/test_wasi_target.py::TestDualTargetConformance"
_SKIP_REASONS = (
    ("families", "host famil"),
    ("no_main", "zero-argument"),
    ("nondeterministic", "nondeterministic ops"),
)
_SKIP_LINE = re.compile(r"^SKIPPED \[(\d+)\] (.*)$", re.M)
# pytest omits a category with a zero count, so "174 passed in 3.1s" and
# "52 skipped in 3.1s" are both well-formed summaries.  A pattern
# requiring both made either one unreadable, and an unreadable report is
# a gate failure — a false one (#1329 review).
_PYTEST_TOTALS = re.compile(r"(\d+) (passed|skipped)\b")
_PYTEST_SUMMARY = re.compile(r"\d+ (?:passed|skipped)\b[^\n]*\bin [\d.]+s")
_DUAL_TARGET_FIGURES = (
    ("tested", r"(\d+) are dual-tested"),
    ("skipped", r"and (\d+) skip"),
    ("families", r"(\d+) whose compiled WAT"),
    ("no_main", r"(\d+) with no public zero-argument"),
    ("nondeterministic", r"and (\d+) calling a nondeterministic op"),
)


def parse_dual_target_report(report: str) -> DualTargetSplit | None:
    """Read a split out of pytest's ``-rs`` output, or ``None``.

    ``None`` means the run cannot be read — no summary line, or a skip whose
    reason matches none of the three documented properties.  A new skip reason
    is exactly the case the row's "stays accurate as programs are added" claim
    needs to hear about, so it must not be silently folded into a category.
    """
    summary = _PYTEST_SUMMARY.search(report)
    if summary is None:
        return None
    totals = {kind: int(n) for n, kind in _PYTEST_TOTALS.findall(summary.group(0))}
    counts = dict.fromkeys((name for name, _ in _SKIP_REASONS), 0)
    for raw, reason in _SKIP_LINE.findall(report):
        for name, marker in _SKIP_REASONS:
            if marker in reason:
                counts[name] += int(raw)
                break
        else:
            return None
    skipped = totals.get("skipped", 0)
    if sum(counts.values()) != skipped:
        return None
    return DualTargetSplit(totals.get("passed", 0), skipped, **counts)


def dual_target_split(root: Path) -> DualTargetSplit | None:
    """Run the dual-target differential and report what it did."""
    pytest_bin = root / ".venv/bin/pytest"
    if not pytest_bin.exists():
        pytest_bin = Path("pytest")
    try:
        result = subprocess.run(
            [str(pytest_bin), _DUAL_TARGET_TEST, "-q", "-rs", "-p", "no:randomly"],
            capture_output=True,
            text=True,
            encoding="utf-8",
            cwd=str(root),
            timeout=300,
            check=False,
        )
    except (OSError, subprocess.SubprocessError):
        # Every other check here turns a failure into a string in `errors`
        # and lets `main` print the whole list.  Letting this one raise
        # would end the run on a traceback and the other twenty checks
        # would never report — and this call is on the default path, so
        # the pre-commit hook takes it every time (#1329 review).
        return None
    if result.returncode != 0:
        return None
    return parse_dual_target_report(result.stdout)


def check_dual_target_row(
    testing_text: str, run_level_total: int, split: DualTargetSplit
) -> list[str]:
    """Check TESTING.md's dual-target row against the manifest and a run."""
    errors: list[str] = []
    cited_total = re.search(r"all ([\d,]+) run-level", testing_text)
    if cited_total is None:
        errors.append(
            "TESTING.md: could not find the dual-target run-level total "
            "(`all N run-level conformance programs`)"
        )
    elif int(cited_total.group(1).replace(",", "")) != run_level_total:
        errors.append(
            f"TESTING.md dual-target run-level total: doc says "
            f"{cited_total.group(1)}, manifest has {run_level_total}"
        )

    cited: dict[str, int] = {}
    for name, pattern in _DUAL_TARGET_FIGURES:
        found = re.search(pattern, testing_text)
        if found is None:
            errors.append(
                f"TESTING.md dual-target row: could not find the {name} count"
            )
            continue
        cited[name] = int(found.group(1))
        if cited[name] != getattr(split, name):
            errors.append(
                f"TESTING.md dual-target {name}: doc says {cited[name]}, "
                f"a live run has {getattr(split, name)}"
            )
    if len(cited) == len(_DUAL_TARGET_FIGURES):
        if cited["tested"] + cited["skipped"] != run_level_total:
            errors.append(
                f"TESTING.md dual-target row does not add up: "
                f"{cited['tested']} + {cited['skipped']} is not {run_level_total}"
            )
        categories = cited["families"] + cited["no_main"] + cited["nondeterministic"]
        if categories != cited["skipped"]:
            errors.append(
                f"TESTING.md dual-target skip categories do not add up: "
                f"{categories} is not {cited['skipped']}"
            )
    return errors


# ---------------------------------------------------------------------------
# KNOWN_ISSUES' Bugs table against the tracker
#
# The convention is one row per open `bug`-labelled issue.  Two halves, and
# they are separated on purpose: the structural half is pure text and runs
# always, while the parity half needs the GitHub API and a pre-commit hook must
# not depend on a network call — it is opt-in via `--check-bug-issues`, for the
# release PR, where the tracker and the file are meant to agree.  Mid-burndown
# they legitimately do not: a bug filed on an open PR's branch has an issue
# before it has a row.
# ---------------------------------------------------------------------------

_BUGS_SECTION = re.compile(r"^## Bugs[ \t]*$(.*?)(?=^## |\Z)", re.M | re.S)
_ISSUE_LINK = re.compile(r"\[#(\d+)\]\(https://github\.com/[\w.-]+/[\w.-]+/issues/(\d+)\)")
_NO_BUGS = "No known bugs."


def bug_rows(known_issues_text: str) -> list[int] | None:
    """Issue numbers from the Bugs table's Issue column, in order.

    The Issue column is a row's canonical tracker, and it is the only place
    read: rows cross-link other issues in their prose, and counting those
    would make one bug's context read as another bug's row.

    ``[]`` is the documented empty state — the section body is exactly "No
    known bugs." — and ``None`` means the section could not be read at all.
    The two are different problems and a caller must not conflate them.
    """
    section = _BUGS_SECTION.search(known_issues_text)
    if section is None:
        return None
    body = section.group(1).strip()
    if body == _NO_BUGS:
        return []
    numbers: list[int] = []
    for line in body.splitlines():
        if not line.startswith("|") or set(line) <= set("|- "):
            continue
        cells = [cell.strip() for cell in line.strip().strip("|").split("|")]
        if cells[-1] == "Issue":
            continue
        # The last cell, so prose carrying a `|` cannot shift the column.
        links = [
            int(number)
            for number, url_number in _ISSUE_LINK.findall(cells[-1])
            if number == url_number
        ]
        if len(links) != 1:
            return None
        numbers.append(links[0])
    return numbers or None


def check_faq_example_count(faq_text: str, live_examples: int) -> list[str]:
    """FAQ.md's by-the-numbers example bullet against the live count.

    The same list's TEST bullet was already pinned, and its CONFORMANCE
    bullet before that — each added only after the unpinned half had
    drifted.  The example bullet went stale the same way, so it is pinned
    here rather than left as the third instance of one lesson.  A missing
    pattern is an error, not a skip: rewording the line would otherwise
    disable the check and reopen the blind spot one level up.
    """
    errors: list[str] = []
    # Anchored to the by-the-numbers BULLET, not to the phrase.  An unanchored
    # search takes the first occurrence anywhere in the page, so prose above
    # the list that happens to say "N working example programs" would be
    # validated instead of the bullet -- the check would then be green while
    # the bullet itself was stale.  Zero matches and MULTIPLE matches are both
    # errors: a second bullet means the page has two answers and this function
    # cannot say which one the reader believes.
    found = re.findall(
        r"^- ([\d,]+) working example programs\s*$", faq_text, re.MULTILINE
    )
    if not found:
        return [
            "FAQ.md: example-count bullet"
            " ('- N working example programs') not found"
        ]
    if len(found) > 1:
        return [
            f"FAQ.md: example-count bullet appears {len(found)} times"
            f" ({', '.join(found)}); expected exactly one"
        ]
    doc_examples = int(found[0].replace(",", ""))
    if doc_examples != live_examples:
        errors.append(
            f"FAQ.md: example count: doc says {doc_examples},"
            f" live is {live_examples}"
        )
    return errors


def check_bug_rows(known_issues_text: str) -> list[str]:
    """Check the Bugs table's shape: one well-formed, unique issue per row."""
    numbers = bug_rows(known_issues_text)
    if numbers is None:
        return [
            "KNOWN_ISSUES.md: the `## Bugs` table was not found, or a row's "
            "Issue column does not hold exactly one `[#N](…/issues/N)` link. "
            "An empty section is written `No known bugs.`"
        ]
    duplicates = sorted({n for n in numbers if numbers.count(n) > 1})
    return [
        f"KNOWN_ISSUES.md: issue #{number} has a Bugs row twice"
        for number in duplicates
    ]


# ---------------------------------------------------------------------------
# ROADMAP's burndown header word vs. the burndown table vs. KNOWN_ISSUES'
# Bugs table (#1370-class): three independent counts of "how many open bugs
# are there right now" that must read as one fact.  Two parallel PRs each
# hand-wrote the header word from their own stale count on the same night —
# whichever merged second was wrong, and nothing caught it.  This gate makes
# the drift structural: the header word is PARSED into a number (not
# eyeballed), and compared against both row counts.
# ---------------------------------------------------------------------------

_ROADMAP_BURNDOWN_SECTION = re.compile(
    r"^## The v[\d.]+ burndown[ \t]*$(.*?)(?=^## |\Z)", re.M | re.S
)
_BURNDOWN_HEADER = re.compile(
    r"^\*([A-Za-z-]+) open bugs, driven to zero\.\*[ \t]*$", re.M
)

_ONES_WORDS = {
    "zero": 0, "one": 1, "two": 2, "three": 3, "four": 4, "five": 5,
    "six": 6, "seven": 7, "eight": 8, "nine": 9, "ten": 10, "eleven": 11,
    "twelve": 12, "thirteen": 13, "fourteen": 14, "fifteen": 15,
    "sixteen": 16, "seventeen": 17, "eighteen": 18, "nineteen": 19,
}
_TENS_WORDS = {
    "twenty": 20, "thirty": 30, "forty": 40, "fifty": 50, "sixty": 60,
    "seventy": 70, "eighty": 80, "ninety": 90,
}


def _english_number_word_to_int(word: str) -> int | None:
    """Parse an English number word (0-99, including a hyphenated
    compound like 'twenty-one') into an int, or None if `word` is not
    one.  Deliberately small (this repo's bug count is never going to
    need "one hundred") rather than pulling in a parsing dependency
    for a single doc sentence."""
    lowered = word.lower()
    if lowered in _ONES_WORDS:
        return _ONES_WORDS[lowered]
    if lowered in _TENS_WORDS:
        return _TENS_WORDS[lowered]
    if "-" in lowered:
        tens_part, _, ones_part = lowered.partition("-")
        if tens_part in _TENS_WORDS and ones_part in _ONES_WORDS:
            return _TENS_WORDS[tens_part] + _ONES_WORDS[ones_part]
    return None


def roadmap_burndown_rows(roadmap_text: str) -> list[int] | None:
    """Issue numbers from the CURRENT '## The vX.Y.Z burndown' table's
    Issue column, in the same shape `bug_rows` reads KNOWN_ISSUES.md's
    Bugs table — reused so the two are compared like for like."""
    section = _ROADMAP_BURNDOWN_SECTION.search(roadmap_text)
    if section is None:
        return None
    numbers: list[int] = []
    for line in section.group(1).splitlines():
        if not line.startswith("|") or set(line) <= set("|- "):
            continue
        cells = [cell.strip() for cell in line.strip().strip("|").split("|")]
        if cells[0] == "Issue":
            continue
        links = [
            int(number)
            for number, url_number in _ISSUE_LINK.findall(cells[0])
            if number == url_number
        ]
        if len(links) != 1:
            return None
        numbers.append(links[0])
    return numbers or None


def check_burndown_header_matches_rows(
    roadmap_text: str, known_issues_text: str,
) -> list[str]:
    """The burndown header word, the burndown table's row count, and
    KNOWN_ISSUES.md's Bugs table row count must all agree — three
    numbers, one fact.  A mismatch on any pair is reported together
    (not as separate errors per pair) so the message reads as the one
    underlying disagreement it is."""
    section = _ROADMAP_BURNDOWN_SECTION.search(roadmap_text)
    if section is None:
        return ["ROADMAP.md: could not find '## The vX.Y.Z burndown' section"]

    header_match = _BURNDOWN_HEADER.search(section.group(1))
    if header_match is None:
        return [
            "ROADMAP.md: burndown section has no "
            "'*<Word> open bugs, driven to zero.*' header line"
        ]
    header_word = header_match.group(1)
    header_number = _english_number_word_to_int(header_word)
    if header_number is None:
        return [
            f"ROADMAP.md: burndown header word {header_word!r} is not a "
            "recognised English number word (0-99)"
        ]

    burndown_rows = roadmap_burndown_rows(roadmap_text)
    if burndown_rows is None:
        return ["ROADMAP.md: burndown table has no issue rows"]

    bugs = bug_rows(known_issues_text)
    if bugs is None:
        return [
            "KNOWN_ISSUES.md: the `## Bugs` table was not found — cannot "
            "cross-check against ROADMAP.md's burndown header"
        ]

    values = {
        "burndown header word": header_number,
        "burndown table rows": len(burndown_rows),
        "KNOWN_ISSUES.md Bugs table rows": len(bugs),
    }
    if len(set(values.values())) > 1:
        detail = ", ".join(f"{k} = {v}" for k, v in values.items())
        return [
            f"ROADMAP.md burndown header {header_word!r} does not match "
            f"the row counts it should agree with: {detail}"
        ]
    return []


def check_bug_issue_parity(rows: list[int], open_bugs: list[int]) -> list[str]:
    """Check the Bugs table against the open `bug`-labelled issues."""
    if not open_bugs:
        return [
            "KNOWN_ISSUES.md: an open `bug`-labelled issue was not found at "
            "all, so the Bugs table has nothing to be checked against. An "
            "empty query is a failed one, not a clean bill of health."
        ]
    errors = [
        f"KNOWN_ISSUES.md: issue #{number} is an open bug with no Bugs row"
        for number in sorted(set(open_bugs) - set(rows))
    ]
    errors += [
        f"KNOWN_ISSUES.md: the Bugs row for #{number} is not an open bug issue"
        for number in sorted(set(rows) - set(open_bugs))
    ]
    return errors


class BugQueryError(RuntimeError):
    """The tracker could not be queried — a failed run, not an empty one."""


def open_bug_issues(repo: str = "aallan/vera") -> list[int]:
    """Open issue numbers carrying the `bug` label, from the GitHub API.

    Raises `BugQueryError` rather than returning `[]` on a transport or
    payload failure.  `check_bug_issue_parity` reads an empty list as
    "the query failed", so returning one here would reach the right
    verdict for the wrong reason — and the caller could no longer tell a
    burned-down tracker from an unreachable one (#1329 review).
    """
    numbers: list[int] = []
    for page in range(1, 11):
        url = (
            f"https://api.github.com/repos/{repo}/issues"
            f"?labels=bug&state=open&per_page=100&page={page}"
        )
        request = Request(url, headers={"User-Agent": "vera-doc-counts/1"})
        token = os.environ.get("GH_TOKEN") or os.environ.get("GITHUB_TOKEN")
        if token:
            request.add_header("Authorization", f"Bearer {token}")
        try:
            # The URL is built from a caller-supplied repository, not input.
            with urlopen(request, timeout=30) as response:
                payload = json.load(response)
        except (OSError, ValueError) as exc:
            # URLError and HTTPError are OSError; a socket timeout is too,
            # and a malformed body raises JSONDecodeError, a ValueError.
            raise BugQueryError(f"could not query {repo} for open bugs: {exc}") from exc
        if not payload:
            break
        numbers += [
            item["number"] for item in payload if "pull_request" not in item
        ]
    return numbers


_ERROR_CODES_CITATION = re.compile(
    r"maps every code to a short description \((\d+) entries — (\d+) `E` codes "
    r"and the two `W` warning codes\)"
)


def check_error_codes_count(readme_text: str, registry: dict[str, object]) -> list[str]:
    """Check vera/README.md's `ERROR_CODES` figures against the registry.

    Three numbers in one sentence, and none was gated: the total, the `E`
    count, and the claim that the remainder is exactly the two `W` codes.
    The registry is the only source for any of them, so the sentence could
    drift on every code added (#1330 review).
    """
    found = _ERROR_CODES_CITATION.search(readme_text)
    if found is None:
        return [
            "vera/README.md: could not find the ERROR_CODES count sentence "
            "('maps every code to a short description (N entries — N `E` "
            "codes and the two `W` warning codes)')"
        ]
    cited_total, cited_e = (int(g) for g in found.groups())
    live_e = sum(1 for code in registry if code.startswith("E"))
    live_w = sum(1 for code in registry if code.startswith("W"))
    errors: list[str] = []
    if cited_total != len(registry):
        errors.append(
            f"vera/README.md ERROR_CODES total: doc says {cited_total}, "
            f"live is {len(registry)}"
        )
    if cited_e != live_e:
        errors.append(
            f"vera/README.md ERROR_CODES E-code count: doc says {cited_e}, "
            f"live is {live_e}"
        )
    if live_w != 2:
        errors.append(
            f"vera/README.md says the remainder is two `W` codes; the "
            f"registry has {live_w}"
        )
    return errors


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--check-bug-issues",
        action="store_true",
        help=(
            "also check KNOWN_ISSUES.md's Bugs table against the open "
            "`bug`-labelled issues (needs the GitHub API; for the release PR, "
            "not for pre-commit)"
        ),
    )
    args = parser.parse_args()
    root = Path(__file__).resolve().parent.parent
    # This script's several `from vera...` imports below are IN-PROCESS,
    # unlike the pytest/subprocess calls above that already pin
    # `root / ".venv/bin/pytest"` (falling back to PATH only if that venv
    # is absent).  A plain `import vera` instead falls through to
    # whichever venv's editable-install finder answers first — a
    # `__editable__.veralang-*.pth` file pinned to WHATEVER checkout `pip
    # install -e` last ran in, which can be a different worktree entirely
    # (that finder only engages when nothing earlier on `sys.path` already
    # resolved `vera`).  Inserting `root` here — ahead of site-packages,
    # so ahead of that finder — makes `vera` resolve as the plain on-disk
    # package under `root/vera/` instead: unambiguously the tree this
    # script's own `__file__` lives in, regardless of which interpreter or
    # editable install happens to be active.  The equivalent trap on the
    # pytest side (a test file measuring the wrong checkout because
    # pytest's OWN rootdir detection wins) is documented in TESTING.md's
    # "Running against ANOTHER checkout" section — a different mechanism
    # with a different remedy (relocate the test file into the target
    # tree), not this one.
    sys.path.insert(0, str(root))
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
    errors.extend(check_tests_breakdown(testing_md, live_total_tests))

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
        r"configures (\d+) hooks",
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

    # The lint job's contents, not just the job count: the row enumerates
    # every script that job runs, and nothing held the two in step.
    errors.extend(check_ci_lint_scripts(testing_md, ci_text))

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

    errors.extend(check_contributing_hook_count(contrib_md, live_hooks))

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

    # One sentence carries six live figures.  Its four countable ones are
    # gated together, each an error when it goes missing: the four patterns
    # that used to sit here beside the tests one matched no README text at
    # all, and returned silently rather than saying so.
    errors.extend(
        check_project_status(
            readme_md,
            live_total_tests,
            live_conformance,
            live_examples,
            len(list((root / "spec").glob("*.md"))),
        )
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

    errors.extend(check_faq_example_count(faq_md, live_examples))

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
    # both.  They are checked against each other AND against `git tag`,
    # because agreeing with each other is what they did all the way from
    # v0.1.8 while both were two behind the repository.
    tags = release_tags(root)
    if tags is None:
        print(
            "NOTE: no release tags in this checkout — the release count"
            " was cross-checked between README.md and HISTORY.md only.",
            file=sys.stderr,
        )
    errors.extend(
        check_release_count(
            readme_md, history_md, tags, project_version(root)
        )
    )

    # ------------------------------------------------------------------
    # 17. Check the vera/README.md module map against the source tree
    # ------------------------------------------------------------------

    vera_readme_md = (root / "vera/README.md").read_text(encoding="utf-8")
    errors.extend(check_module_map(vera_readme_md, root))
    errors.extend(
        check_vera_readme_test_counts(
            vera_readme_md,
            live_total_tests,
            live_test_files,
            live_conformance,
            live_examples,
        )
    )

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

    from vera.errors import ERROR_CODES

    errors.extend(check_error_codes_count(vera_readme_md, ERROR_CODES))
    errors.extend(check_corpus_count(root))
    errors.extend(check_conformance_skip_total(root))

    # ------------------------------------------------------------------
    # 20. Check TESTING.md's dual-target row against a live run
    # ------------------------------------------------------------------

    split = dual_target_split(root)
    if split is None:
        errors.append(
            f"TESTING.md: the dual-target differential ({_DUAL_TARGET_TEST}) "
            f"could not be read — it failed, or it skipped for a reason the "
            f"row's three documented properties do not cover"
        )
    else:
        errors.extend(
            check_dual_target_row(testing_md, level_counts.get("run", 0), split)
        )

    # ------------------------------------------------------------------
    # 21. Check KNOWN_ISSUES.md's Bugs table
    # ------------------------------------------------------------------

    known_issues = (root / "KNOWN_ISSUES.md").read_text(encoding="utf-8")
    errors.extend(check_bug_rows(known_issues))
    errors.extend(check_burndown_header_matches_rows(roadmap_md, known_issues))
    if args.check_bug_issues:
        rows = bug_rows(known_issues)
        if rows is not None:
            try:
                errors.extend(check_bug_issue_parity(rows, open_bug_issues()))
            except BugQueryError as exc:
                errors.append(f"KNOWN_ISSUES.md: {exc}")

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
