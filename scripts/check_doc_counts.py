#!/usr/bin/env python
"""The documentation's release-time checks.

No gate compares two hand-written copies of a count: a count lives in one
place, TESTING.md's generated status, which ``scripts/render_status.py``
writes from the tree, and no other document states one.  Between releases
the generated status may lag the tree, so a fix PR or a commit has nothing
to keep in step.  What is left is checked when a release is cut:

- ``--release`` (the release PR): TESTING.md's generated blocks are what
  ``render_status.py`` writes now.  CI passes ``--release-if-version-raised
  <base>``, which turns release mode on exactly when ``[project].version``
  rose against the base: a pull request against its base branch, a push
  against the commit before it (#1536).  In the default mode the script
  checks nothing.
- ``--check-bug-issues``: KNOWN_ISSUES.md's Bugs table carries one row per
  open `bug`-labelled issue.  It needs the GitHub API, so it is opt-in, for
  the release PR.
- ``--print-release-mode <base>`` prints the release-mode answer alone, as a
  ``release=true`` or ``release=false`` line, and checks nothing: ci.yml's
  plan job reads it to decide whether the push event a merge produces on
  ``main`` runs the whole test matrix.
"""

import argparse
import importlib.util
import json
import os
import re
import subprocess
import sys
import tomllib
from pathlib import Path
from types import ModuleType
from urllib.request import Request, urlopen


def parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--check-bug-issues",
        action="store_true",
        help=(
            "also check KNOWN_ISSUES.md's Bugs table against the open "
            "`bug`-labelled issues (needs the GitHub API; for the release PR)"
        ),
    )
    parser.add_argument(
        "--release",
        action="store_true",
        help=(
            "check that TESTING.md's generated status is what "
            "scripts/render_status.py writes now (the release PR)"
        ),
    )
    parser.add_argument(
        "--release-if-version-raised",
        metavar="BASE",
        help=(
            "run in --release mode when pyproject.toml's [project].version is "
            "higher than at BASE: a branch name (read as origin/BASE, as a CI "
            "checkout has it) or a commit.  CI passes a pull request's base "
            "branch and a push's previous commit (#1536)"
        ),
    )
    parser.add_argument(
        "--print-release-mode",
        metavar="BASE",
        help=(
            "print `release=true` or `release=false`, the answer "
            "--release-if-version-raised acts on for BASE, and exit without "
            "checking any document; ci.yml's plan job reads the line as a "
            "step output"
        ),
    )
    return parser.parse_args(argv)


# ---------------------------------------------------------------------------
# Release mode keys on the version bump (#1536).  The release PR is the pull
# request that raises `[project].version` against its base — the same signal
# `release.yml` publishes on — so the choice does not depend on which branch
# fix PRs target.
# ---------------------------------------------------------------------------


class ReleaseModeError(Exception):
    """The base's version could not be read, so the mode cannot be chosen.

    Raised rather than answered "not a release": a base that reads as
    nothing would otherwise skip the release checks on the release PR.
    """


_NO_PREVIOUS_COMMIT = re.compile(r"^0{40}$")


def _project_version(pyproject_text: str) -> tuple[int, ...]:
    try:
        version = tomllib.loads(pyproject_text)["project"]["version"]
        parts = tuple(int(part) for part in str(version).split("."))
    except (tomllib.TOMLDecodeError, KeyError, TypeError, ValueError) as exc:
        raise ValueError(f"no readable [project].version ({exc})") from exc
    if not parts:
        raise ValueError("an empty [project].version")
    return parts


def version_raised(base_pyproject: str, head_pyproject: str) -> bool:
    """Whether the head's `[project].version` is higher than the base's,
    compared as numbers (`0.2.10` is above `0.2.9`)."""
    return _project_version(head_pyproject) > _project_version(base_pyproject)


def _pyproject_at(ref: str, root: Path) -> str | None:
    # `GIT_*` from a hook names the repository the hook runs in; this reads
    # the tree at `root`, whichever that is.
    env = {k: v for k, v in os.environ.items() if not k.startswith("GIT_")}
    for candidate in (f"origin/{ref}", ref):
        # Bounded, like every other subprocess here: this runs in CI and a
        # blocked git would hang the job.  A candidate git could not answer
        # for is unreadable, so a base that yields none reaches the caller's
        # `ReleaseModeError` rather than a hang or a traceback.
        try:
            result = subprocess.run(
                ["git", "show", f"{candidate}:pyproject.toml"],
                cwd=root, env=env, capture_output=True, text=True, check=False,
                encoding="utf-8", timeout=30,
            )
        except (OSError, subprocess.SubprocessError):
            continue
        if result.returncode == 0:
            return result.stdout
    return None


def release_mode_for(base: str, root: Path) -> tuple[bool, str]:
    """Whether the tree at `root` raises the version against `base`, and
    the reason, for the log.

    A push that creates a branch has no previous commit (an all-zero SHA),
    so it has no version to raise and runs in the default mode.  Any other
    base that does not resolve is an error.
    """
    if _NO_PREVIOUS_COMMIT.match(base):
        return False, "no previous commit (a new branch)"
    if not base:
        raise ReleaseModeError("no base was given to compare the version with")
    base_text = _pyproject_at(base, root)
    if base_text is None:
        raise ReleaseModeError(
            f"cannot read pyproject.toml at {base!r} (tried origin/{base} "
            f"and {base})"
        )
    head_text = (root / "pyproject.toml").read_text(encoding="utf-8")
    try:
        raised = version_raised(base_text, head_text)
        old = ".".join(map(str, _project_version(base_text)))
        new = ".".join(map(str, _project_version(head_text)))
    except ValueError as exc:
        raise ReleaseModeError(str(exc)) from exc
    verdict = "raised" if raised else "not raised"
    return raised, f"[project].version {old} -> {new} against {base}: {verdict}"


# ---------------------------------------------------------------------------
# The generated status, fresh at release.  The measuring and the rendering
# are render_status.py's; this script only asks whether the document holds
# what that script would write now.
# ---------------------------------------------------------------------------


def _render_status() -> ModuleType:
    path = Path(__file__).with_name("render_status.py")
    spec = importlib.util.spec_from_file_location("render_status", path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {path}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def stale_status(root: Path) -> list[str]:
    """Why TESTING.md's generated status is not what render_status.py
    writes now, one line per stale block; ``[]`` when it is current."""
    errors: list[str] = _render_status().stale_blocks(root)
    return errors


# ---------------------------------------------------------------------------
# KNOWN_ISSUES.md's Bugs table against the tracker, at release.
# ---------------------------------------------------------------------------

_BUGS_SECTION = re.compile(r"^## Bugs[ \t]*$(.*?)(?=^## |\Z)", re.M | re.S)
_ISSUE_LINK = re.compile(r"\[#(\d+)\]\(https://github\.com/[\w.-]+/[\w.-]+/issues/(\d+)\)")
_NO_BUGS = "No known bugs."


def _read_bug_table(body: str) -> list[int] | str:
    """Issue numbers from the `## Bugs` table, or why it could not be read.

    Only the Issue column, the LAST cell, is read: it is a row's canonical
    tracker, and rows cross-link other issues in their prose, which would
    otherwise read as other bugs' rows.  A last cell cannot be shifted by
    prose that carries a `|`.

    The zero state is a MARKER, not an absence (#1401): the section keeps
    its heading and its standing description of what the table is, the
    table is GONE, and the body's last line is `No known bugs.`.  A table
    emptied WITHOUT the marker stays unreadable, which is what keeps "the
    last row was deleted by accident" an error rather than a clean bill of
    health.

    The marker and a table cannot coexist, in either order: a section
    carrying both claims some open bugs and none at once (PR #1411
    review).  Any line starting with `|` counts, a leftover header and
    separator included.
    """
    table_lines = [line for line in body.splitlines() if line.startswith("|")]
    # The marker is compared as a whole stripped line, anywhere in the
    # body.  A substring test would accept it inside a sentence, and the
    # standing description is exactly the place that would one day quote
    # it; a last-line-only test would miss it above a table.
    lines = [line.strip() for line in body.splitlines() if line.strip()]
    marker_at = [index for index, line in enumerate(lines) if line == _NO_BUGS]
    if marker_at and table_lines:
        return (
            f"the section carries the `{_NO_BUGS}` marker AND "
            f"{len(table_lines)} table line(s), which claims both some open "
            f"bugs and none. The zero form has no table at all — not even a "
            f"leftover header row"
        )

    numbers: list[int] = []
    for line in table_lines:
        if set(line) <= set("|- "):
            continue
        cells = [cell.strip() for cell in line.strip().strip("|").split("|")]
        if cells[-1] == "Issue":
            continue
        links = [
            int(number)
            for number, url_number in _ISSUE_LINK.findall(cells[-1])
            if number == url_number
        ]
        if len(links) != 1:
            return (
                "the section has a row whose Issue column does not hold "
                "exactly one `[#N](…/issues/N)` link whose number matches its URL"
            )
        numbers.append(links[0])
    if numbers:
        return numbers
    if marker_at and marker_at[-1] == len(lines) - 1:
        return []
    if marker_at:
        return (
            f"the section carries the `{_NO_BUGS}` marker but does not END "
            f"with it. Text after the marker qualifies the claim, and the "
            f"check cannot know how"
        )
    return (
        f"the section has no issue rows and does not end with the "
        f"`{_NO_BUGS}` marker. A table driven to zero is written by keeping "
        f"the section's description, deleting the table, and ending the "
        f"section with that line on its own"
    )


def bug_rows(known_issues_text: str) -> list[int] | str:
    """Issue numbers from the Bugs table's Issue column, in order, or why
    the table cannot be read.

    ``[]`` is the documented empty state — the section keeps its heading
    and its description and ends with "No known bugs." — and a string is a
    section that could not be read at all.  The two are different problems
    and a caller must not conflate them.
    """
    section = _BUGS_SECTION.search(known_issues_text)
    if section is None:
        return "there is no `## Bugs` section"
    return _read_bug_table(section.group(1))


def check_bug_issue_parity(rows: list[int], open_bugs: list[int]) -> list[str]:
    """Check the Bugs table against the open `bug`-labelled issues.

    Zero on BOTH sides is the burndown's success state and passes: the
    file claims no open bugs and the tracker has none, which is the two
    agreeing (#1401).  What cannot pass is zero on the tracker side
    ALONE, because a query that came back empty is indistinguishable
    from one that failed — except that `open_bug_issues` raises
    `BugQueryError` rather than returning `[]` on a transport or payload
    failure, so the distinction is drawn where the query is made and an
    empty list reaching here is a real answer.  Rows without it are
    still reported, since a row for an issue the tracker does not carry
    as an open bug is wrong either way.
    """
    if not open_bugs and rows:
        return [
            "KNOWN_ISSUES.md: an open `bug`-labelled issue was not found at "
            f"all, so the Bugs table's {len(rows)} row(s) have nothing to be "
            "checked against. An empty query is a failed one, not a clean "
            "bill of health."
        ]
    bug_set, row_set = set(open_bugs), set(rows)
    matched = bug_set & row_set
    missing_rows = sorted(bug_set - row_set)
    errors = [
        f"KNOWN_ISSUES.md: issue #{number} is an open bug with no Bugs row"
        for number in missing_rows
    ]
    errors += [
        f"KNOWN_ISSUES.md: the Bugs row for #{number} is not an open bug issue"
        for number in sorted(row_set - bug_set)
    ]
    # Every open bug is either MATCHED (has a row) or reported above as a
    # missing row — matched and missing_rows partition open_bugs exactly,
    # by construction of the two set operations above.  This can only be
    # violated by a bug in that construction itself (a future refactor
    # that computes one of them some other way, or a type mismatch
    # between `rows` and `open_bugs` — e.g. one holding strings where the
    # other holds ints, which would make membership tests silently wrong
    # rather than raise) — not by any state KNOWN_ISSUES.md or the
    # tracker can be in, so this never fires against real data (#1377
    # review: "a dropped issue should surface as an inconsistency rather
    # than as silence").
    if len(matched) + len(missing_rows) != len(bug_set):
        errors.append(
            "KNOWN_ISSUES.md: internal inconsistency in the parity check "
            f"itself — {len(matched)} matched + {len(missing_rows)} "
            f"missing-row divergences should account for all "
            f"{len(bug_set)} open bugs; this is a bug in the "
            f"reconciliation logic, not in KNOWN_ISSUES.md"
        )
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


def check_bug_issues(root: Path) -> list[str]:
    """KNOWN_ISSUES.md's Bugs table against the open `bug` issues: one
    row per issue, so a second row for one issue is an error too."""
    rows = bug_rows((root / "KNOWN_ISSUES.md").read_text(encoding="utf-8"))
    if isinstance(rows, str):
        return [f"KNOWN_ISSUES.md: the Bugs table cannot be read: {rows}"]
    errors = [
        f"KNOWN_ISSUES.md: issue #{number} has a Bugs row twice"
        for number in sorted({n for n in rows if rows.count(n) > 1})
    ]
    try:
        return errors + check_bug_issue_parity(rows, open_bug_issues())
    except BugQueryError as exc:
        return [*errors, f"KNOWN_ISSUES.md: {exc}"]


def main() -> int:
    args = parse_args()
    root = Path(__file__).resolve().parent.parent
    # render_status.py imports `vera` in process (the registries, the
    # conformance tests): from this checkout, not whichever editable
    # install the interpreter would find first — a `__editable__` finder
    # pinned to another worktree, say.  Inserting `root` ahead of
    # site-packages before anything imports `vera` makes it the plain
    # on-disk package under `root/vera/`.
    sys.path.insert(0, str(root))

    if args.print_release_mode is not None:
        # The plan job's question: the answer alone, on stdout for
        # $GITHUB_OUTPUT, the reason on stderr for the log, and no document
        # measured.  A base that cannot be read fails the step rather than
        # answering either way.
        try:
            raised, why = release_mode_for(args.print_release_mode, root)
        except ReleaseModeError as exc:
            print(f"ERROR: release mode: {exc}", file=sys.stderr)
            return 1
        print(f"Release mode {'on' if raised else 'off'}: {why}.", file=sys.stderr)
        print(f"release={'true' if raised else 'false'}")
        return 0

    if args.release_if_version_raised is not None:
        try:
            raised, why = release_mode_for(args.release_if_version_raised, root)
        except ReleaseModeError as exc:
            print(f"ERROR: release mode: {exc}", file=sys.stderr)
            return 1
        print(f"Release mode {'on' if raised else 'off'}: {why}.")
        args.release = args.release or raised

    errors: list[str] = []
    if args.release:
        errors += stale_status(root)
    if args.check_bug_issues:
        errors += check_bug_issues(root)

    if errors:
        print(f"ERROR: {len(errors)} documentation check(s) failed:", file=sys.stderr)
        for err in errors:
            print(f"  {err}", file=sys.stderr)
        return 1
    checked = [
        name for name, on in (
            ("TESTING.md's generated status is current", args.release),
            ("KNOWN_ISSUES.md's Bugs table matches the tracker", args.check_bug_issues),
        ) if on
    ]
    if checked:
        print("; ".join(checked) + ".")
    else:
        print(
            "Nothing to check outside a release: the release PR regenerates"
            " TESTING.md's status (scripts/render_status.py) and checks it"
            " with --release."
        )
    return 0


if __name__ == "__main__":
    sys.exit(main())
