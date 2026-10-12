#!/usr/bin/env python
"""Check that every issue a limitation or bug table cites is still open.

The limitation tables are rendered from ``limitations.json`` by
``scripts/render_lists.py``, so there is no copy of them to compare; what
can still go stale is the tracker, when an issue a row cites is closed.
The issues the tables cite are:

  1. each issue a record in ``limitations.json`` names: the source of the
     limitation tables in KNOWN_ISSUES.md, vera/README.md, the spec
     chapters, SKILL.md and LSP_SERVER.md;
  2. the Issue column of KNOWN_ISSUES.md's ``## Bugs`` table and SKILL.md's
     ``## Known Bugs and Workarounds`` table, which are hand-kept.

With ``--check-states`` the script asks the tracker about each one (``gh
issue view``), and fails on an issue that is closed or whose state cannot
be determined.  Without it, the script reads the sources and reports how
many issues it would ask about, without the network.  A Bugs heading that
is gone, or a data file that cannot be read, is an error in both modes.

``.github/workflows/limitations-sync.yml`` runs it weekly on a bare Python,
so it imports nothing beyond the standard library and ``render_lists.py``,
which reads the data file with the standard library alone.
"""

import argparse
import importlib.util
import re
import subprocess
import sys
from collections.abc import Callable
from pathlib import Path
from types import ModuleType


_ISSUE_LINK_RE = re.compile(r"\[#(\d+)\]\(https://github\.com/[^)]+\)")


def _row_issue_links(line: str, issue_column_only: bool) -> set[int]:
    """Issue links in one Markdown table row.

    ``issue_column_only`` narrows the scan to the row's LAST cell — the
    **Issue** column every limitation and bug table carries.  The two
    widths answer different questions (#1337).

    The WIDE form is every link the row holds.  The ``--check-states``
    scan wants the NARROW form, because a row's prose legitimately cites
    CLOSED issues for context — "the general disease behind [#1315]",
    "fixed in [#1305]" — and reading those as claims that the issue is
    still open failed the nightly on eight such citations while the row's
    own Issue column was correct throughout.
    """
    source = line.strip().strip("|").split("|")[-1] if issue_column_only else line
    return {int(n) for n in _ISSUE_LINK_RE.findall(source)}


_FENCE_RE = re.compile(r"^ {0,3}(?P<delim>`{3,}|~{3,})(?P<info>.*)$")


def _section_body_lines(
    text: str, is_heading: Callable[[str], bool]
) -> list[str] | None:
    """The body lines of the first section whose heading satisfies
    `is_heading`, bounded at the next second-level heading.

    One walk for both extractors below, so the bound is decided in one
    place.  Two things it gets right that a per-extractor scan kept
    getting wrong:

    The bound does not wait for a table.  A section with none — a
    `## Bugs` section driven to zero (#1401), or `spec/11-compilation.md`'s
    `## 11.17 Limitations`, which has never had one — used to run the scan
    on into the NEXT section's table and report it as this section's
    contents (#1405).

    Fenced code is EXCLUDED, from the boundary decision and from the
    body alike.  A `## ` line inside a fence is code, not structure:
    treating one as a boundary ends the section early and the real table
    is never read, and under-collecting a table is the FALSE PASS
    direction, since a closed issue cited there stops being flagged
    (PR #1411 review).  The same is true one line down — an example table
    inside a fence is not inventory, and returning it would have the
    caller either count its rows as claims or, worse, take it for the
    section's table and stop at the closing fence before the real one.
    The fence state is tracked from the top of the file, so a fenced
    heading cannot open a section either, and a block is closed only by
    a run of the SAME character at least as long as the one that opened
    it — a four-backtick block quoting a three-backtick one would
    otherwise toggle closed on its own content and put the rest of the
    example back into the document (PR #1411 review).

    ``None`` when no heading matches, which callers distinguish from an
    empty body.
    """
    body: list[str] = []
    started = False
    fence: tuple[str, int] | None = None
    for line in text.splitlines():
        marker = _FENCE_RE.match(line)
        if marker is not None:
            delim = marker.group("delim")
            if fence is None:
                fence = (delim[0], len(delim))
                continue
            # A closing fence carries no info string, and must be the
            # same character run at least as long as the opener.
            char, length = fence
            if (
                delim[0] == char
                and len(delim) >= length
                and not marker.group("info").strip()
            ):
                fence = None
            continue
        if fence is not None:
            continue
        if not started:
            if is_heading(line):
                started = True
            continue
        if line.startswith("## "):
            break
        body.append(line)
    return body if started else None


def extract_limitation_table_issues(
    text: str, table_header: str, issue_column_only: bool = False
) -> set[int]:
    """Extract issue numbers from a Markdown limitation table.

    Finds the table that follows `table_header` and extracts all issue
    references from it.  Stops at the next heading or blank line after
    the table; the section bound itself is `_section_body_lines`.
    """
    body = _section_body_lines(text, lambda line: table_header in line)
    if body is None:
        return set()

    issues: set[int] = set()
    in_table = False
    for line in body:
        # Skip blank lines between heading and table
        if not in_table and line.strip() == "":
            continue

        # Table rows start with |
        if line.strip().startswith("|"):
            in_table = True
            # Skip separator rows
            if re.match(r"^\|[\s\-|]+\|$", line.strip()):
                continue
            # Extract issue numbers from this row
            issues.update(_row_issue_links(line, issue_column_only))
        elif in_table:
            # Table ended
            break

    return issues


def extract_section_issues(
    text: str, heading: str, issue_column_only: bool = False
) -> set[int] | None:
    """Extract issue links from the table rows of one `## heading` section.

    The scan is bounded at the next `## ` heading (or end of file), and
    only lines that are Markdown table rows contribute — issue links in
    surrounding prose are narrative, not inventory.  Returns ``None``
    when the heading is absent so the caller can treat a renamed or
    deleted section as an error rather than an empty result.
    """
    wanted = f"## {heading}"
    body = _section_body_lines(text, lambda line: line.rstrip() == wanted)
    if body is None:
        return None
    issues: set[int] = set()
    for line in body:
        if not line.strip().startswith("|"):
            continue
        issues.update(_row_issue_links(line, issue_column_only))
    return issues


def check_issue_states(issue_numbers: set[int]) -> dict[int, str]:
    """Check open/closed state of GitHub issues using gh CLI."""
    if not issue_numbers:
        return {}

    states: dict[int, str] = {}
    for num in sorted(issue_numbers):
        try:
            result = subprocess.run(
                [
                    "gh", "issue", "view", str(num),
                    "--json", "state", "-q", ".state",
                ],
                capture_output=True,
                text=True,
                encoding="utf-8",
                timeout=10,
                check=False,
            )
            if result.returncode == 0:
                states[num] = result.stdout.strip()
            else:
                states[num] = "UNKNOWN"
        except (subprocess.TimeoutExpired, FileNotFoundError):
            states[num] = "UNKNOWN"

    return states


def _render_lists() -> ModuleType:
    """scripts/render_lists.py, whose loader is the one definition of the
    data file's format."""
    path = Path(__file__).with_name("render_lists.py")
    spec = importlib.util.spec_from_file_location("render_lists", path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {path}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def _known_issues_bugs(text: str) -> set[int] | None:
    if _section_body_lines(text, lambda line: line.rstrip() == "## Bugs") is None:
        return None
    return extract_limitation_table_issues(text, "## Bugs", issue_column_only=True)


def _skill_bugs(text: str) -> set[int] | None:
    return extract_section_issues(
        text, "Known Bugs and Workarounds", issue_column_only=True
    )


# The hand-kept Bugs tables: their document, heading, reader, and the
# label a report names them by.
BUG_TABLES: tuple[tuple[str, str, Callable[[str], set[int] | None], str], ...] = (
    ("KNOWN_ISSUES.md", "Bugs", _known_issues_bugs, "KNOWN_ISSUES.md (Bugs)"),
    (
        "SKILL.md",
        "Known Bugs and Workarounds",
        _skill_bugs,
        "SKILL.md (Known Bugs and Workarounds)",
    ),
)


def issues_to_check(root: Path) -> tuple[dict[int, list[str]], list[str]]:
    """Every issue the tables cite, with where each is listed, and every
    reason a source cannot be read.

    A limitation's issues are its record's in ``limitations.json``, which
    names them apart from any prose in its cells, listed under each table
    that carries it.  A Bugs table is read from its Issue column alone
    (#1337): a row's prose cites closed issues for context, and those are
    not claims that the issue is open.
    """
    listed: dict[int, list[str]] = {}
    errors: list[str] = []
    data = _render_lists().load_limitations(root)
    if isinstance(data, list):
        errors += data
    else:
        for table in data.tables:
            for rid in table.rows:
                for number in data.records[rid].issues:
                    where = listed.setdefault(number, [])
                    if table.id not in where:
                        where.append(table.id)
    for document, heading, read, label in BUG_TABLES:
        path = root / document
        if not path.is_file():
            errors.append(f"{document}: no such file")
            continue
        found = read(path.read_text(encoding="utf-8"))
        if found is None:
            errors.append(
                f"{document}: there is no `## {heading}` section, whose Issue"
                " column the state check reads"
            )
            continue
        for number in sorted(found):
            listed.setdefault(number, []).append(label)
    return dict(sorted(listed.items())), errors


def main(argv: list[str] | None = None, root: Path | None = None) -> int:
    parser = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    parser.add_argument(
        "--check-states",
        action="store_true",
        help="ask the tracker whether each issue is still open (needs gh)",
    )
    args = parser.parse_args(argv)
    root = root or Path(__file__).resolve().parent.parent
    listed, errors = issues_to_check(root)

    if args.check_states and not errors:
        states = check_issue_states(set(listed))
        for number, where in listed.items():
            state = states.get(number, "UNKNOWN")
            if state == "CLOSED":
                errors.append(
                    f"Issue #{number} is CLOSED but still listed in:"
                    f" {', '.join(where)}"
                )
            elif state != "OPEN":
                # A state that cannot be determined (gh CLI missing, auth
                # failure, rate limit, timeout) must be loud: a silent pass
                # here would leave the scheduled #852 workflow green while
                # checking nothing.
                errors.append(
                    f"Issue #{number} state could not be determined "
                    "(gh CLI missing, auth failure, or timeout); "
                    "--check-states cannot verify the tables"
                )

    if errors:
        print(f"ERROR: {len(errors)} limitation sync issue(s):", file=sys.stderr)
        for err in errors:
            print(f"  {err}", file=sys.stderr)
        return 1

    if args.check_states:
        print(f"Every one of the {len(listed)} issues the tables cite is open.")
    else:
        print(
            f"The tables cite {len(listed)} issues; --check-states asks the"
            " tracker whether each is open."
        )
    return 0


if __name__ == "__main__":
    sys.exit(main())
