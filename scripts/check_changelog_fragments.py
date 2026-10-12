#!/usr/bin/env python
"""Verify that every CHANGELOG fragment under ``changelog.d/`` is well formed.

A fragment is one pull request's CHANGELOG entry, in a file of its own
(#1529), so no two pull requests edit the same line of ``CHANGELOG.md``.
This module is the one definition of a fragment: ``scripts/release.py``
assembles fragments with it and ``scripts/check_changelog_updated.py``
recognises one by its name.  ``changelog.d/README.md`` states the convention
and is not a fragment, and neither is a dotfile such as Finder's
``.DS_Store``: every tool ignores both.

Name: ``<issue>.<section>.md`` for a pull request that closes an issue, or
``+<slug>.<section>.md``, the slug being the last path component of the
branch name.  The section is one of ``SECTIONS``, the Keep a Changelog
sections in their order.

Content: the bullets exactly as ``CHANGELOG.md`` will carry them.  The first
line is a bullet (``- `` and its text); every later line is a bullet or a
continuation indented by spaces, which is how the CHANGELOG writes a
sub-bullet or a wrapped line.  No blank line, and the file ends with exactly
one newline.

Exit codes: ``0`` when every fragment is well formed, ``1`` otherwise, with
one line per malformed file on stderr.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from pathlib import Path
import re
import sys

DIRECTORY = Path(__file__).resolve().parent.parent / "changelog.d"
README = "README.md"
SECTIONS = ("added", "changed", "deprecated", "removed", "fixed", "security")
FRAGMENT_NAME = re.compile(
    r"(?:(?P<issue>[1-9][0-9]*)|\+(?P<slug>[A-Za-z0-9][A-Za-z0-9._-]*))"
    rf"\.(?P<section>{'|'.join(SECTIONS)})\.md"
)
# Any `<stem>.<section>.md`, to name an unknown section as such.
_SECTIONED_NAME = re.compile(r".+\.(?P<section>[^.]+)\.md")
_BULLET = re.compile(r"- \S")
_CONTINUATION = re.compile(r" +\S")


@dataclass(frozen=True)
class Fragment:
    """One fragment: where it is, what its name says, and its bullets."""

    path: Path
    section: str
    issue: int | None
    slug: str | None
    text: str

    @property
    def order(self) -> tuple[int, int, str]:
        """Issue fragments by number, then slug fragments by slug."""
        if self.issue is not None:
            return (0, self.issue, "")
        return (1, 0, self.slug or "")


def _name_problem(name: str) -> str:
    sectioned = _SECTIONED_NAME.fullmatch(name)
    if sectioned is not None and sectioned.group("section") not in SECTIONS:
        return (
            f"section {sectioned.group('section')!r} is not one of "
            f"{', '.join(SECTIONS)}"
        )
    return "not a fragment name: <issue>.<section>.md or +<slug>.<section>.md"


def _content_problem(text: str) -> str | None:
    if not text:
        return "is empty"
    if not text.endswith("\n") or text.endswith("\n\n"):
        return "must end with exactly one newline"
    for number, line in enumerate(text[:-1].split("\n"), start=1):
        if not line.strip():
            return f"line {number} is blank"
        if _BULLET.match(line) or (number > 1 and _CONTINUATION.match(line)):
            continue
        wanted = "a bullet" if number == 1 else "a bullet or a space-indented continuation"
        return f"line {number} is not {wanted}: {line!r}"
    return None


def read_fragments(directory: Path = DIRECTORY) -> tuple[list[Fragment], list[str]]:
    """Every fragment in ``directory``, and one problem per malformed entry.

    The README and dotfiles are skipped.  Each problem names its file as
    ``changelog.d/<name>``.  A directory that does not exist holds no
    fragments.
    """
    found: list[Fragment] = []
    problems: list[str] = []
    if not directory.is_dir():
        return found, problems
    for path in sorted(directory.iterdir()):
        if path.name == README or path.name.startswith("."):
            continue
        shown = f"{directory.name}/{path.name}"
        match = FRAGMENT_NAME.fullmatch(path.name)
        if match is None:
            problems.append(f"{shown}: {_name_problem(path.name)}")
            continue
        if not path.is_file():
            problems.append(f"{shown}: not a file")
            continue
        try:
            text = path.read_text(encoding="utf-8")
        except UnicodeDecodeError:
            problems.append(f"{shown}: not UTF-8")
            continue
        problem = _content_problem(text)
        if problem is not None:
            problems.append(f"{shown}: {problem}")
            continue
        issue = match.group("issue")
        found.append(
            Fragment(
                path=path,
                section=match.group("section"),
                issue=int(issue) if issue is not None else None,
                slug=match.group("slug"),
                text=text,
            )
        )
    return found, problems


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--directory", type=Path, default=DIRECTORY)
    args = parser.parse_args(argv)
    _found, problems = read_fragments(args.directory)
    for problem in problems:
        print(f"ERROR: {problem}", file=sys.stderr)
    return 1 if problems else 0


if __name__ == "__main__":
    sys.exit(main())
