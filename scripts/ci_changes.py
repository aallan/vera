#!/usr/bin/env python
"""Whether a pull request changes only files no filtered CI job reads.

    python scripts/ci_changes.py BASE HEAD

ci.yml's plan job runs this on a pull request, with the pull request's base
and head commits, and appends what it prints, ``inert=true`` or
``inert=false``, to ``$GITHUB_OUTPUT``.  On ``inert=true`` the jobs that read
none of those files stand down: the suite's shards, typecheck, eager-gc,
browser-parity, wheel-preflight, dependency-audit, package-distribution and
sbom.  Plan, lint, security and matrix-gate run on every pull request.

A path is inert when it is one of the VS Code extension's own files, which
vscode-extension.yml builds and tests: a file under ``editors/vscode/`` of a
kind ``INERT_SUFFIXES`` or ``INERT_NAMES`` names, in no ``syntax`` or
``syntaxes`` directory, and not a grammar by its name.  The two gates that
read files there are why: ``scripts/render_lists.py`` renders the effect
list into the extension's grammar and discovers any other grammar under
``editors/`` (``GRAMMAR_DIRS``, ``GRAMMAR_SUFFIXES``), and
``scripts/check_doc_examples.py`` holds every tracked document to its
registry, so no inert kind is a document's, and the extension's README and
CHANGELOG are not inert either.  The grammar tables are copies, since this
runs before anything is installed; ``tests/test_ci_changes.py`` holds them
to ``scripts/render_lists.py``'s, and the inert kinds apart from
``scripts/check_doc_examples.py``'s document suffixes.

Every path the diff from the merge base lists counts, a rename's old name as
well as its new one (``--no-renames``), and a diff that lists none is not
inert.  A git failure exits non-zero and prints nothing, which fails the
plan job and, with it, matrix-gate.
"""

from __future__ import annotations

import os
import subprocess
import sys
from collections.abc import Iterable, Sequence
from pathlib import PurePosixPath

#: The VS Code extension's directory.
EXTENSION = "editors/vscode/"

#: The kinds of file the extension holds that nothing outside
#: vscode-extension.yml reads: its code, its manifests and lockfile, its icon.
INERT_SUFFIXES: tuple[str, ...] = (".js", ".json", ".png")

#: The extension's files of no suffix the table above names.
INERT_NAMES: tuple[str, ...] = (".gitignore", ".vscodeignore", "LICENSE")

#: scripts/render_lists.py's `_GRAMMAR_DIRS` and `_GRAMMAR_SUFFIXES`.
GRAMMAR_DIRS = frozenset({"syntax", "syntaxes"})
GRAMMAR_SUFFIXES: tuple[str, ...] = (
    ".tmlanguage", ".tmlanguage.json", ".sublime-syntax", ".el", ".scm")

#: The variables that name a repository for git, which a hook exports and
#: which would otherwise decide which repository answers.
GIT_SELECTORS = (
    "GIT_DIR", "GIT_WORK_TREE", "GIT_INDEX_FILE", "GIT_COMMON_DIR",
    "GIT_OBJECT_DIRECTORY", "GIT_ALTERNATE_OBJECT_DIRECTORIES",
)


def is_inert(path: str) -> bool:
    """Whether *path*, repo-relative and POSIX, is one of the VS Code
    extension's own files that no filtered job reads."""
    if not path.startswith(EXTENSION):
        return False
    parts = PurePosixPath(path).parts
    name = parts[-1]
    if any(part.lower() in GRAMMAR_DIRS for part in parts[:-1]):
        return False
    lowered = name.lower()
    if lowered.endswith(GRAMMAR_SUFFIXES):
        return False
    return lowered.endswith(INERT_SUFFIXES) or name in INERT_NAMES


def inert(paths: Iterable[str]) -> bool:
    """Whether every one of *paths* is inert, and there is at least one."""
    listed = list(paths)
    return bool(listed) and all(is_inert(path) for path in listed)


def changed_paths(base: str, head: str) -> list[str]:
    """Every path the diff from the merge base of *base* and *head* to
    *head* lists, a rename as its two names."""
    env = {k: v for k, v in os.environ.items() if k not in GIT_SELECTORS}
    listing = subprocess.run(
        ["git", "-c", "core.quotePath=false", "diff", "--name-only", "--no-renames",
         "-z", f"{base}...{head}"],
        capture_output=True, check=True, env=env)
    return [path for path in listing.stdout.decode("utf-8").split("\0") if path]


def main(argv: Sequence[str] | None = None) -> int:
    args = list(sys.argv[1:] if argv is None else argv)
    if len(args) != 2:
        print("usage: ci_changes.py BASE HEAD", file=sys.stderr)
        return 2
    try:
        paths = changed_paths(args[0], args[1])
    except subprocess.CalledProcessError as exc:
        print(f"ci_changes: git diff failed: {exc.stderr.decode('utf-8', 'replace').strip()}",
              file=sys.stderr)
        return 1
    print(f"inert={'true' if inert(paths) else 'false'}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
