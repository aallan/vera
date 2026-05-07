#!/usr/bin/env python
"""Verify version numbers are consistent across the project."""

import re
import sys
from pathlib import Path


def main() -> int:
    root = Path(__file__).resolve().parent.parent
    versions: dict[str, str] = {}

    # pyproject.toml
    pyproject = root / "pyproject.toml"
    match = re.search(r'^version\s*=\s*"([^"]+)"', pyproject.read_text(), re.MULTILINE)
    if match:
        versions["pyproject.toml"] = match.group(1)
    else:
        print("ERROR: Could not find version in pyproject.toml", file=sys.stderr)
        return 1

    # vera/__init__.py
    init = root / "vera" / "__init__.py"
    match = re.search(r'^__version__\s*=\s*"([^"]+)"', init.read_text(), re.MULTILINE)
    if match:
        versions["vera/__init__.py"] = match.group(1)
    else:
        print("ERROR: Could not find __version__ in vera/__init__.py", file=sys.stderr)
        return 1

    # docs/index.html — version badge has the version twice on one
    # line: in the release-tag URL and in the visible link text:
    #
    #   <span>v<a href=".../releases/tag/v0.0.134">0.0.134</a></span>
    #
    # Both must be checked.  Pre-fix this script only extracted
    # from the URL via ``releases/tag/v([^"]+)`` — a naive
    # ``sed 's/v{old}/v{new}/g'`` during version bumps matched
    # the URL (where ``v`` is part of the path) but skipped the
    # visible text (no ``v`` prefix), and the visible text
    # silently lagged for two releases (v0.0.133 and v0.0.134)
    # before being caught by the user.
    #
    # The two halves are extracted via a single combined regex
    # anchored on the badge's full shape ``releases/tag/vX.Y.Z">
    # X.Y.Z</a>`` rather than two independent ``re.search`` calls
    # against the whole document.  This guarantees both groups
    # come from the *same badge instance*, so the all-match
    # check at the end can't pass vacuously by reading the URL
    # from one badge and the link text from another (the doc
    # also contains body-text release links to v0.0.4, v0.0.7,
    # v0.0.108 in the VeraBench results section).
    index_html = root / "docs" / "index.html"
    if not index_html.is_file():
        # Fail-fast like the other version-source readers.  A
        # missing docs/index.html means a non-standard checkout
        # (the file is committed and required for the site
        # build); silently skipping would let the all-match
        # check pass vacuously on the remaining files.
        print(
            "ERROR: docs/index.html not found",
            file=sys.stderr,
        )
        return 1
    html_text = index_html.read_text()
    badge_match = re.search(
        r'releases/tag/v([0-9]+\.[0-9]+\.[0-9]+)">([0-9]+\.[0-9]+\.[0-9]+)</a>',
        html_text,
    )
    if not badge_match:
        print(
            "ERROR: Could not find version badge in docs/index.html "
            "(expected `releases/tag/vX.Y.Z\">X.Y.Z</a>` shape)",
            file=sys.stderr,
        )
        return 1
    versions["docs/index.html (URL)"] = badge_match.group(1)
    versions["docs/index.html (link text)"] = badge_match.group(2)

    # README.md — "active development at vX.Y.Z"
    readme = root / "README.md"
    match = re.search(r"at v([0-9]+\.[0-9]+\.[0-9]+)", readme.read_text())
    if match:
        versions["README.md"] = match.group(1)
    else:
        print("ERROR: Could not find version string in README.md", file=sys.stderr)
        return 1

    # uv.lock — the editable ``[[package]] name = "vera"`` entry holds
    # the same version as ``pyproject.toml``.  CI runs ``uv lock --check``
    # in the lint job (`.github/workflows/ci.yml`); a stale lockfile
    # fails CI with a generic "lockfile needs to be updated" message
    # and forces a round-trip.  Catching it here keeps the version-bump
    # checklist self-contained: bump pyproject + __init__ + run
    # ``uv lock`` (or ``uv sync``), and this script catches drift on
    # any of the three.
    lock = root / "uv.lock"
    if not lock.is_file():
        print("ERROR: uv.lock not found", file=sys.stderr)
        return 1
    # Match ``name = "vera"`` followed by ``version = "X.Y.Z"`` on the
    # next non-blank line.  Anchored on the package boundary
    # (``[[package]]``) so we don't accidentally pick up a transitive
    # dependency that happens to be named ``vera`` in some far-future
    # ecosystem expansion — the project's own entry is the only one
    # with ``source = { editable = "." }``.
    lock_match = re.search(
        r'\[\[package\]\]\s*\n'
        r'name\s*=\s*"vera"\s*\n'
        r'version\s*=\s*"([0-9]+\.[0-9]+\.[0-9]+)"',
        lock.read_text(),
    )
    if not lock_match:
        print(
            'ERROR: Could not find ``[[package]] name = "vera"`` block '
            "with a version field in uv.lock — has the lockfile shape "
            "changed?",
            file=sys.stderr,
        )
        return 1
    versions["uv.lock"] = lock_match.group(1)

    # Check they all match
    unique = set(versions.values())
    if len(unique) == 1:
        version = unique.pop()
        print(f"Version {version} is consistent across {len(versions)} files.")
        return 0

    print("ERROR: Version mismatch detected!", file=sys.stderr)
    for path, version in versions.items():
        print(f"  {path}: {version}", file=sys.stderr)
    return 1


if __name__ == "__main__":
    sys.exit(main())
