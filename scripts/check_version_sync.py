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
    # Both must be checked separately.  Pre-fix this script only
    # extracted from the URL via ``releases/tag/v([^"]+)`` — a naive
    # ``sed 's/v{old}/v{new}/g'`` during version bumps matched the
    # URL (where ``v`` is part of the path) but skipped the visible
    # text (no ``v`` prefix), and the visible text silently lagged
    # for two releases (v0.0.133 and v0.0.134) before being caught
    # by the user.  Now extract both and report each as a distinct
    # source so the all-match check catches any divergence.
    index_html = root / "docs" / "index.html"
    if index_html.is_file():
        html_text = index_html.read_text()
        url_match = re.search(r"releases/tag/v([0-9]+\.[0-9]+\.[0-9]+)", html_text)
        if url_match:
            versions["docs/index.html (URL)"] = url_match.group(1)
        else:
            print(
                "WARNING: Could not find release URL version "
                "in docs/index.html",
                file=sys.stderr,
            )
        # Visible link-text version: ``...">X.Y.Z</a>`` immediately
        # after the URL.  Pin to the same line as the release URL
        # by anchoring on the closing-quote-then-angle-bracket of
        # the href.
        text_match = re.search(
            r'releases/tag/v[0-9]+\.[0-9]+\.[0-9]+">([0-9]+\.[0-9]+\.[0-9]+)</a>',
            html_text,
        )
        if text_match:
            versions["docs/index.html (link text)"] = text_match.group(1)
        else:
            print(
                "WARNING: Could not find link-text version "
                "in docs/index.html",
                file=sys.stderr,
            )

    # README.md — "active development at vX.Y.Z"
    readme = root / "README.md"
    match = re.search(r"at v([0-9]+\.[0-9]+\.[0-9]+)", readme.read_text())
    if match:
        versions["README.md"] = match.group(1)
    else:
        print("ERROR: Could not find version string in README.md", file=sys.stderr)
        return 1

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
