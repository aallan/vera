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
