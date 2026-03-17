#!/usr/bin/env python
"""Verify all installed packages have MIT-compatible licenses.

Vera is MIT-licensed.  This script ensures no dependency (direct or
transitive) introduces a license that is incompatible with MIT
redistribution.  It uses ``pip-licenses`` to enumerate packages and
checks each license string against a set of known-compatible patterns.

Runs in under 1 second — fast enough for a pre-commit hook.
"""

import json
import subprocess
import sys

# ---------------------------------------------------------------------------
# Compatible license patterns (case-insensitive substring match)
# ---------------------------------------------------------------------------
# All of these are permissive licenses compatible with MIT redistribution.
# MPL-2.0 is included because it allows larger works under any license —
# only the MPL-covered source files themselves must remain under MPL.

_COMPATIBLE_PATTERNS: list[str] = [
    "mit",
    "bsd",
    "apache",
    "psf",
    "python software foundation",
    "isc",
    "mpl",
    "unlicense",
    "cc0",
    "public domain",
    "0bsd",
]

# Packages to exclude from checking (this project itself).
_SELF_PACKAGES: set[str] = {"vera"}


def _is_compatible(license_str: str) -> bool:
    """Return True if *license_str* matches a known-compatible pattern."""
    normalised = license_str.strip().lower()
    return any(pattern in normalised for pattern in _COMPATIBLE_PATTERNS)


def main() -> int:
    # Run pip-licenses as a subprocess (module name is ``piplicenses``).
    try:
        result = subprocess.run(
            [sys.executable, "-m", "piplicenses", "--format=json"],
            capture_output=True,
            text=True,
            timeout=30,
        )
    except FileNotFoundError:
        print(
            "ERROR: pip-licenses is not installed."
            "  Run: pip install -e '.[dev]'",
            file=sys.stderr,
        )
        return 1

    if result.returncode != 0:
        print(
            f"ERROR: pip-licenses failed:\n{result.stderr}",
            file=sys.stderr,
        )
        return 1

    packages: list[dict[str, str]] = json.loads(result.stdout)

    violations: list[tuple[str, str, str]] = []
    checked = 0

    for pkg in packages:
        name = pkg["Name"]
        if name.lower() in _SELF_PACKAGES:
            continue

        license_str = pkg.get("License", "UNKNOWN")
        checked += 1

        if license_str in ("UNKNOWN", "") or not _is_compatible(license_str):
            violations.append((name, pkg.get("Version", "?"), license_str))

    if violations:
        print(
            f"ERROR: {len(violations)} package(s) with incompatible or"
            " unknown licenses:",
            file=sys.stderr,
        )
        for name, version, lic in violations:
            print(f"  {name} {version}: {lic!r}", file=sys.stderr)
        return 1

    print(f"All {checked} packages have compatible licenses.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
