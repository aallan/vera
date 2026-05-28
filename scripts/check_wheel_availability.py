#!/usr/bin/env python3
"""Verify all pinned runtime dependencies have wheels for supported platforms.

This is the structural backstop against the macOS 14 install regression
documented in #691: when an upstream dep bumps its platform-tag baseline,
this script fails fast in CI rather than letting users on older systems
discover the regression by hitting a cryptic source-build failure 20
minutes into ``pip install``.

The supported platforms checked by this script are the executable form of
the policy documented in README.md §Supported platforms.  If you want to
add or remove a supported platform, update both the policy text and the
SUPPORTED table below — they must agree.

What this checks:

- For each (platform tag, Python version) tuple in SUPPORTED,
  every runtime dependency declared in ``pyproject.toml`` resolves to a
  prebuilt wheel.  Anything that would fall back to source build (sdist)
  on the target platform is a failure.

What this does NOT check:

- Whether the wheel actually works end-to-end on the target platform.
  That is what running the CI matrix on the platform itself is for; see
  the ``test`` job in ``.github/workflows/ci.yml``.  This script is the
  cheaper proxy for the install step, run before the test matrix.

- The ``[dev]`` extras.  Those are dev tooling (pytest, mypy, ruff, etc.)
  and are typically pure Python; their platform-tag risk is much lower.

- Transitive dependencies.  ``--no-deps`` is used to focus on the deps we
  directly pin; if a transitive of one of our deps loses wheel coverage,
  the surface-level dep would too (because pip would fail to resolve).

Usage::

    python scripts/check_wheel_availability.py

Exit codes::

    0  — every (dep, platform, python_version) combination has a wheel
    1  — at least one combination falls back to sdist or fails to resolve
"""
from __future__ import annotations

import subprocess
import sys
import tempfile
import tomllib
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
PYPROJECT = REPO_ROOT / "pyproject.toml"

# (platform_tag, python_version, human_description).
# Each entry corresponds to a row in README.md §Supported platforms.
# Keep these in sync: if a platform is added here, document it in the
# README; if a platform is documented in the README as supported, it
# belongs here too.
SUPPORTED: list[tuple[str, str, str]] = [
    # macOS arm64
    ("macosx_15_0_arm64", "3.11", "macOS 15+ Apple Silicon (Python 3.11)"),
    ("macosx_15_0_arm64", "3.12", "macOS 15+ Apple Silicon (Python 3.12)"),
    ("macosx_15_0_arm64", "3.13", "macOS 15+ Apple Silicon (Python 3.13)"),
    # Linux x86_64 — manylinux_2_27 picked because that is z3-solver 4.16.0's
    # tag; anything older is documented as the conservative baseline.
    ("manylinux_2_27_x86_64", "3.11", "Linux x86_64 manylinux_2_27+ (Python 3.11)"),
    ("manylinux_2_27_x86_64", "3.12", "Linux x86_64 manylinux_2_27+ (Python 3.12)"),
    ("manylinux_2_27_x86_64", "3.13", "Linux x86_64 manylinux_2_27+ (Python 3.13)"),
    # Windows x86_64
    ("win_amd64", "3.11", "Windows x86_64 (Python 3.11)"),
    ("win_amd64", "3.12", "Windows x86_64 (Python 3.12)"),
    ("win_amd64", "3.13", "Windows x86_64 (Python 3.13)"),
]


def runtime_deps() -> list[str]:
    """Return the runtime dependencies declared in pyproject.toml."""
    with PYPROJECT.open("rb") as f:
        data = tomllib.load(f)
    return data["project"]["dependencies"]


def check_one(dep: str, platform_tag: str, python_version: str) -> tuple[bool, str]:
    """Check that ``dep`` has a wheel for (platform_tag, python_version).

    Returns (ok, message).  When ok is False, ``message`` is the pip stderr
    (truncated) so the caller can attribute the failure.
    """
    with tempfile.TemporaryDirectory(prefix="vera_preflight_") as tmp:
        cmd = [
            sys.executable, "-m", "pip", "download",
            dep,
            "--no-deps",
            "--only-binary", ":all:",
            "--platform", platform_tag,
            "--python-version", python_version,
            "--dest", tmp,
            "--quiet",
        ]
        try:
            # 60s per (dep, platform, python) combination.  Each download
            # is small (--no-deps), so 60s is generous; the timeout exists
            # to prevent indefinite hangs (slow mirror, transient PyPI
            # outage) from blocking CI for hours.
            result = subprocess.run(
                cmd, capture_output=True, text=True, timeout=60,
            )
        except subprocess.TimeoutExpired:
            return False, f"pip download timed out after 60s for {dep}"
    if result.returncode == 0:
        return True, ""
    # Truncate stderr to keep the report readable
    stderr = result.stderr.strip()
    if len(stderr) > 400:
        stderr = stderr[:400] + " […truncated]"
    return False, stderr


def main() -> int:
    deps = runtime_deps()
    print(f"Checking {len(deps)} runtime deps × {len(SUPPORTED)} platforms...")
    print(f"  deps: {', '.join(deps)}")
    print()

    failures: list[tuple[str, str, str, str]] = []
    for platform_tag, python_version, description in SUPPORTED:
        print(f"  {description}")
        all_ok = True
        for dep in deps:
            ok, msg = check_one(dep, platform_tag, python_version)
            status = "✓" if ok else "✗"
            print(f"    {status} {dep}")
            if not ok:
                all_ok = False
                failures.append((platform_tag, python_version, dep, msg))
        if all_ok:
            print(f"    OK — {len(deps)} wheels resolved")
        print()

    if failures:
        print(f"FAILED: {len(failures)} (platform, dep) combinations have no wheel:")
        print()
        for platform_tag, python_version, dep, msg in failures:
            print(f"  {platform_tag} / Python {python_version} / {dep}")
            for line in msg.splitlines():
                print(f"    {line}")
            print()
        print(
            "If this is intentional (you have dropped a platform), update both "
            "the SUPPORTED table in this script and the README §Supported "
            "platforms section so they agree.  If this is a regression, either "
            "pin a dep version that still has wheel coverage, or accept the "
            "platform drop and document it."
        )
        return 1

    print(f"OK — all {len(deps) * len(SUPPORTED)} combinations have wheels.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
