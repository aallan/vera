#!/usr/bin/env python
"""Verify all conformance programs pass their declared level.

Each entry in tests/conformance/manifest.json declares the deepest
pipeline stage (parse, check, verify, run) the program must pass.
This script validates every entry through that stage and reports
pass/fail summary.
"""

import json
import subprocess
import sys
from pathlib import Path

CONFORMANCE_DIR = Path(__file__).parent.parent / "tests" / "conformance"
MANIFEST_PATH = CONFORMANCE_DIR / "manifest.json"

_LEVEL_ORDER = {"parse": 0, "check": 1, "verify": 2, "run": 3}


def _vera(*args: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [sys.executable, "-m", "vera.cli", *args],
        capture_output=True,
        text=True,
    )


def main() -> int:
    if not MANIFEST_PATH.exists():
        print("Manifest not found:", MANIFEST_PATH, file=sys.stderr)
        return 1

    manifest: list[dict] = json.loads(MANIFEST_PATH.read_text())
    if not manifest:
        print("Empty manifest.", file=sys.stderr)
        return 1

    failed: list[tuple[str, str, str]] = []

    for entry in manifest:
        entry_id = entry["id"]
        path = str(CONFORMANCE_DIR / entry["file"])
        level = entry["level"]
        level_n = _LEVEL_ORDER.get(level, 0)

        # Parse
        result = _vera("check", path)  # check implies parse
        if level_n >= _LEVEL_ORDER["check"]:
            if "OK:" not in result.stdout:
                failed.append((entry_id, "check", result.stdout + result.stderr))
                continue

        # Verify
        if level_n >= _LEVEL_ORDER["verify"]:
            result = _vera("verify", path)
            if "OK:" not in result.stdout:
                failed.append((entry_id, "verify", result.stdout + result.stderr))
                continue

        # Run
        if level_n >= _LEVEL_ORDER["run"]:
            result = _vera("run", path)
            if result.returncode != 0:
                failed.append((entry_id, "run", result.stdout + result.stderr))
                continue

    if failed:
        for entry_id, stage, output in failed:
            print(f"FAIL ({stage}): {entry_id}", file=sys.stderr)
            # Print first 3 lines of output for context
            for line in output.strip().splitlines()[:3]:
                print(f"  {line}", file=sys.stderr)
        print(
            f"\n{len(failed)} failures across {len(manifest)} conformance programs.",
            file=sys.stderr,
        )
        return 1

    print(f"All {len(manifest)} conformance programs pass.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
