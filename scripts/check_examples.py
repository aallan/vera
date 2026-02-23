#!/usr/bin/env python
"""Verify all .vera examples type-check and verify cleanly."""

import glob
import subprocess
import sys


def main() -> int:
    files = sorted(glob.glob("examples/*.vera"))
    if not files:
        print("No .vera examples found.", file=sys.stderr)
        return 1

    failed = []

    # Phase 1: type-check all examples
    for f in files:
        result = subprocess.run(
            [sys.executable, "-m", "vera.cli", "check", f],
            capture_output=True,
            text=True,
        )
        if "OK:" not in result.stdout:
            failed.append(("check", f))
            print(f"FAIL (check): {f}", file=sys.stderr)
            if result.stderr:
                print(result.stderr, file=sys.stderr)

    # Phase 2: verify contracts on all examples
    for f in files:
        result = subprocess.run(
            [sys.executable, "-m", "vera.cli", "verify", f],
            capture_output=True,
            text=True,
        )
        if "OK:" not in result.stdout:
            failed.append(("verify", f))
            print(f"FAIL (verify): {f}", file=sys.stderr)
            if result.stderr:
                print(result.stderr, file=sys.stderr)

    if failed:
        print(f"{len(failed)} failures across {len(files)} examples.",
              file=sys.stderr)
        return 1

    print(f"All {len(files)} examples pass (check + verify).")
    return 0


if __name__ == "__main__":
    sys.exit(main())
