#!/usr/bin/env python
"""Verify all .vera examples type-check cleanly."""

import glob
import subprocess
import sys


def main() -> int:
    files = sorted(glob.glob("examples/*.vera"))
    if not files:
        print("No .vera examples found.", file=sys.stderr)
        return 1

    failed = []
    for f in files:
        result = subprocess.run(
            [sys.executable, "-m", "vera.cli", "check", f],
            capture_output=True,
            text=True,
        )
        if "OK:" not in result.stdout:
            failed.append(f)
            print(f"FAIL: {f}", file=sys.stderr)
            if result.stderr:
                print(result.stderr, file=sys.stderr)

    if failed:
        print(f"{len(failed)}/{len(files)} examples failed.", file=sys.stderr)
        return 1

    print(f"All {len(files)} examples pass.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
