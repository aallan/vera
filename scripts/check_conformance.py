#!/usr/bin/env python
"""Verify all conformance programs pass their declared level.

Each entry in tests/conformance/manifest.json declares the deepest
pipeline stage (parse, check, verify, run) the program must pass.
This script validates every entry through that stage and reports
pass/fail summary.  A run-level entry passes its run stage only when
the run exits with its ``expected_exit`` and prints exactly its
``expected_stdout`` (or carries a ``nondeterministic_stdout`` reason in
place of the output); scripts/conformance_golden.py holds that rule, and
tests/test_conformance.py shares it.
"""

import json
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from conformance_golden import entry_problems, run_mismatch, run_program

CONFORMANCE_DIR = Path(__file__).parent.parent / "tests" / "conformance"
MANIFEST_PATH = CONFORMANCE_DIR / "manifest.json"

_LEVEL_ORDER = {"parse": 0, "check": 1, "verify": 2, "run": 3}


def _vera(*args: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [sys.executable, "-m", "vera.cli", *args],
        capture_output=True,
        text=True,
        encoding="utf-8",
        check=False,
    )


def main() -> int:
    if not MANIFEST_PATH.exists():
        print("Manifest not found:", MANIFEST_PATH, file=sys.stderr)
        return 1

    manifest: list[dict] = json.loads(MANIFEST_PATH.read_text(encoding="utf-8"))
    if not manifest:
        print("Empty manifest.", file=sys.stderr)
        return 1

    failed: list[tuple[str, str, str]] = []

    for entry in manifest:
        entry_id = entry["id"]
        path = str(CONFORMANCE_DIR / entry["file"])
        level = entry["level"]
        level_n = _LEVEL_ORDER.get(level, 0)

        # What a run-level entry declares about its run (expected_stdout and
        # expected_exit, or a nondeterministic_stdout reason), and that no
        # lower-level entry carries any of it.  A malformed entry has no
        # declared run to compare, so it stops here.
        problems = entry_problems(entry)
        if problems:
            failed.append((entry_id, "manifest", "\n".join(problems)))
            continue

        # Negative test: the program must FAIL with a specific error code
        # (e.g. ch08_circular_import → E011).  `expected_error_stage` names
        # the pipeline stage the diagnostic fires at — "check" (the default)
        # or "compile".  A COMPILE-stage negative additionally asserts that
        # `check` is clean, which is the whole point of the class it exists
        # to pin: a program the checker accepts and codegen must refuse
        # (#1277's E621).  Either way the positive pipeline is skipped.
        expected_error = entry.get("expected_error")
        if expected_error is not None:
            stage = entry.get("expected_error_stage", "check")
            # A negative's positive obligation stops at check, so it is
            # declared at level "check" whichever stage it fails at.  Fail
            # fast on a mislabelled entry so a verify/run negative can't
            # silently skip its declared stage.
            if level != "check":
                failed.append((
                    entry_id, "manifest",
                    f"expected_error is only valid at level 'check'; "
                    f"got level={level!r}",
                ))
                continue
            if stage not in ("check", "compile"):
                failed.append((
                    entry_id, "manifest",
                    f"expected_error_stage must be 'check' or 'compile'; "
                    f"got {stage!r}",
                ))
                continue
            if stage == "compile":
                pre = _vera("check", path)
                if "OK:" not in pre.stdout:
                    failed.append((
                        entry_id, "check (compile-stage negative)",
                        "a compile-stage negative must type-check cleanly:\n"
                        + pre.stdout + pre.stderr,
                    ))
                    continue
            result = _vera(stage, "--json", path)
            try:
                payload = json.loads(result.stdout)
            except json.JSONDecodeError:
                failed.append((
                    entry_id, f"{stage} (negative)",
                    "expected JSON diagnostics, got:\n"
                    + result.stdout + result.stderr,
                ))
                continue
            codes = [d.get("error_code") for d in payload.get("diagnostics", [])]
            if payload.get("ok") is not False or expected_error not in codes:
                failed.append((
                    entry_id, f"{stage} (negative)",
                    f"expected failure with {expected_error}; "
                    f"got ok={payload.get('ok')} codes={codes}",
                ))
            continue

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

        # Run: the exit status and the exact stdout the entry declares
        if level_n >= _LEVEL_ORDER["run"]:
            mismatch = run_mismatch(entry, run_program(CONFORMANCE_DIR / entry["file"]))
            if mismatch is not None:
                failed.append((entry_id, "run", mismatch))
                continue

    if failed:
        for entry_id, stage, output in failed:
            print(f"FAIL ({stage}): {entry_id}", file=sys.stderr)
            # A run mismatch or a manifest problem is shown whole: it is the
            # expected and the actual output, or the keys at fault.  Any
            # other stage's output is diagnostics, and its first 3 lines
            # give the context.
            lines = output.strip().splitlines()
            for line in lines if stage in ("run", "manifest") else lines[:3]:
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
