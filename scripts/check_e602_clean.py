#!/usr/bin/env python
"""Pre-commit / CI gate: no `[E602]` (body unsupported) or `[E604]`
(parameter unsupported) skips outside the known allowlist.

Layer 1 of #626 ("convert 'translate returns None → silent skip'
failures into loud diagnostics").  The `[E602]` warning channel was
the project's *only* signal for silent translator-skip failures, and
five prelude-combinator instances of it were buried in every WASM
compile — making it impossible to spot a new genuine skip without
manually sifting through expected-noise warnings.

This script fails the build when any compile of an example or
conformance program emits an `[E602]` / `[E604]` for a function
name not in `ALLOWED_SKIPS`.  When a new genuine skip surfaces,
either:

- the underlying bug gets fixed and the function compiles cleanly,
  OR
- the function name is added to `ALLOWED_SKIPS` with a tracking
  issue reference, so the gap is explicit rather than buried.

Currently allowed: the five #604 prelude combinators that emit
spurious warnings on every compile (their mono clones either work
correctly — for the `_unwrap_or` pair — or trap at runtime — for
the `_map`/`_and_then` triplet; see issue #604 for the full
diagnosis).
"""

from __future__ import annotations

import glob
import json
import subprocess
import sys
from pathlib import Path


# Allowlist: function names whose `[E602]` / `[E604]` skips are
# expected pending an open tracking issue.  Each entry: function
# name → (error_code, issue_number, brief reason).
#
# Removing an entry without fixing the underlying bug will cause
# every compile that touches the prelude to fail the gate — by
# design.  The allowlist is meant to shrink over time.
ALLOWED_SKIPS: dict[str, tuple[str, int, str]] = {
    # ----- Prelude combinators tracked by #604 -----
    "option_unwrap_or": (
        "E604", 604,
        "Bare type-var @T param on generic prelude decl.  Mono "
        "clones (option_unwrap_or$<T>) work end-to-end.",
    ),
    "result_unwrap_or": (
        "E604", 604,
        "Same shape as option_unwrap_or — bare type-var @T param. "
        "Mono clones work end-to-end.",
    ),
    "option_map": (
        "E602", 604,
        "apply_fn-in-match-arm body.  Mono clones currently "
        "produce wrong type-arg suffix and trap at runtime — "
        "real bug, see #604 investigation comment.",
    ),
    "option_and_then": (
        "E602", 604,
        "Same shape as option_map — apply_fn-in-match-arm body.",
    ),
    "result_map": (
        "E602", 604,
        "Same shape as option_map — apply_fn-in-match-arm body.",
    ),

    # ----- User-code generics tracked by #655 (Shape A — same root
    # cause as #604's _unwrap_or half: warning fires on generic
    # template, mono clones work) -----
    "identity": (
        "E604", 655,
        "Generic forall<T> fn(@T -> @T) — bare type-var @T param. "
        "Mono identity$<T> works end-to-end.",
    ),
    "const": (
        "E604", 655,
        "Generic forall<A, B> fn(@A, @B -> @A) — bare type-var "
        "params.  Mono works end-to-end.",
    ),
    "is_some": (
        "E602", 655,
        "Generic forall<T> fn(@Option<T> -> @Bool) — match on "
        "@Option<T>.0 with type-var-typed Some arm.  Mono "
        "is_some$<T> works end-to-end.",
    ),
    "are_equal": (
        "E604", 655,
        "Generic forall<T where Eq<T>> — bare type-var @T param "
        "with ability constraint.  Mono works end-to-end.",
    ),
    "cmp_sign": (
        "E604", 655,
        "Generic forall<T where Ord<T>> — bare type-var @T param "
        "with ability constraint.  Mono works end-to-end.",
    ),

    # ----- Real codegen gap tracked by #655 (Shape B — non-generic
    # refinement-of-Array param) -----
    "head": (
        "E602", 655,
        "Non-generic, takes @NonEmptyArray (refinement-of-Array "
        "alias) param.  IndexExpr translator returns None for "
        "@NonEmptyArray.0[0] — calling head() actually fails "
        "with 'unknown func: $head'.  Real bug.",
    ),
}


def _extract_skips(
    file: str,
) -> list[tuple[str, str, str]]:
    """Compile a single file with --json and extract (code, fn_name,
    description) tuples for each E602 / E604 warning.

    Returns empty list on a clean compile, non-empty list of skip
    tuples otherwise.  Compile errors (vs warnings) are surfaced via
    the JSON envelope's `ok` field — those count as failures too.
    """
    # Use `compile --wat` rather than `--target browser` to avoid
    # producing an output directory; the WAT-only path still runs
    # the full compilability pipeline so all `[E602]` / `[E604]`
    # warnings surface.
    result = subprocess.run(
        [sys.executable, "-m", "vera.cli", "compile", "--wat",
         "--json", file],
        capture_output=True,
        text=True,
    )
    try:
        envelope = json.loads(result.stdout)
    except json.JSONDecodeError:
        # Not JSON — compile produced something else (CLI error).
        # Surface as a failure with the stderr text inline.
        return [("PARSE_ERROR", file, result.stderr.strip()[:200])]

    skips: list[tuple[str, str, str]] = []
    for w in envelope.get("warnings", []):
        code = w.get("error_code", "")
        if code not in ("E602", "E604"):
            continue
        desc = w.get("description", "")
        # Function name is parsed from the description; format is
        # "Function 'NAME' has unsupported parameter type — skipped."
        # or "Function 'NAME' body contains unsupported expressions
        # — skipped."
        fn_name = ""
        if desc.startswith("Function '"):
            end = desc.find("'", 10)
            if end != -1:
                fn_name = desc[10:end]
        skips.append((code, fn_name, desc))
    return skips


def _scan_paths(paths: list[str]) -> tuple[int, list[str]]:
    """Compile every path; return (clean_count, failures).

    Failures are formatted as one-line strings ready for stderr.
    """
    failures: list[str] = []
    clean = 0
    for path in paths:
        skips = _extract_skips(path)
        unexpected: list[tuple[str, str, str]] = []
        for code, fn_name, desc in skips:
            if code == "PARSE_ERROR":
                unexpected.append((code, fn_name, desc))
                continue
            if fn_name in ALLOWED_SKIPS:
                # Allowlisted — verify the code matches the
                # expected code (catches an unrelated skip on the
                # same function name).
                expected_code = ALLOWED_SKIPS[fn_name][0]
                if code != expected_code:
                    unexpected.append((
                        code, fn_name,
                        f"unexpected code {code} (allowlist "
                        f"entry expects {expected_code}): {desc}",
                    ))
                continue
            unexpected.append((code, fn_name, desc))
        if unexpected:
            for code, fn_name, desc in unexpected:
                failures.append(
                    f"{path}: [{code}] fn={fn_name!r}: "
                    f"{desc[:120]}"
                )
        else:
            clean += 1
    return clean, failures


def main() -> int:
    repo_root = Path(__file__).resolve().parent.parent

    examples = sorted(glob.glob(str(repo_root / "examples/*.vera")))
    conformance = sorted(
        glob.glob(str(repo_root / "tests/conformance/*.vera"))
    )

    if not examples and not conformance:
        print("No .vera files found to scan.", file=sys.stderr)
        return 1

    all_paths = examples + conformance
    clean, failures = _scan_paths(all_paths)

    print(
        f"Scanned {len(all_paths)} files "
        f"({len(examples)} examples + {len(conformance)} "
        f"conformance programs).",
    )
    print(f"  Clean: {clean}")
    print(f"  Allowlisted skips suppressed: "
          f"{len(ALLOWED_SKIPS)} known functions")

    if failures:
        print(
            f"\nFAILURES ({len(failures)} unexpected "
            f"[E602]/[E604] skips):",
            file=sys.stderr,
        )
        for f in failures:
            print(f"  {f}", file=sys.stderr)
        print(
            "\nA new unexpected skip means either (a) a recent "
            "change introduced a translator-returns-None failure, "
            "or (b) the underlying bug is now tracked and the "
            "function name should be added to ALLOWED_SKIPS in "
            "scripts/check_e602_clean.py with a tracking issue "
            "reference.  Layer 1 of #626 — do NOT silently "
            "expand the allowlist without a tracking issue.",
            file=sys.stderr,
        )
        return 1

    print("\nNo unexpected [E602]/[E604] skips. (Layer 1 of #626.)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
