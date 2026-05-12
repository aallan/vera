#!/usr/bin/env python
"""Pre-commit / CI gate: no `[E602]` (body unsupported) or `[E604]`
(parameter unsupported) skips outside the known allowlist.

Layer 1 of #626 ("convert 'translate returns None → silent skip'
failures into loud diagnostics").  The `[E602]` warning channel was
the project's *only* signal for silent translator-skip failures, and
several long-standing instances of it were buried in every WASM
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

Current allowlist groups (each entry tagged with its tracking issue):

- **5 prelude combinators tracked by #604**: `option_unwrap_or`,
  `result_unwrap_or` (mono clones work; warning is spurious),
  plus `option_map`, `option_and_then`, `result_map` (mono clones
  produce wrong type-arg suffix and trap at runtime — real bug
  in monomorphizer's apply_fn-in-match-arm type inference).

- **6 cases tracked by #655** (surfaced by this gate's first
  run across `examples/*.vera` + `tests/conformance/*.vera`):
  5 user-code generics with spurious warnings (`identity`,
  `const`, `is_some`, `are_equal`, `cmp_sign` — mono clones
  work), plus 1 real codegen gap (`head` over a refinement-
  alias-of-Array param — calling `head([1,2,3])` actually
  fails with `unknown func: $head`).

See `ALLOWED_SKIPS` below for the full table with per-entry
diagnoses and #604 / #655 for the underlying bug tracking.
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

    # NOTE: 5 user-code generic entries from #655 Shape A (identity,
    # const, is_some, are_equal, cmp_sign) were removed when the
    # template-only [E602]/[E604]/[E605] warnings stopped firing for
    # forall decls whose mono clones successfully compile (audit
    # recommendation 2 from #604, implemented in
    # vera/codegen/core.py::compile_program post-compile suppression
    # pass).  Each conformance/example program that exercises those
    # generics now produces a working mono clone with no template
    # noise.  See PR #659 for the fix.

    # NOTE: `head` entry (#655 Shape B) was removed in v0.0.146 when
    # `_alias_array_element` in `vera/wasm/inference.py` was extended
    # to unwrap `RefinementType` layers from alias targets.  See
    # PR #<TBD> for the fix.
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
    #
    # 60-second per-file timeout matches `check_html_examples.py`'s
    # `vera verify` subprocess timeout (the longest existing
    # per-file budget in any check script) — compile is faster
    # than verify, but a pathological program could hang on Z3
    # discharge inside the verify pass that compile triggers as
    # a side effect.  TimeoutExpired surfaces as a failure (same
    # shape as a JSON-decode failure), so the script never blocks
    # CI / pre-commit indefinitely.
    try:
        result = subprocess.run(
            [sys.executable, "-m", "vera.cli", "compile", "--wat",
             "--json", file],
            capture_output=True,
            text=True,
            timeout=60,
        )
    except subprocess.TimeoutExpired:
        return [(
            "TIMEOUT", file,
            "compile exceeded 60s — pathological program or "
            "infinite loop in compilation pipeline",
        )]
    try:
        envelope = json.loads(result.stdout)
    except json.JSONDecodeError:
        # Not JSON — compile produced something else (CLI error).
        # Surface as a failure with the stderr text inline.
        return [("PARSE_ERROR", file, result.stderr.strip()[:200])]

    # Hard compile failure (e.g. parse error, type error, unresolved
    # symbol) — the envelope is well-formed JSON but `ok` is False
    # and the error sits in `diagnostics`, not `warnings`.  Without
    # this check the script would treat the file as clean (because
    # `warnings` has no `[E602]` / `[E604]`), letting a real compile
    # failure slip through the gate.  Surface as a hard failure with
    # the first error's description (the gate's caller treats
    # COMPILE_ERROR identically to PARSE_ERROR / TIMEOUT — all three
    # are non-skip failures).
    if not envelope.get("ok", True):
        diagnostics = envelope.get("diagnostics", [])
        if diagnostics:
            first_err = diagnostics[0]
            err_code = first_err.get("error_code", "")
            err_desc = first_err.get("description", "")[:200]
            msg = f"[{err_code}] {err_desc}" if err_code else err_desc
        else:
            msg = (result.stderr.strip() or "compile failed")[:200]
        return [("COMPILE_ERROR", file, msg)]

    skips: list[tuple[str, str, str]] = []
    for w in envelope.get("warnings", []):
        code = w.get("error_code", "")
        # E605 is part of the same template-warning surface as E602/E604
        # — see the suppression pass in vera/codegen/core.py and the
        # CHANGELOG entry for v0.0.145.  A future E605 silent skip (e.g.
        # generic decl with unsupported return type) should hit the gate
        # too, not slip past with the existing allowlist machinery.
        if code not in ("E602", "E604", "E605"):
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


def _scan_paths(
    paths: list[str],
    used_allowlist: set[str] | None = None,
) -> tuple[int, list[str], list[str]]:
    """Compile every path; return (clean_count, skip_failures,
    hard_failures).

    Two failure categories with distinct semantics:

    - **skip_failures** — unexpected `[E602]` / `[E604]` warnings on
      function names that aren't in the allowlist (or are
      allowlisted under a different error code).  These are the
      core "silent skip" detections the gate exists for.
    - **hard_failures** — file-level failures: compile error
      (`COMPILE_ERROR`), unparseable JSON envelope (`PARSE_ERROR`),
      or compile timeout (`TIMEOUT`).  These mean the file couldn't
      be evaluated at all — distinct in kind from per-function
      skips and reported separately so the user can correlate
      cause and effect.

    Both are formatted as one-line strings ready for stderr.
    """
    skip_failures: list[str] = []
    hard_failures: list[str] = []
    clean = 0
    for path in paths:
        skips = _extract_skips(path)
        unexpected_skips: list[tuple[str, str, str]] = []
        path_hard_failures: list[tuple[str, str, str]] = []
        for code, fn_name, desc in skips:
            if code in ("PARSE_ERROR", "TIMEOUT", "COMPILE_ERROR"):
                path_hard_failures.append((code, fn_name, desc))
                continue
            if fn_name in ALLOWED_SKIPS:
                # Allowlisted — verify the code matches the
                # expected code (catches an unrelated skip on the
                # same function name).
                expected_code = ALLOWED_SKIPS[fn_name][0]
                if code != expected_code:
                    unexpected_skips.append((
                        code, fn_name,
                        f"unexpected code {code} (allowlist "
                        f"entry expects {expected_code}): {desc}",
                    ))
                elif used_allowlist is not None:
                    # Record this allowlist key as actually
                    # used — `main` will report stale entries
                    # (keys never matched against any warning)
                    # so they don't silently suppress future
                    # regressions when the underlying bug is
                    # fixed.
                    used_allowlist.add(fn_name)
                continue
            unexpected_skips.append((code, fn_name, desc))
        if not unexpected_skips and not path_hard_failures:
            clean += 1
            continue
        for code, fn_name, desc in unexpected_skips:
            skip_failures.append(
                f"{path}: [{code}] fn={fn_name!r}: {desc[:120]}"
            )
        for code, fn_name, desc in path_hard_failures:
            # fn_name is the file path for hard-failure tuples (see
            # `_extract_skips`); avoid the redundant fn= repeat.
            hard_failures.append(
                f"{path}: [{code}] {desc[:160]}"
            )
    return clean, skip_failures, hard_failures


def main() -> int:
    repo_root = Path(__file__).resolve().parent.parent

    examples = sorted(glob.glob(str(repo_root / "examples/*.vera")))

    # Filter conformance programs to those declared compilable in the
    # manifest.  `level: "check"` programs are intentionally
    # uncompilable — e.g. `ch03_typed_holes.vera` exists specifically
    # to demonstrate `[E614] Program contains a typed hole; fill all
    # holes before compiling` and is expected to fail at compile
    # time.  Only `verify` and `run` level programs are required to
    # compile cleanly; those are the ones a `[E602]` / `[E604]`
    # silent skip would actually regress.
    #
    # Fail fast on missing manifest or missing-but-listed file: the
    # manifest is the source of truth for the conformance suite and
    # a missing file is a state-inconsistency bug we want surfaced
    # loudly, not silently masked as "fewer programs to scan".
    manifest_path = repo_root / "tests/conformance/manifest.json"
    if not manifest_path.is_file():
        print(
            f"ERROR: conformance manifest not found at {manifest_path}",
            file=sys.stderr,
        )
        return 1

    # Load + parse the manifest defensively.  A corrupt or
    # locale-mis-encoded manifest would otherwise crash the gate
    # with a stack trace rather than the structured stderr
    # diagnostic this script promises.
    try:
        with manifest_path.open(encoding="utf-8") as f:
            manifest = json.load(f)
    except UnicodeDecodeError as exc:
        print(
            f"ERROR: conformance manifest at {manifest_path} is not "
            f"valid UTF-8: {exc}",
            file=sys.stderr,
        )
        return 1
    except json.JSONDecodeError as exc:
        print(
            f"ERROR: conformance manifest at {manifest_path} is not "
            f"valid JSON: {exc.msg} at line {exc.lineno}, "
            f"column {exc.colno}",
            file=sys.stderr,
        )
        return 1

    if not isinstance(manifest, list):
        print(
            f"ERROR: conformance manifest at {manifest_path} must "
            f"be a JSON array of entry objects; got "
            f"{type(manifest).__name__}",
            file=sys.stderr,
        )
        return 1

    # Validate every entry's file exists before populating the
    # scan list.  Surfacing missing-file errors *after* the scan
    # would let the gate run on an incomplete set silently.
    # Malformed entries (missing required keys, wrong shape) are
    # treated as hard errors with the entry id surfaced for
    # debugging.
    missing_files: list[tuple[str, str]] = []
    candidate_paths: list[str] = []
    for i, entry in enumerate(manifest):
        if not isinstance(entry, dict):
            print(
                f"ERROR: conformance manifest entry at index {i} "
                f"must be an object; got {type(entry).__name__}",
                file=sys.stderr,
            )
            return 1
        if entry.get("level") not in ("verify", "run"):
            continue
        entry_file = entry.get("file")
        if not isinstance(entry_file, str) or not entry_file:
            entry_id = entry.get("id", f"<entry {i}>")
            print(
                f"ERROR: conformance manifest entry id={entry_id!r} "
                f"at index {i} is missing required field 'file' "
                f"(or it isn't a non-empty string)",
                file=sys.stderr,
            )
            return 1
        path = repo_root / "tests/conformance" / entry_file
        if not path.is_file():
            missing_files.append((entry.get("id", "?"), entry_file))
            continue
        candidate_paths.append(str(path))

    if missing_files:
        print(
            f"ERROR: conformance manifest references "
            f"{len(missing_files)} file(s) that don't exist on disk:",
            file=sys.stderr,
        )
        for entry_id, fname in missing_files:
            print(
                f"  id={entry_id!r}: tests/conformance/{fname}",
                file=sys.stderr,
            )
        print(
            "\nManifest and filesystem are out of sync — fix by "
            "adding the missing files or removing the manifest "
            "entries.  The gate refuses to run on an incomplete "
            "scan set because a partial pass would silently hide "
            "regressions in the missing programs.",
            file=sys.stderr,
        )
        return 1

    conformance = sorted(candidate_paths)

    if not examples and not conformance:
        print("No .vera files found to scan.", file=sys.stderr)
        return 1

    all_paths = examples + conformance
    used_allowlist: set[str] = set()
    clean, skip_failures, hard_failures = _scan_paths(
        all_paths, used_allowlist=used_allowlist,
    )

    print(
        f"Scanned {len(all_paths)} files "
        f"({len(examples)} examples + {len(conformance)} "
        f"conformance programs).",
    )
    print(f"  Clean: {clean}")
    print(f"  Allowlisted skips suppressed: "
          f"{len(ALLOWED_SKIPS)} known functions "
          f"({len(used_allowlist)} matched, "
          f"{len(ALLOWED_SKIPS) - len(used_allowlist)} stale)")

    # Hard failures (PARSE_ERROR / TIMEOUT / COMPILE_ERROR) are
    # distinct from per-function skips — print first so the user
    # sees file-level problems before any per-function detail.
    if hard_failures:
        print(
            f"\nHARD FAILURES ({len(hard_failures)} file(s) the "
            f"gate could not evaluate — compile error, unparseable "
            f"JSON envelope, or timeout):",
            file=sys.stderr,
        )
        for f in hard_failures:
            print(f"  {f}", file=sys.stderr)
        print(
            "\nA hard failure means the file couldn't be compiled "
            "to produce the warning envelope this gate inspects.  "
            "Fix the underlying compile/parse error or address the "
            "timeout before the gate can evaluate per-function "
            "skips on this file.",
            file=sys.stderr,
        )

    if skip_failures:
        print(
            f"\nUNEXPECTED SKIPS ({len(skip_failures)} new "
            f"[E602]/[E604] warning(s) outside the allowlist):",
            file=sys.stderr,
        )
        for f in skip_failures:
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

    # Report stale allowlist entries (keys never matched against
    # any warning during the scan).  A stale entry is one whose
    # underlying bug is fixed but whose suppression record still
    # sits in `ALLOWED_SKIPS` — keeping it would silently mask a
    # future regression that re-introduces the same skip.  The
    # gate fails on stale entries so the allowlist shrinks
    # naturally as bugs close.
    stale_allowlist = sorted(set(ALLOWED_SKIPS) - used_allowlist)
    if stale_allowlist:
        print(
            f"\nSTALE ALLOWLIST ENTRIES ({len(stale_allowlist)} "
            f"function(s) never matched any warning during the "
            f"scan):",
            file=sys.stderr,
        )
        for fn_name in stale_allowlist:
            code, issue, reason = ALLOWED_SKIPS[fn_name]
            print(
                f"  {fn_name!r} [{code}] (tracked by #{issue}): "
                f"{reason[:100]}",
                file=sys.stderr,
            )
        print(
            "\nRemove stale entries from ALLOWED_SKIPS in "
            "scripts/check_e602_clean.py — keeping them silently "
            "masks a future regression that re-introduces the "
            "same skip.  If the underlying bug is still open, "
            "verify the affected example/conformance program "
            "actually exercises the function (otherwise the "
            "allowlist entry is suppressing nothing).",
            file=sys.stderr,
        )

    if hard_failures or skip_failures or stale_allowlist:
        return 1

    print("\nNo unexpected [E602]/[E604] skips. (Layer 1 of #626.)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
