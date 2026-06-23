#!/usr/bin/env python3
"""Turn a mutmut run into the committed score + badge + the issue artefacts.

Mutation testing (#387).  Reads `mutmut results` (the survivor + timeout
list — mutmut does not list killed mutants) and the generated `mutants/`
tree (to recover per-module totals), and writes:

  * mutation-summary.csv  — per-module total/killed/survived/timeout/caught%
                            (committed: a diff-able score history across sweeps)
  * mutation.json         — shields.io endpoint badge for the README
  * mutation-survivors.csv — the survivor + timeout inventory (module, mutant,
                            status) for the #387 issue attachment (not committed)

Usage:  python scripts/mutation_report.py [--results FILE] [--label core]
        (defaults: run `mutmut results`; label "core")

Mutation score = caught / total = (killed + timeout) / total.  Timeouts are
counted as caught by convention; the runbook's guardrail applies (a slow-Z3
timeout can mask a gap), so the survivor inventory is the actionable artefact,
not the headline percentage alone.
"""
from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from collections import Counter
from pathlib import Path

# A mutmut mutant name is "<dotted.module>.x<sep><mangled>__mutmut_<N>"; the
# separator after "x" is "_" (module function, e.g. x_verify / x__adt) or "ǁ"
# (class method, xǁClassǁmethod).  Capture the module prefix (shortest, up to
# the first ".x_"/".xǁ").
_LINE = re.compile(r"^\s*(\S+?)\.x[_ǁ].*:\s*(survived|timeout)\s*$")
# A generated mutant definition (excludes the "__mutmut_orig" baseline copy).
# ".*" spans the "__"/"ǁClassǁ" prefix (the "ǁ" separator is non-ASCII, so it
# can't appear in a bytes literal — but ".*" matches its bytes fine).
_MUTANT_DEF = re.compile(rb"def x.*__mutmut_[0-9]+\(")


def _module_path(mod: str, mutants_root: Path) -> Path | None:
    """vera.smt -> mutants/vera/smt.py ; vera.obligations -> .../obligations/__init__.py"""
    base = mutants_root / Path(mod.replace(".", "/"))
    for cand in (base.with_suffix(".py"), base / "__init__.py"):
        if cand.exists():
            return cand
    return None


def _count_total(path: Path) -> int:
    """Count generated mutants in a file (one ``def x…__mutmut_N(`` per mutant)."""
    n = 0
    with path.open("rb") as fh:
        for line in fh:
            if _MUTANT_DEF.search(line):
                n += 1
    return n


def _badge_color(pct: float) -> str:
    if pct >= 90:
        return "brightgreen"
    if pct >= 80:
        return "green"
    if pct >= 70:
        return "yellowgreen"
    if pct >= 60:
        return "yellow"
    return "orange"


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--results", help="captured `mutmut results` output; else runs it")
    ap.add_argument("--mutants", default="mutants", help="mutmut mutants/ dir")
    ap.add_argument("--label", default="core", help="badge scope label")
    args = ap.parse_args()

    if args.results:
        text = Path(args.results).read_text(encoding="utf-8")
    else:
        text = subprocess.run(
            ["mutmut", "results"], capture_output=True, text=True, check=True
        ).stdout

    survived: Counter[str] = Counter()
    timeout: Counter[str] = Counter()
    inventory: list[tuple[str, str, str]] = []  # (module, mutant, status)
    unmatched = 0
    for line in text.splitlines():
        m = _LINE.match(line)
        if not m:
            if line.strip().endswith((": survived", ": timeout")):
                unmatched += 1
            continue
        mod, status = m.group(1), m.group(2)
        (survived if status == "survived" else timeout)[mod] += 1
        inventory.append((mod, line.strip().rsplit(":", 1)[0].strip(), status))
    if unmatched:
        print(f"  warning: {unmatched} survived/timeout lines did not parse", file=sys.stderr)

    mutants_root = Path(args.mutants)
    mods = sorted(set(survived) | set(timeout))
    rows = []
    for mod in mods:
        path = _module_path(mod, mutants_root)
        total = _count_total(path) if path else (survived[mod] + timeout[mod])
        label = str(path.relative_to(mutants_root)) if path else mod.replace(".", "/") + ".py"
        s, t = survived[mod], timeout[mod]
        killed = max(total - s - t, 0)
        caught = killed + t
        rows.append({
            "module": label,
            "total": total, "killed": killed, "survived": s, "timeout": t,
            "caught_pct": round(caught / total * 100, 1) if total else 0.0,
        })

    T = sum(r["total"] for r in rows)
    S = sum(r["survived"] for r in rows)
    TO = sum(r["timeout"] for r in rows)
    K = T - S - TO
    score = round((K + TO) / T * 100, 1) if T else 0.0

    # mutation-summary.csv (committed)
    with open("mutation-summary.csv", "w", encoding="utf-8") as fh:
        fh.write("module,total,killed,survived,timeout,caught_pct\n")
        for r in sorted(rows, key=lambda r: r["survived"], reverse=True):
            fh.write(f"{r['module']},{r['total']},{r['killed']},{r['survived']},{r['timeout']},{r['caught_pct']}\n")
        fh.write(f"TOTAL ({args.label}),{T},{K},{S},{TO},{score}\n")

    # mutation.json (committed; shields.io endpoint badge)
    Path("mutation.json").write_text(json.dumps({
        "schemaVersion": 1,
        "label": f"mutation ({args.label})",
        "message": f"{score}%",
        "color": _badge_color(score),
    }) + "\n", encoding="utf-8")

    # mutation-survivors.csv (issue attachment; not committed)
    with open("mutation-survivors.csv", "w", encoding="utf-8") as fh:
        fh.write("module,mutant,status\n")
        for mod, mutant, status in sorted(inventory):
            fh.write(f"{mod.replace('.', '/')}.py,{mutant},{status}\n")

    print(f"\nMutation score ({args.label}): {score}%  "
          f"[{K} killed + {TO} timeout caught / {T} total; {S} survived]")
    print("  wrote mutation-summary.csv, mutation.json, mutation-survivors.csv")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
