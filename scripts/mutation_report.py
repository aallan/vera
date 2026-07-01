#!/usr/bin/env python3
"""Turn a mutmut run into the committed score + badge + the issue artefacts.

Mutation testing (#387).  Reads `mutmut results` (the survivor + timeout
list — mutmut does not list killed mutants) and the generated `mutants/`
tree (to recover per-module totals), and writes, at the repo root:

  * mutation-summary.csv   — per-module total/killed/survived/timeout/caught%
                             (committed: a diff-able score history across sweeps)
  * mutation.json          — shields.io endpoint badge for the README
  * mutation-survivors.csv — the survivor + timeout inventory (module, mutant,
                             status) for the #387 issue attachment (gitignored)
  * mutation-<label>.png   — a per-module killed/survived/timeout chart for the
                             issue attachment (gitignored; needs matplotlib,
                             which ships in the `[mutation]` extra)

Usage:  python scripts/mutation_report.py [--results FILE] [--mutants DIR]
                                          [--label core]
        (defaults: run `mutmut results`; mutants "<repo>/mutants"; label "core")

Mutation score = caught / total = (killed + timeout) / total.  Timeouts are
counted as caught by convention; the runbook's guardrail applies (a slow-Z3
timeout can mask a gap), so the survivor inventory is the actionable artefact,
not the headline percentage alone.

A mutation score is committed and rendered as a public badge, so this script
fails LOUD rather than emit a number it cannot stand behind.  Each of these is
a hard error (nonzero exit, nothing written), never a warning over a written
score: an empty corpus (`T == 0`), an unparseable result line (mutmut format
drift), a `mutmut results` status the parser does not model (it lists every
non-killed mutant, so "not checked" / "suspicious" / "caught by type check" can
appear and must not be folded into killed), a module whose file is missing from
the mutants/ tree, and a per-module total below its survived+timeout count (a
`_count_total` undercount).
"""
from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from collections import Counter
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent

# A mutmut mutant name is "<dotted.module>.x<sep><mangled>__mutmut_<N>"; the
# separator after "x" is "_" (module function, e.g. x_verify / x__adt_sort_key)
# or "ǁ" (U+01C1, class method, xǁClassǁmethod).  Capture the module with a
# *greedy* prefix anchored on the LAST ".x<sep>...__mutmut_<N>", so a module
# path that itself contains ".x_" (e.g. a future vera/x*.py) is not mis-split.
_LINE = re.compile(
    r"^\s*(.+)\.x[_ǁ]\S*__mutmut_\d+\s*:\s*(survived|timeout)\s*$"
)
# A generated mutant definition, anchored at the start of the (possibly
# indented) line so it cannot match a second "def" later on the line and does
# not require the "(" (which black could in principle wrap to the next line).
# "__mutmut_[0-9]+" excludes the "__mutmut_orig" baseline copy.  Bytes regex
# (the file is read as bytes); "\S" matches the non-ASCII "ǁ" separator bytes.
_MUTANT_DEF = re.compile(rb"^\s*def x\S*__mutmut_[0-9]+")
# Any mutmut result line, whatever the status: "<mutant>__mutmut_<N>: <status>".
# `mutmut results` skips killed (derived from the tree total) but prints every
# OTHER status, so besides survived/timeout it can emit "not checked",
# "suspicious", and "caught by type check".  Used to fail loud on a status this
# parser does not model rather than silently fold it into killed.
_ANY_STATUS = re.compile(r"__mutmut_\d+\s*:\s*(.+)$")


def _fail(msg: str) -> int:
    """Print a hard-error to stderr and return the nonzero exit code."""
    print(f"error: {msg}", file=sys.stderr)
    return 1


def _module_of(rel: Path) -> str:
    """mutants-relative path -> dotted module (vera/smt.py -> vera.smt;
    vera/obligations/__init__.py -> vera.obligations)."""
    parts = rel.parent.parts if rel.name == "__init__.py" else rel.with_suffix("").parts
    return ".".join(parts)


def _count_total(path: Path) -> int:
    """Count generated mutants in a file (one ``def x…__mutmut_N`` per mutant)."""
    n = 0
    with path.open("rb") as fh:
        for line in fh:
            if _MUTANT_DEF.search(line):
                n += 1
    return n


def _badge_color(pct: float) -> str:
    """Shields.io badge colour band for a caught-percentage."""
    if pct >= 90:
        return "brightgreen"
    if pct >= 80:
        return "green"
    if pct >= 70:
        return "yellowgreen"
    if pct >= 60:
        return "yellow"
    if pct >= 50:
        return "orange"
    return "red"


def _write_chart(rows: list[dict], label: str, score: float, out: Path) -> None:
    """Per-module killed/survived/timeout stacked bar (the #387 issue chart).

    Best-effort: skipped with a note if matplotlib is absent (it ships in the
    `[mutation]` extra, but the CSV + badge must still be produced without it).
    """
    try:
        import matplotlib
        matplotlib.use("Agg")
        import matplotlib.pyplot as plt
    except ImportError:
        print(f"  note: matplotlib not installed — skipping the chart ({out.name}); "
              'install it via `pip install -e ".[mutation]"`', file=sys.stderr)
        return

    ordered = sorted(rows, key=lambda r: r["survived"], reverse=True)
    mods = [r["module"] for r in ordered]
    killed = [r["killed"] for r in ordered]
    survived = [r["survived"] for r in ordered]
    timeout = [r["timeout"] for r in ordered]
    base = [k + s for k, s in zip(killed, survived)]
    y = range(len(mods))
    xmax = max((r["total"] for r in ordered), default=1)

    fig, ax = plt.subplots(figsize=(11, max(3.0, 0.5 * len(mods) + 1.5)))
    ax.barh(y, killed, color="#2ca02c", label="killed")
    ax.barh(y, survived, left=killed, color="#d62728", label="survived")
    ax.barh(y, timeout, left=base, color="#e8a33d", label="timeout")
    for i, r in enumerate(ordered):
        ax.text(r["total"] + xmax * 0.01, i, f"{r['caught_pct']:.0f}%",
                va="center", fontsize=8)
    ax.set_yticks(list(y))
    ax.set_yticklabels(mods, fontsize=8)
    ax.invert_yaxis()
    ax.set_xlabel("mutants")
    surv = sum(r["survived"] for r in rows)
    ax.set_title(f"Vera mutation testing ({label}) — {score}% caught, {surv:,} survivors")
    ax.legend(loc="lower right", fontsize=8)
    fig.tight_layout()
    fig.savefig(out, dpi=100)
    plt.close(fig)


def main() -> int:
    """Parse `mutmut results`, compute the score, and write the artefacts."""
    ap = argparse.ArgumentParser()
    ap.add_argument("--results", help="captured `mutmut results` output; else runs it")
    ap.add_argument("--mutants", default=str(REPO_ROOT / "mutants"),
                    help="mutmut mutants/ dir (default <repo>/mutants)")
    ap.add_argument("--label", default="core", help="badge scope label")
    args = ap.parse_args()

    if args.results:
        text = Path(args.results).read_text(encoding="utf-8")
    else:
        text = subprocess.run(
            ["mutmut", "results"], capture_output=True, text=True, encoding="utf-8", check=True
        ).stdout

    survived: Counter[str] = Counter()
    timeout: Counter[str] = Counter()
    inventory: list[tuple[str, str, str]] = []  # (module, mutant, status)
    unmatched = 0
    unhandled: Counter[str] = Counter()
    for line in text.splitlines():
        m = _LINE.match(line)
        if m:
            mod, status = m.group(1), m.group(2)
            (survived if status == "survived" else timeout)[mod] += 1
            inventory.append((mod, line.strip().rsplit(":", 1)[0].strip(), status))
            continue
        sm = _ANY_STATUS.search(line)
        if sm:
            other = sm.group(1).strip()
            if other in ("survived", "timeout"):
                unmatched += 1            # a survived/timeout line whose module part didn't parse
            else:
                unhandled[other] += 1     # not checked / suspicious / caught by type check / ...

    # Fail loud rather than emit a skewed score (#387 — a public badge).
    # A drifted survived/timeout line drops a survivor and inflates the caught%.
    if unmatched:
        return _fail(
            f"{unmatched} survived/timeout line(s) did not parse — mutmut output "
            "format may have changed; refusing to write a skewed score"
        )
    # killed is derived as (total − survived − timeout), so any other status
    # `mutmut results` lists (a partly-uncovered module's "not checked", a
    # "suspicious", a "caught by type check") would be silently miscounted as
    # killed.  The core sweep has none; a later per-module sweep may — refuse
    # until the parser models them explicitly.
    if unhandled:
        return _fail(
            f"`mutmut results` lists statuses this parser does not model: "
            f"{dict(unhandled)} — killed is derived as (total − survived − "
            "timeout), so these would be miscounted; add explicit per-status "
            "handling before scoring such a run"
        )

    mutants_root = Path(args.mutants)
    if not mutants_root.is_dir():
        return _fail(f"mutants dir {mutants_root} not found — run `mutmut run` first")

    # Derive the module set from the TREE, not from the survived/timeout keys:
    # `mutmut results` omits killed mutants, so a fully-killed module has no line
    # there and would otherwise drop out of the denominator entirely.  Every
    # module mutmut actually mutated has at least one `def x…__mutmut_N` in its
    # copied file; a copied-but-unmutated file (outside only_mutate, or an
    # also_copy path) has none and is skipped.
    rows: list[dict] = []
    mod_path: dict[str, str] = {}  # dotted module -> its actual tree-relative path
    for path in sorted(mutants_root.rglob("*.py")):
        total = _count_total(path)
        if total == 0:
            continue
        rel = path.relative_to(mutants_root)
        mod = _module_of(rel)
        mod_path[mod] = str(rel)
        s, t = survived[mod], timeout[mod]
        if total < s + t:
            return _fail(
                f"module {mod!r}: counted {total} mutants < {s + t} survived+timeout "
                "— _count_total undercount (mutant-def regex drift?)"
            )
        killed = total - s - t
        rows.append({
            "module": str(rel),
            "total": total, "killed": killed, "survived": s, "timeout": t,
            "caught_pct": round((killed + t) / total * 100, 1),
        })

    # A module with survivors/timeouts but no mutated file in the tree is a
    # results/tree desync — don't silently drop its survivors.
    missing = (set(survived) | set(timeout)) - set(mod_path)
    if missing:
        return _fail(
            f"modules {sorted(missing)} appear in `mutmut results` but have no "
            f"mutated file under {mutants_root}/ — tree out of sync with the cache"
        )

    T = sum(r["total"] for r in rows)
    if T == 0:
        return _fail(
            f"no mutated modules found under {mutants_root}/ (wrong --mutants dir, "
            "or `mutmut run` has not generated mutants) — refusing to write a score"
        )
    S = sum(r["survived"] for r in rows)
    TO = sum(r["timeout"] for r in rows)
    K = T - S - TO
    score = round((K + TO) / T * 100, 1)

    # mutation-summary.csv (committed)
    with (REPO_ROOT / "mutation-summary.csv").open("w", encoding="utf-8") as fh:
        fh.write("module,total,killed,survived,timeout,caught_pct\n")
        for r in sorted(rows, key=lambda r: r["survived"], reverse=True):
            fh.write(f"{r['module']},{r['total']},{r['killed']},{r['survived']},{r['timeout']},{r['caught_pct']}\n")
        fh.write(f"TOTAL ({args.label}),{T},{K},{S},{TO},{score}\n")

    # mutation.json (committed; shields.io endpoint badge).  The core sweep is
    # the headline badge — keep its label short ("mutation", like "codecov");
    # a scoped per-module sweep tags itself ("mutation (codegen)").
    badge_label = "mutation" if args.label == "core" else f"mutation ({args.label})"
    (REPO_ROOT / "mutation.json").write_text(json.dumps({
        "schemaVersion": 1,
        "label": badge_label,
        "message": f"{score}%",
        "color": _badge_color(score),
    }) + "\n", encoding="utf-8")

    # mutation-survivors.csv (issue attachment; gitignored).  The mutant column
    # is the bare name — the module is already its own column, taken from the
    # actual tree path (a package's survivors live in __init__.py, not <pkg>.py).
    with (REPO_ROOT / "mutation-survivors.csv").open("w", encoding="utf-8") as fh:
        fh.write("module,mutant,status\n")
        for mod, mutant, status in sorted(inventory):
            short = mutant[len(mod) + 1:] if mutant.startswith(mod + ".") else mutant
            fh.write(f"{mod_path[mod]},{short},{status}\n")

    # mutation-<label>.png (issue attachment; gitignored)
    _write_chart(rows, args.label, score, REPO_ROOT / f"mutation-{args.label}.png")

    print(f"\nMutation score ({args.label}): {score}%  "
          f"[{K} killed + {TO} timeout caught / {T} total; {S} survived]")
    print(f"  wrote mutation-summary.csv, mutation.json, mutation-survivors.csv, "
          f"mutation-{args.label}.png")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
