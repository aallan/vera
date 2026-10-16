#!/usr/bin/env python3
"""The nightly mutation sweep: every function mutmut mutates in ``vera/``, a slice a night.

The whole-``vera/`` measure (MUTATION.md § The measure-all baseline).  About
110,000 mutants, each costing anything from a twentieth of a second (killed by
its first test) to most of an hour on a runner (a survivor runs every test
that reaches its function), so no run holds all of them; the one marathon that
tried hung four times under Python 3.14.  The sweep measures a slice a night
in ``JOBS`` parallel jobs and carries what each decided:

1. The inventory: every unit mutmut mutates (a top-level function, or a
   method of a top-level class), with a hash of its code (``ast``, docstrings
   set aside).  A unit's mutant count is mutmut's own, learned the first night
   mutmut generates it; until then the plan estimates it from the unit's size.
2. The state, carried from night to night in the workflow's artifact: each
   unit's hash, mutant count and decided mutants by number.  A unit whose code
   changed starts afresh, a unit gone from the tree is dropped, and a new
   engine version starts every unit afresh, since mutmut numbers a function's
   mutants by its own rules.
3. The night's plan: the undecided work in the tree's order (path, then
   line), filled into ``--of`` bins of one job's budget each at an estimated
   cost a mutant; a unit whose count is known splits across bins by its
   mutants' numbers, one whose count is not is taken whole.  Every job of the
   night computes the same plan from the same state, and job ``--slice`` runs
   its bin.
4. The run: PR #1727's machinery (``scripts/mutate_diff.py``) over a scratch
   tree of the head narrowed to the bin's units, the oracle every test file the
   lane's rule admits (one that reaches the compiler in process, bar the
   subprocess, Node and tooling families), the copy holding the whole tree.  A
   test that starts a Python or ``vera`` process is no oracle in the copy
   (``tests/mutation_oracle.py``), and one that fails there with no mutant
   active is dropped from the run and reported.
5. The stitch merges the night's slice records into the state.  When every
   unit's every mutant is decided the cycle closes: its per-module totals are
   kept in the state and written as ``mutation-summary.csv`` and the README
   badge's ``mutation.json`` (``summary``), which a pull request commits, and
   the next cycle starts.

A night that decides nothing, a slice whose engine or lane failed, and a slice
whose record is missing exit 2, and the workflow files a tracking issue;
survivors are the measurement, never a failure.

Usage:
    python scripts/mutate_sweep.py night --slice 0 --of 1 --state DIR --out DIR
    python scripts/mutate_sweep.py stitch --state DIR --slices DIR --of 1 --out DIR
    python scripts/mutate_sweep.py summary --state DIR --out DIR
"""

from __future__ import annotations

import argparse
import ast
import datetime
import hashlib
import io
import json
import os
import subprocess
import sys
import tarfile
import tempfile
import time
from collections import Counter
from collections.abc import Iterable, Mapping, Sequence
from dataclasses import dataclass
from pathlib import Path
from typing import Any

sys.path.insert(0, str(Path(__file__).resolve().parent))

import mutate_diff as md  # a sibling script, on the path above
from mutation_report import _badge_color

ROOT = Path(__file__).resolve().parent.parent

#: The state's file, inside the directory the workflow keeps as the
#: ``mutation-sweep-state`` artifact.
STATE_FILE = "sweep-state.json"

SCHEMA = 1

#: The jobs a scheduled night runs (the workflow's matrix).  The arithmetic:
#: the measured samples project a cycle at 160 to 250 runner hours of mutants;
#: a job's budget is 4.5 h, of which FIXED_S goes to the passes before its
#: first mutant, leaving 3.7 h of mutants a job, so 43 to 68 job-nights a
#: cycle, and 6.2 to 9.7 nights at seven jobs a night.
JOBS = 7

#: The most jobs a dispatched night may ask for.
MAX_JOBS = 12

#: A job's budget for mutmut, seconds (4.5 h of the 6 h a hosted job may run).
DEFAULT_BUDGET_S = 16200

#: Seconds a job spends before its first mutant, on a runner: generating the
#: bin's mutants, the stats pass over the whole oracle and the clean run of a
#: bin's covering tests.  A sample bin of five functions took 1,142 s on the
#: measuring machine (588 s of stats pass, 546 s of clean run), which is
#: about 2.5 times faster than a runner.
FIXED_S = 2900

#: Estimated runner seconds a mutant at four workers, by family: the soundness
#: core's mutants run the verifier's tests under Z3 (0.05 to 0.2 a second on
#: the measuring machine), the rest about one a second.
CORE_RATE_S = 25.0
OTHER_RATE_S = 2.5
CORE = ("vera/verifier.py", "vera/smt.py", "vera/checker/", "vera/obligations/")

#: mutmut's mutants per ``ast`` node of a unit, measured over vera/ at
#: 366bf326 (110,025 mutants in 2,541 units of 450,967 nodes); the estimate of
#: a unit's count until mutmut has generated it.
MUTANTS_PER_NODE = 0.24

#: Statuses that leave a mutant to a later night: mutmut never ran it, or the
#: run stopped while it ran.
UNDECIDED = frozenset({"not checked", "check was interrupted by user"})

#: Statuses a budget stop can leave on a mutant it cut short (a worker killed
#: is ``segfault``, one ended with an unexpected code ``suspicious``), so they
#: are taken from a run the budget did not stop, and left undecided otherwise.
CUT_SHORT = frozenset({"segfault", "suspicious"})

#: The nights the state keeps a line for.
KEPT_NIGHTS = 120


class StateError(ValueError):
    """The sweep's state, or a slice's record, is not one this script can use."""


# ---------------------------------------------------------------------------
# The inventory
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class SweepUnit:
    """A unit mutmut mutates: where it is, its code's hash, and its size."""

    path: str
    key: str
    start: int
    hash: str
    estimate: int

    @property
    def ident(self) -> str:
        return f"{self.path}::{self.key}"

    @property
    def module(self) -> str:
        return md.module_name(self.path)


def units_of(source: str, path: str) -> list[SweepUnit]:
    """The units mutmut mutates in one file, in its order."""
    tree = ast.parse(source)
    scanned = md.scan_units(source, path)
    found: list[SweepUnit] = []
    for node, cls in md._unit_nodes(tree):
        unit = scanned[md._key(node.name, cls)]
        if unit.excluded is not None:
            continue
        nodes = sum(1 for _ in ast.walk(node))
        found.append(SweepUnit(path=path, key=unit.key, start=unit.start,
                               hash=hashlib.sha256(unit.code.encode("utf-8")).hexdigest()[:16],
                               estimate=max(1, round(nodes * MUTANTS_PER_NODE))))
    return found


def inventory(sources: Mapping[str, str]) -> list[SweepUnit]:
    """Every unit of ``vera/``, in the tree's order (path, then line)."""
    units = [u for path in sorted(sources) for u in units_of(sources[path], path)]
    return sorted(units, key=lambda u: (u.path, u.start, u.key))


def vera_sources(repo: Path, rev: str) -> dict[str, str]:
    """``vera/``'s Python files at ``rev``, read from git (the checkout's own
    files may differ from the commit)."""
    archive = subprocess.run(["git", "-C", str(repo), "archive", "--format=tar", rev, "vera"],
                             capture_output=True, env=md._git_env(), check=False)
    if archive.returncode != 0:
        raise md.LaneError(f"git archive {rev} vera failed: "
                           f"{archive.stderr.decode('utf-8', 'replace')}")
    sources: dict[str, str] = {}
    with tarfile.open(fileobj=io.BytesIO(archive.stdout)) as tar:
        for member in tar.getmembers():
            if member.isfile() and member.name.endswith(".py"):
                handle = tar.extractfile(member)
                assert handle is not None
                sources[member.name] = handle.read().decode("utf-8")
    return sources


# ---------------------------------------------------------------------------
# The state
# ---------------------------------------------------------------------------


def empty_state(today: str) -> dict[str, Any]:
    """The state before the first night of the first cycle."""
    return {"schema": SCHEMA, "engine": None, "cycle": 1, "cycle_started": today,
            "calibration": 1.0, "units": {}, "last_complete": None, "nights": []}


def load_state(path: Path | None, today: str) -> dict[str, Any]:
    """The state in ``path``, or the first cycle's when there is none."""
    if path is None or not path.exists():
        return empty_state(today)
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError as exc:
        raise StateError(f"{path} is not JSON: {exc}") from exc
    if not isinstance(data, dict) or data.get("schema") != SCHEMA or not isinstance(
            data.get("units"), dict):
        raise StateError(f"{path} is not a schema {SCHEMA} sweep state")
    return data


def state_digest(path: Path | None) -> str:
    """The state file's identity, which every slice of a night must share."""
    if path is None or not path.exists():
        return "none"
    return hashlib.sha256(path.read_bytes()).hexdigest()


def save_state(state: Mapping[str, Any], directory: Path) -> Path:
    directory.mkdir(parents=True, exist_ok=True)
    path = directory / STATE_FILE
    path.write_text(json.dumps(state, indent=1, sort_keys=True, ensure_ascii=False) + "\n",
                    encoding="utf-8")
    return path


def _fresh(unit: SweepUnit) -> dict[str, Any]:
    return {"hash": unit.hash, "mutants": None, "statuses": {}}


def reconcile(state: Mapping[str, Any], units: Iterable[SweepUnit],
              engine: str) -> dict[str, Any]:
    """The state with one record for each unit in the tree: a unit whose code
    changed starts afresh, a unit gone is dropped, and a new engine version
    starts every unit afresh."""
    same_engine = state.get("engine") in (None, engine)
    records: dict[str, Any] = {}
    for unit in units:
        old = state["units"].get(unit.ident)
        if same_engine and old is not None and old.get("hash") == unit.hash:
            records[unit.ident] = {"hash": unit.hash, "mutants": old.get("mutants"),
                                   "statuses": dict(old.get("statuses", {}))}
        else:
            records[unit.ident] = _fresh(unit)
    return {**state, "engine": engine, "units": records}


def undecided(record: Mapping[str, Any]) -> list[int] | None:
    """A unit's undecided mutant numbers; None while its count is unknown."""
    count = record["mutants"]
    if count is None:
        return None
    return [n for n in range(1, count + 1) if str(n) not in record["statuses"]]


# ---------------------------------------------------------------------------
# A night's plan
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class Pick:
    """A job's share of one unit: the mutant numbers it runs, or None for
    every mutant of a unit whose count is not known yet."""

    unit: SweepUnit
    numbers: tuple[int, ...] | None


def rate(unit: SweepUnit, calibration: float = 1.0) -> float:
    """Estimated runner seconds a mutant of ``unit``."""
    base = CORE_RATE_S if unit.path.startswith(CORE) else OTHER_RATE_S
    return base * calibration


def plan(state: Mapping[str, Any], units: Sequence[SweepUnit], *, jobs: int,
         budget_s: float) -> list[list[Pick]]:
    """The night's work in ``jobs`` bins of one job's budget each.

    The undecided work in the tree's order fills each bin to the job's
    budget less ``FIXED_S``, at ``rate`` a mutant: a unit whose count is known
    splits across bins by its mutants' numbers, one whose count is not goes
    whole into one bin (into the next one when it does not fit and the bin
    holds something).  A bin's first piece is taken whatever its cost, so a
    bin with work open decides something."""
    capacity = max(budget_s - FIXED_S, budget_s / 4)
    calibration = float(state.get("calibration") or 1.0)
    bins: list[list[Pick]] = [[] for _ in range(jobs)]
    current = 0
    room = capacity
    for unit in units:
        if current >= jobs:
            break
        todo = undecided(state["units"][unit.ident])
        cost = rate(unit, calibration)
        if todo is None:
            whole = unit.estimate * cost
            if whole > room and bins[current]:
                current += 1
                room = capacity
                if current >= jobs:
                    break
            bins[current].append(Pick(unit=unit, numbers=None))
            room -= whole
            if room <= 0:
                current += 1
                room = capacity
            continue
        while todo and current < jobs:
            fit = int(room // cost)
            if fit <= 0 and not bins[current]:
                fit = 1
            if fit <= 0:
                current += 1
                room = capacity
                continue
            take, todo = todo[:fit], todo[fit:]
            bins[current].append(Pick(unit=unit, numbers=tuple(take)))
            room -= cost * len(take)
            if room < cost:
                current += 1
                room = capacity
    return bins


def engine_targets(picks: Sequence[Pick]) -> list[str]:
    """mutmut's arguments: a glob for a unit run whole, names for a part."""
    targets: list[str] = []
    for pick in picks:
        if pick.numbers is None:
            targets.append(md.mutant_glob(pick.unit.path, pick.unit.key))
        else:
            targets += [f"{pick.unit.module}.{pick.unit.key}__mutmut_{n}" for n in pick.numbers]
    return targets


# ---------------------------------------------------------------------------
# A night's slice: running the plan's bin
# ---------------------------------------------------------------------------


def slice_results(picks: Sequence[Pick], results: Mapping[str, str], *,
                  cut_short: bool) -> dict[str, Any]:
    """Each picked unit's mutant count and its decided mutants, from
    ``mutmut results``.  A unit's count is the number of its mutants mutmut
    lists (it generates every mutant of a unit it keeps).  A mutant of a unit
    the bin does not hold means the narrowing went wrong."""
    owners = {(p.unit.module, p.unit.key): p.unit for p in picks}
    listed: dict[str, dict[int, str]] = {p.unit.ident: {} for p in picks}
    for name, status in results.items():
        unit = owners.get(md.unit_of_mutant(name))
        if unit is None:
            raise StateError(f"a result for a function the night did not plan: {name}")
        listed[unit.ident][md._mutant_number(name)] = status
    out: dict[str, Any] = {}
    for pick in picks:
        statuses = listed[pick.unit.ident]
        count = len(statuses)
        if sorted(statuses) != list(range(1, count + 1)):
            raise StateError(f"mutmut numbered {pick.unit.ident}'s mutants with gaps")
        decided = {str(n): s for n, s in statuses.items()
                   if s not in UNDECIDED and not (cut_short and s in CUT_SHORT)}
        out[pick.unit.ident] = {"hash": pick.unit.hash, "mutants": count, "statuses": decided}
    return out


def _whole_tree(tree: Path) -> list[str]:
    """``also_copy`` for the whole archived tree: every top-level entry
    mutmut does not copy on its own account (``vera/``, its source)."""
    return sorted(p.name for p in tree.iterdir() if p.name not in ("vera", "mutants"))


def run_slice(args: argparse.Namespace, *, repo: Path, workdir: Path, engine: list[str],
              today: str) -> dict[str, Any]:
    """Plan the night and run slice ``args.slice``'s bin: its record."""
    started = time.monotonic()
    head = md._git(repo, "rev-parse", "--verify", "HEAD^{commit}").strip()
    env = md._git_env()
    env["PYTHONDONTWRITEBYTECODE"] = "1"
    skips = workdir / "oracle-skips.txt"
    env["MUTATION_ORACLE_SKIPS"] = str(skips)
    version = md._engine_version(engine, env)
    if not version:
        raise md.LaneError("the engine did not report its version")
    state_path = Path(args.state) if args.state else None
    units = inventory(vera_sources(repo, head))
    state = reconcile(load_state(state_path, today), units, version)
    bins = plan(state, units, jobs=args.of, budget_s=args.budget)
    picks = bins[args.slice]
    record: dict[str, Any] = {
        "schema": SCHEMA, "slice": args.slice, "of": args.of, "head": head,
        "state_in": state_digest(state_path), "engine": version, "budget_s": args.budget,
        "date": today, "planned": [{"unit": p.unit.ident, "hash": p.unit.hash,
                                    "numbers": None if p.numbers is None else list(p.numbers)}
                                   for p in picks],
        "results": {}, "stopped": None, "engine_exit": None, "engine_s": 0.0,
        "dropped_tests": [], "subprocess_tests": [], "selection": 0, "engine_tail": [],
    }
    if not picks:
        record["elapsed_s"] = round(time.monotonic() - started, 1)
        return record
    tree = workdir / "tree"
    tree.mkdir()
    md._extract(repo, head, tree)
    files = sorted({p.unit.path for p in picks})
    for path in files:
        keep = {p.unit.key for p in picks if p.unit.path == path}
        source = (tree / path).read_text(encoding="utf-8")
        (tree / path).write_text(md.narrow(source, keep), encoding="utf-8")
    tests = sorted(p.relative_to(tree).as_posix() for p in (tree / "tests").glob("test_*.py"))
    selection, _ = md.oracle_tests(tests, tree)
    record["selection"] = len(selection)
    pyproject = tree / "pyproject.toml"
    config = pyproject.read_text(encoding="utf-8")
    also_copy = _whole_tree(tree)
    run, log, dropped = md.run_dropping(
        [*engine, "run", "--max-children", str(args.max_children), *engine_targets(picks)],
        tree=tree, pyproject=pyproject, budget_s=args.budget, workdir=workdir, env=env,
        config_for=lambda dropped: md.rewrite_config(
            config, only_mutate=files, extra_tests=selection, also_copy=also_copy,
            extra_args=[f"--deselect={test}" for test in dropped]))
    record["engine_s"] = round(time.monotonic() - started, 1)
    record["dropped_tests"] = dropped
    if skips.exists():
        record["subprocess_tests"] = sorted(
            {line for line in skips.read_text(encoding="utf-8").splitlines() if line.strip()})
    record["engine_exit"] = run.returncode
    text = log.read_text(encoding="utf-8", errors="replace")
    no_tests = run.returncode == 1 and md.NO_TESTS_SENTENCE in text
    stopped = run.stopped or (None if run.returncode == 0 or no_tests else "engine")
    listed = md._engine_call(engine, ["results", "--all", "true"], cwd=tree, env=env)
    results: dict[str, str] = {}
    if listed is None or listed.returncode != 0:
        stopped = stopped or "engine"
    else:
        try:
            results = md.parse_results(listed.stdout)
        except md.ResultsError as exc:
            stopped = stopped or "engine"
            record["engine_tail"] = [str(exc)]
    if no_tests:
        results = {name: "no tests" for name in results}
    try:
        record["results"] = slice_results(picks, results, cut_short=run.stopped is not None)
    except StateError as exc:
        stopped = stopped or "unmapped"
        record["engine_tail"] = [str(exc)]
    record["stopped"] = stopped
    if stopped not in (None, "budget") and not record["engine_tail"]:
        record["engine_tail"] = md._tail(log)
    record["elapsed_s"] = round(time.monotonic() - started, 1)
    return record


def decided_count(record: Mapping[str, Any]) -> int:
    return sum(len(r["statuses"]) for r in record.get("results", {}).values())


def progress(record: Mapping[str, Any]) -> int:
    """What a slice moved on: its decided mutants, and the functions it took
    whole whose count it learned (one with no mutant at all is decided by
    that alone)."""
    learned = sum(1 for p in record.get("planned", [])
                  if p.get("numbers") is None and p.get("unit") in record.get("results", {}))
    return decided_count(record) + learned


def slice_exit(record: Mapping[str, Any]) -> int:
    """0 when the slice moved on, or had nothing to do; 2 when its engine or
    lane failed, or it moved nothing of the work it held."""
    if record.get("stopped") not in (None, "budget"):
        return 2
    if record.get("planned") and progress(record) == 0:
        return 2
    return 0


# ---------------------------------------------------------------------------
# The stitch: the night's slices into the state
# ---------------------------------------------------------------------------


def merge(state: dict[str, Any], record: Mapping[str, Any]) -> int:
    """Fold one slice's results into the state; what it moved on: the
    mutants newly decided and the functions newly counted."""
    added = 0
    for ident, result in record.get("results", {}).items():
        rec = state["units"].get(ident)
        if rec is None or rec["hash"] != result["hash"]:
            raise StateError(f"slice {record.get('slice')} ran {ident} at code the tree does not hold")
        if rec["mutants"] is not None and rec["mutants"] != result["mutants"]:
            raise StateError(f"slice {record.get('slice')} counts {result['mutants']} mutants of "
                             f"{ident}, where the state counts {rec['mutants']}")
        if rec["mutants"] is None:
            added += 1
        rec["mutants"] = result["mutants"]
        for number, status in result["statuses"].items():
            if number not in rec["statuses"]:
                added += 1
            rec["statuses"][number] = status
    return added


def _column(status: str) -> str:
    """Where a decided mutant counts in the committed summary."""
    if status in ("killed", "caught by type check"):
        return "killed"
    if status in ("timeout", "survived"):
        return status
    if status == "no tests":
        return "no_tests"
    return "other"


def tally(state: Mapping[str, Any], units: Iterable[SweepUnit]) -> dict[str, dict[str, int]]:
    """Per-module counts of the decided mutants, by summary column."""
    modules: dict[str, dict[str, int]] = {}
    for unit in units:
        row = modules.setdefault(unit.path, dict.fromkeys(
            ("killed", "survived", "timeout", "no_tests", "other"), 0))
        for status in state["units"][unit.ident]["statuses"].values():
            row[_column(status)] += 1
    return modules


def complete(state: Mapping[str, Any], units: Iterable[SweepUnit]) -> bool:
    """Whether every unit's count is known and every mutant decided."""
    return all(undecided(state["units"][u.ident]) == [] for u in units)


def close_cycle(state: dict[str, Any], units: Sequence[SweepUnit], *, head: str,
                today: str) -> bool:
    """Close the cycle when it is complete: its per-module totals and its
    survivors become ``last_complete``, and the next cycle starts."""
    if not complete(state, units):
        return False
    survivors = sorted(
        f"{u.module}.{u.key}__mutmut_{n}:{s}" for u in units
        for n, s in state["units"][u.ident]["statuses"].items() if s in ("survived", "timeout"))
    state["last_complete"] = {"cycle": state["cycle"], "started": state["cycle_started"],
                              "finished": today, "head": head, "engine": state["engine"],
                              "modules": tally(state, units), "survivors": survivors}
    state["cycle"] += 1
    state["cycle_started"] = today
    for rec in state["units"].values():
        rec["statuses"] = {}
    return True


def calibrate(state: dict[str, Any], records: Sequence[Mapping[str, Any]],
              units: Mapping[str, SweepUnit]) -> None:
    """Fold the night's measured cost into ``calibration``, the factor on
    ``rate``: the mutants' runner seconds against their estimate."""
    spent = estimate = 0.0
    for record in records:
        decided = [(ident, len(r["statuses"])) for ident, r in record.get("results", {}).items()]
        cost = sum(rate(units[ident]) * n for ident, n in decided if ident in units)
        if cost <= 0:
            continue
        spent += max(float(record.get("engine_s", 0.0)) - FIXED_S, 0.0)
        estimate += cost
    if estimate > 0:
        ratio = spent / estimate
        old = float(state.get("calibration") or 1.0)
        state["calibration"] = round(min(max((old + ratio) / 2, 0.2), 5.0), 3)


def stitch(state_in: Mapping[str, Any], digest: str, records: Sequence[Mapping[str, Any]], *,
           jobs: int, head: str, units: Sequence[SweepUnit], today: str,
           ) -> tuple[dict[str, Any], dict[str, Any]]:
    """The night's records folded into the state: the new state and the
    night's line (what each slice did, and what the night failed at)."""
    problems: list[str] = []
    valid: list[Mapping[str, Any]] = []
    seen: set[int] = set()
    engines = {r.get("engine") for r in records}
    if len(engines) > 1:
        problems.append(f"the slices ran different engines: {sorted(map(str, engines))}")
    for record in records:
        where = f"slice {record.get('slice')}"
        if record.get("schema") != SCHEMA or record.get("of") != jobs:
            problems.append(f"{where}: not a record of this night's {jobs} slices")
        elif record.get("head") != head:
            problems.append(f"{where}: ran {record.get('head')}, not {head}")
        elif record.get("state_in") != digest:
            problems.append(f"{where}: planned from another state")
        elif record["slice"] in seen:
            problems.append(f"{where}: two records")
        else:
            seen.add(record["slice"])
            valid.append(record)
    missing = sorted(set(range(jobs)) - seen)
    if missing:
        problems.append(f"no record from slice(s) {', '.join(map(str, missing))}")
    engine = next((str(r["engine"]) for r in valid if r.get("engine")), state_in.get("engine") or "")
    state = reconcile(state_in, units, engine)
    added = 0
    for record in valid:
        try:
            added += merge(state, record)
        except StateError as exc:
            problems.append(str(exc))
        if record.get("stopped") not in (None, "budget"):
            problems.append(f"slice {record['slice']}: stopped by the {record['stopped']}")
    if not problems and added == 0 and any(r.get("planned") for r in valid):
        problems.append("the night decided no mutant and counted no function")
    if not any(r.get("planned") for r in valid) and not complete(state, units):
        problems.append("the night planned nothing while the cycle is open")
    calibrate(state, valid, {u.ident: u for u in units})
    closed = close_cycle(state, units, head=head, today=today) if not problems else False
    night = {"date": today, "head": head, "jobs": jobs, "moved": added,
             "slices": [{"slice": r["slice"], "planned": len(r.get("planned", [])),
                         "decided": decided_count(r), "stopped": r.get("stopped"),
                         "engine_s": r.get("engine_s"), "dropped_tests": r.get("dropped_tests", []),
                         "subprocess_tests": len(r.get("subprocess_tests", []))}
                        for r in sorted(valid, key=lambda r: r["slice"])],
             "problems": problems, "closed": closed}
    state["nights"] = [*state.get("nights", []), night][-KEPT_NIGHTS:]
    return state, night


# ---------------------------------------------------------------------------
# The committed summary
# ---------------------------------------------------------------------------


def _pct(caught: int, total: int) -> float:
    return round(caught / total * 100, 1) if total else 0.0


def write_summary(state: Mapping[str, Any], directory: Path) -> float:
    """``mutation-summary.csv``, ``mutation.json`` and ``mutation-survivors.csv``
    from the last closed cycle, in ``scripts/mutation_report.py``'s format;
    the score.  A module's total is its mutants an in-process test reaches
    with a known outcome (killed, survived, timeout): its ``no tests``
    mutants are not observable in process, and its ``segfault`` and
    ``suspicious`` ones have no outcome to score."""
    last = state.get("last_complete")
    if not last:
        raise StateError("no cycle has closed yet, so there is no summary to write")
    rows = []
    for module, row in last["modules"].items():
        total = row["killed"] + row["survived"] + row["timeout"]
        if total:
            rows.append((module, total, row["killed"], row["survived"], row["timeout"],
                         _pct(row["killed"] + row["timeout"], total)))
    if not rows:
        raise StateError("the closed cycle scored no mutant")
    rows.sort(key=lambda r: (-r[3], r[0]))
    total = sum(r[1] for r in rows)
    killed = sum(r[2] for r in rows)
    survived = sum(r[3] for r in rows)
    timeout = sum(r[4] for r in rows)
    score = _pct(killed + timeout, total)
    directory.mkdir(parents=True, exist_ok=True)
    lines = ["module,total,killed,survived,timeout,caught_pct"]
    lines += [",".join(str(v) for v in r) for r in rows]
    lines.append(f"TOTAL (vera),{total},{killed},{survived},{timeout},{score}")
    (directory / "mutation-summary.csv").write_text("\n".join(lines) + "\n", encoding="utf-8")
    (directory / "mutation.json").write_text(json.dumps({
        "schemaVersion": 1, "label": "mutation", "message": f"{score}%",
        "color": _badge_color(score)}) + "\n", encoding="utf-8")
    inventory_lines = ["module,mutant,status"]
    for entry in last["survivors"]:
        name, _, status = entry.rpartition(":")
        module, key = md.unit_of_mutant(name)
        inventory_lines.append(f"{module},{key}__mutmut_{md._mutant_number(name)},{status}")
    (directory / "mutation-survivors.csv").write_text("\n".join(inventory_lines) + "\n",
                                                      encoding="utf-8")
    return score


# ---------------------------------------------------------------------------
# The reports
# ---------------------------------------------------------------------------


def render_slice(record: Mapping[str, Any]) -> str:
    counts: Counter[str] = Counter(s for r in record.get("results", {}).values()
                                   for s in r["statuses"].values())
    out = [f"## Mutation sweep: slice {record['slice']} of {record['of']}", "",
           f"`{str(record['head'])[:12]}`, mutmut {record.get('engine') or '(not run)'}, "
           f"budget {record['budget_s']:g} s, {record.get('elapsed_s', 0):.0f} s elapsed; "
           f"{len(record['planned'])} unit(s) planned, {decided_count(record)} mutant(s) decided"
           + (f", the oracle {record['selection']} test files" if record.get("selection") else "")
           + ".", ""]
    if counts:
        out.append(", ".join(f"{status}: {n}" for status, n in sorted(counts.items())))
        out.append("")
    if record.get("stopped"):
        out.append(f"Stopped by the {record['stopped']}.")
        out.append("")
    if record.get("dropped_tests"):
        out.append("Dropped from the oracle (each failed inside mutmut's copy with no mutant "
                   "active):")
        out += [f"- `{t}`" for t in record["dropped_tests"]]
        out.append("")
    if record.get("subprocess_tests"):
        out.append(f"{len(record['subprocess_tests'])} test(s) started a Python or `vera` process "
                   "and were no oracle in mutmut's copy (the record lists them).")
        out.append("")
    if record.get("engine_tail"):
        out += ["```", *record["engine_tail"], "```", ""]
    return "\n".join(out)


def render_night(state: Mapping[str, Any], night: Mapping[str, Any],
                 units: Sequence[SweepUnit]) -> str:
    known = [state["units"][u.ident] for u in units]
    counted = sum(r["mutants"] or 0 for r in known)
    decided = sum(len(r["statuses"]) for r in known)
    unknown = sum(1 for r in known if r["mutants"] is None)
    out = [f"## Mutation sweep: {night['date']}", "",
           f"`{night['head'][:12]}`, {night['jobs']} job(s): {night['moved']} mutant(s) decided or "
           f"function(s) counted tonight.  Cycle {state['cycle']} (from {state['cycle_started']}): {decided} of "
           f"{counted} counted mutants decided, {unknown} of {len(units)} functions not yet "
           f"generated.", ""]
    if night["slices"]:
        out += ["| Slice | Units | Decided | Stopped | Engine s |", "|---:|---:|---:|---|---:|"]
        out += [f"| {s['slice']} | {s['planned']} | {s['decided']} | {s['stopped'] or ''} | "
                f"{s['engine_s'] or 0:.0f} |" for s in night["slices"]]
        out.append("")
    if night["problems"]:
        out.append("**Stopped short:**")
        out += [f"- {p}" for p in night["problems"]]
        out.append("")
    if night["closed"]:
        last = state["last_complete"]
        out.append(f"**Cycle {last['cycle']} closed** ({last['started']} to {last['finished']}); "
                   "its summary is in this artifact.")
        out.append("")
    return "\n".join(out)


# ---------------------------------------------------------------------------
# The command line
# ---------------------------------------------------------------------------


def _today() -> str:
    return datetime.datetime.now(datetime.timezone.utc).date().isoformat()


def _write(path: str | None, text: str) -> None:
    if path:
        with open(path, "a", encoding="utf-8") as fh:
            fh.write(text + "\n")


def _state_file(directory: str | None) -> Path | None:
    return Path(directory) / STATE_FILE if directory else None


def cmd_night(args: argparse.Namespace) -> int:
    repo = Path(args.repo).resolve()
    out = Path(args.out).resolve()
    out.mkdir(parents=True, exist_ok=True)
    if args.workdir:
        workdir = Path(args.workdir).resolve()
        if workdir.exists() and any(workdir.iterdir()):
            raise SystemExit(f"--workdir {workdir} is not empty")
        workdir.mkdir(parents=True, exist_ok=True)
    else:
        workdir = Path(tempfile.mkdtemp(prefix="vera-mutate-sweep-"))
    engine = list(args.engine) if args.engine else md._default_engine()
    args.state = str(_state_file(args.state)) if args.state else None
    try:
        record = run_slice(args, repo=repo, workdir=workdir, engine=engine, today=_today())
    except Exception as exc:  # noqa: BLE001 — a failure of the lane is exit 2, recorded
        import traceback

        traceback.print_exc()
        record = {"schema": SCHEMA, "slice": args.slice, "of": args.of, "head": None,
                  "state_in": state_digest(Path(args.state) if args.state else None),
                  "engine": None, "budget_s": args.budget, "planned": [], "results": {},
                  "stopped": "lane", "engine_tail": [f"{type(exc).__name__}: {exc}"],
                  "dropped_tests": [], "subprocess_tests": []}
    (out / f"slice-{args.slice}.json").write_text(
        json.dumps(record, indent=1, sort_keys=True, ensure_ascii=False) + "\n", encoding="utf-8")
    report = render_slice(record)
    print(report)
    _write(args.summary, report)
    return slice_exit(record)


def cmd_stitch(args: argparse.Namespace) -> int:
    repo = Path(args.repo).resolve()
    head = md._git(repo, "rev-parse", "--verify", "HEAD^{commit}").strip()
    state_path = _state_file(args.state)
    today = _today()
    state_in = load_state(state_path, today)
    records = []
    for path in sorted(Path(args.slices).glob("slice-*.json")) if args.slices else []:
        records.append(json.loads(path.read_text(encoding="utf-8")))
    units = inventory(vera_sources(repo, head))
    state, night = stitch(state_in, state_digest(state_path), records, jobs=args.of, head=head,
                          units=units, today=today)
    out = Path(args.out)
    save_state(state, out)
    if night["closed"]:
        write_summary(state, out)
    report = render_night(state, night, units)
    print(report)
    _write(args.summary, report)
    return 2 if night["problems"] else 0


def cmd_matrix(args: argparse.Namespace) -> int:
    """The workflow's matrix: ``JOBS`` jobs on the schedule, the number asked
    for on a dispatch (one when none is given)."""
    jobs = JOBS if args.event == "schedule" else int(args.requested or 1)
    if not 1 <= jobs <= MAX_JOBS:
        print(f"error: a night runs 1 to {MAX_JOBS} jobs, not {jobs}", file=sys.stderr)
        return 2
    print(f"jobs={jobs}")
    print(f"slices={json.dumps(list(range(jobs)))}")
    return 0


def cmd_summary(args: argparse.Namespace) -> int:
    state = load_state(_state_file(args.state), _today())
    score = write_summary(state, Path(args.out))
    print(f"cycle {state['last_complete']['cycle']}: {score}% caught; wrote "
          f"mutation-summary.csv, mutation.json and mutation-survivors.csv to {args.out}")
    return 0


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=(__doc__ or "").splitlines()[0])
    sub = parser.add_subparsers(dest="command", required=True)
    night = sub.add_parser("night", help="plan the night and run one slice of it")
    night.add_argument("--slice", type=int, default=0, help="this job's slice (default 0)")
    night.add_argument("--of", type=int, default=1, help="the night's slices (default 1)")
    night.add_argument("--state", help="the directory holding the last state (none: cycle 1)")
    night.add_argument("--out", required=True, help="the directory for slice-<n>.json")
    night.add_argument("--budget", type=float, default=DEFAULT_BUDGET_S,
                       help=f"wall-clock seconds for mutmut (default {DEFAULT_BUDGET_S})")
    night.add_argument("--max-children", type=int, default=os.cpu_count() or 1,
                       help="mutmut's parallel workers (default: every CPU)")
    night.add_argument("--repo", default=str(ROOT), help="the repository (default: this one)")
    night.add_argument("--workdir", help="an empty or absent directory for the scratch tree")
    night.add_argument("--summary", help="append the Markdown summary here")
    night.add_argument("--engine", nargs="+", help="the mutmut command")
    stitch_p = sub.add_parser("stitch", help="fold the night's slices into the state")
    stitch_p.add_argument("--state", help="the directory holding the last state (none: cycle 1)")
    stitch_p.add_argument("--slices", help="the directory holding the night's slice-<n>.json")
    stitch_p.add_argument("--of", type=int, default=1, help="the night's slices (default 1)")
    stitch_p.add_argument("--out", required=True, help="the directory for the new state")
    stitch_p.add_argument("--repo", default=str(ROOT), help="the repository (default: this one)")
    stitch_p.add_argument("--summary", help="append the Markdown summary here")
    summary = sub.add_parser("summary", help="write the last closed cycle's committed files")
    summary.add_argument("--state", required=True, help="the directory holding the state")
    summary.add_argument("--out", default=str(ROOT), help="where to write them (default: the "
                         "repository root)")
    matrix = sub.add_parser("matrix", help="print the workflow's matrix outputs")
    matrix.add_argument("--event", required=True, help="the event that started the run")
    matrix.add_argument("--requested", default="", help="the dispatch's jobs input")
    args = parser.parse_args(argv)
    if args.command in ("night", "stitch") and not 0 <= getattr(args, "slice", 0) < args.of:
        parser.error("--slice must be at least 0 and less than --of")
    commands = {"night": cmd_night, "stitch": cmd_stitch, "summary": cmd_summary,
                "matrix": cmd_matrix}
    return commands[args.command](args)


if __name__ == "__main__":
    raise SystemExit(main())
