#!/usr/bin/env python3
"""The nightly mutation sweep: a sample of the mutants mutmut makes in ``vera/``, a cycle a night or two.

The whole-``vera/`` measure (MUTATION.md § The measure-all baseline).  The
tree holds about 113,000 mutants, each costing from a twentieth of a second
(killed by its first test) to most of an hour on a runner (a survivor runs
every test that reaches its function, and a compiler's front-end functions
are reached by thousands); measured over the nights of October 2026, the
sweep decided 300 to 1,300 a night, so every mutant would take months of
green nights against a tree that changes daily (#1827).  The sweep measures a
random sample instead, ``SAMPLE_FRACTION`` of the mutants, in ``JOBS``
parallel jobs a night, and carries what each decided:

1. The inventory: every unit mutmut mutates (a top-level function, or a
   method of a top-level class), with a hash of its code (``ast``, docstrings
   set aside).  A unit's mutant count is mutmut's own visitor's, asked through
   the engine's ``count`` command before the plan, so its mutants are
   ``1`` to ``n`` in the copy.
2. The state, carried from night to night in the workflow's artifact: each
   unit's hash, mutant count and decided mutants by number.  A unit whose code
   changed starts afresh, a unit gone from the tree is dropped, and a new
   engine version starts every unit afresh, since mutmut numbers a function's
   mutants by its own rules.
3. The sample: mutant ``n`` of a unit is in the cycle's sample when a hash
   of the cycle, the unit and ``n`` falls under ``SAMPLE_FRACTION``, so every
   job of a night and every night of the cycle draws the same sample, each
   mutant with the same chance, and the next cycle draws another.
4. The night's plan: the sample's undecided mutants in the tree's order
   (path, then line), filled into ``--of`` bins of one job's budget each at
   an estimated cost a mutant, a unit splitting across bins by its mutants'
   numbers.  Every job of the night computes the same plan from the same
   state, and job ``--slice`` runs its bin.
5. The run: PR #1727's machinery (``scripts/mutate_diff.py``) over a scratch
   tree of the head narrowed to the bin's units, the oracle every test file the
   lane's rule admits (one that reaches the compiler in process, bar the
   subprocess, Node and tooling families), the copy holding the whole tree.  A
   test that starts a Python or ``vera`` process, or reads the compiler's
   source, is no oracle in the copy (``tests/mutation_oracle.py``); one that
   fails there with no mutant active is dropped from the run and reported, and
   every night after deselects it from the start.  An exception the engine's
   own code raises stops the slice instead, dropping no further test, and
   its record and the night's report name the exception and the engine's
   frame.
6. The stitch merges the night's slice records into the state.  When every
   sampled mutant is decided the cycle closes: its per-module totals are kept
   in the state and written as ``mutation-summary.csv`` and the README badge's
   ``mutation.json`` (``summary``), the score with its 95% interval, which a
   pull request commits, and the next cycle starts.

A night that decides nothing, a slice whose engine or lane failed, and a slice
whose budget ran out before its first mutant exit 2, and the workflow files a
tracking issue; survivors are the measurement, never a failure.  A step that
fails before the sweep runs, while the runner is still there, writes a lane
record (``lane-failed``), reported like any other.  A slice whose record is
missing (its runner was lost before it could upload one) is noted and its
work waits for the next night, unless more than LOST_LIMIT_NIGHT are missing
in one night, which is a hazard the night reports.

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
import math
import os
import re
import subprocess
import sys
import tarfile
import tempfile
import threading
import time
from collections import Counter
from collections.abc import Callable, Iterable, Mapping, Sequence
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
#: a job's budget is 4.5 h, of which FIXED_S goes to the passes before its
#: first mutant, leaving 2.5 h of mutants a job, 17.5 runner hours a night;
#: the sample (SAMPLE_FRACTION of about 113,000 mutants) at the measured 10
#: to 30 s a mutant is 6 to 19 runner hours, so a cycle is a night or two.
JOBS = 7

#: The most jobs a dispatched night may ask for.
MAX_JOBS = 12

#: A job's budget for mutmut, seconds (4.5 h of the 6 h a hosted job may run).
DEFAULT_BUDGET_S = 16200

#: Seconds a job spends before its first mutant, on a runner: generating the
#: bin's mutants, the stats pass over the whole oracle, the clean run of the
#: bin's covering tests and the forced-fail run, each on one core.  Over the
#: fourteen slices of 29 October to 3 November 2026 with a full record, the
#: stats pass took 45 to 130 minutes, the clean run 40 to 70 and the
#: forced-fail run up to 25, so the first mutant came 85 to 200 minutes in;
#: the median, with no test dropped on the way, is about two hours.
FIXED_S = 7200

#: The share of the tree's mutants a cycle measures: each mutant is in the
#: cycle's sample with this probability (``in_sample``), so the sample is a
#: simple random one and the score's interval is a proportion's.  At 2% of
#: about 113,000 mutants the sample is about 2,300, the whole-tree score's
#: 95% interval about ±1.7 points, and a night or two of seven jobs decides
#: it; a module's own interval follows its share.
SAMPLE_FRACTION = 0.02

#: Estimated runner seconds a mutant at four workers, by family: the soundness
#: core's mutants run the verifier's tests under Z3 (0.05 to 0.2 a second on
#: the measuring machine), the rest about one a second.
CORE_RATE_S = 25.0
OTHER_RATE_S = 2.5
CORE = ("vera/verifier.py", "vera/smt.py", "vera/checker/", "vera/obligations/")

#: Seconds the engine's ``count`` of the uncounted units may take: the whole
#: tree took 46 s on the measuring machine, about two minutes on a runner.
COUNT_TIMEOUT_S = 1200

#: Statuses that leave a mutant to a later night: mutmut never ran it, or the
#: run stopped while it ran.
UNDECIDED = frozenset({"not checked", "check was interrupted by user"})

#: Statuses a budget stop can leave on a mutant it cut short (a worker killed
#: is ``segfault``, one ended with an unexpected code ``suspicious``), so they
#: are taken from a run the budget did not stop, and left undecided otherwise.
CUT_SHORT = frozenset({"segfault", "suspicious"})

#: The nights the state keeps a line for.
KEPT_NIGHTS = 120

#: A slice with no record is one whose runner was taken away before it could
#: upload anything (the nights of 19 and 20 October 2026, #1751): a step that
#: fails while the runner is still there writes a lane record instead.  A
#: hosted runner is lost under about 7% of the sweep's 4.5-hour jobs (8 of
#: the first 17 seven-job nights lost one, #1827), so a lost slice is noted
#: and its work waits for the next night; more than LOST_LIMIT_NIGHT in one
#: night is an outage rather than weather, and stops the night short.
LOST_LIMIT_NIGHT = 2

#: Seconds between the heartbeat lines a slice prints while the engine runs:
#: the elapsed time, the runner's available memory, swap and load, and the
#: engine's last status.  A lost runner uploads no record, so what the job
#: printed is all that survives of it, and the log outlives the runner.
HEARTBEAT_S = 300.0

#: Characters of the engine's status a heartbeat line carries.
STATUS_WIDTH = 120

#: The most mutants the state accepts for one function (the largest
#: measured is ``TypeEnv._register_builtins``'s 1,661).
MAX_MUTANTS = 100_000

#: The calibration's range; the stitch clamps to it.
CALIBRATION_RANGE = (0.2, 5.0)

#: The workflow whose runs carry the state, and the state artifact's name.
WORKFLOW = "mutation-nightly.yml"
STATE_ARTIFACT = "mutation-sweep-state"

#: The events whose runs may carry the state: the schedule and a dispatch,
#: both of which run this repository's own ``main``.
STATE_EVENTS = frozenset({"schedule", "workflow_dispatch"})

#: The statuses a state records: every one mutmut prints bar the undecided.
DECIDED = frozenset(md.STATUSES) - UNDECIDED


class StateError(ValueError):
    """The sweep's state, or a slice's record, is not one this script can use."""


# ---------------------------------------------------------------------------
# The inventory
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class SweepUnit:
    """A unit mutmut mutates: where it is, and its code's hash."""

    path: str
    key: str
    start: int
    hash: str

    @property
    def ident(self) -> str:
        return f"{self.path}::{self.key}"

    @property
    def module(self) -> str:
        return md.module_name(self.path)


def _identity(code: str, lines: Sequence[str]) -> str:
    """A unit's identity: its code (``ast``, docstrings set aside), and the
    lines in it that carry a ``pragma: no mutate`` comment, which change
    mutmut's mutants without changing the code."""
    pragmas = [line.strip() for line in lines if "pragma: no mutate" in line]
    return hashlib.sha256("\n".join([code, *pragmas]).encode("utf-8")).hexdigest()[:16]


def units_of(source: str, path: str) -> list[SweepUnit]:
    """The units mutmut mutates in one file, in its order."""
    tree = ast.parse(source)
    lines = source.splitlines()
    scanned = md.scan_units(source, path)
    found: list[SweepUnit] = []
    for node, cls in md._unit_nodes(tree):
        unit = scanned[md._key(node.name, cls)]
        if unit.excluded is not None:
            continue
        found.append(SweepUnit(path=path, key=unit.key, start=unit.start,
                               hash=_identity(unit.code, lines[unit.start - 1:unit.end])))
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


_HEX40 = re.compile(r"[0-9a-f]{40}")
_NUMBER = re.compile(r"[1-9][0-9]{0,8}")
_HEX16 = re.compile(r"[0-9a-f]{16}")
_HEX64 = re.compile(r"[0-9a-f]{64}")
_DATE = re.compile(r"[0-9]{4}-[0-9]{2}-[0-9]{2}")
_VERSION = re.compile(r"[0-9]+(?:\.[0-9]+)*(?:[.+-]?[0-9A-Za-z]+)*")
_PART = r"[A-Za-z_][A-Za-z0-9_]*"
_PATH = re.compile(rf"vera/(?:{_PART}/)*{_PART}\.py")
_KEY = rf"x(?:_{_PART}|{md.SEP}{_PART}{md.SEP}{_PART})"
_IDENT = re.compile(rf"{_PATH.pattern}::{_KEY}")
_SURVIVOR = re.compile(rf"(?:{_PART}\.)*{_PART}\.{_KEY}__mutmut_[1-9][0-9]*:(?:survived|timeout)")
_TESTID = re.compile(r"[^\x00-\x1f]{1,1000}")


def _check(ok: bool, what: str) -> None:
    if not ok:
        raise StateError(what)


def _int(value: Any, low: int, high: int, what: str) -> int:
    _check(type(value) is int and low <= value <= high, f"{what} is not a whole number from {low} to {high}")
    return int(value)


def _text(value: Any, pattern: re.Pattern[str], what: str) -> str:
    _check(isinstance(value, str) and pattern.fullmatch(value) is not None, f"{what} is malformed")
    return str(value)


def _keys(value: Any, keys: set[str], what: str) -> Mapping[str, Any]:
    _check(isinstance(value, dict) and set(value) == keys,
           f"{what} does not have exactly the fields {sorted(keys)}")
    return value  # type: ignore[no-any-return]


def check_unit(ident: Any, record: Any) -> None:
    """One function's record: its ident, its code hash, its count, and its
    decided mutants, each a number within the count and a decided status."""
    _text(ident, _IDENT, f"function {ident!r}")
    rec = _keys(record, {"hash", "mutants", "statuses"}, f"{ident}'s record")
    _text(rec["hash"], _HEX16, f"{ident}'s hash")
    count = rec["mutants"]
    if count is not None:
        _int(count, 0, MAX_MUTANTS, f"{ident}'s mutant count")
    statuses = rec["statuses"]
    _check(isinstance(statuses, dict), f"{ident}'s statuses are not a mapping")
    _check(count is not None or not statuses, f"{ident} has decided mutants and no count")
    for number, status in statuses.items():
        _check(isinstance(number, str) and _NUMBER.fullmatch(number) is not None
               and int(number) <= (count or 0), f"{ident}'s mutant {number!r} is out of range")
        _check(status in DECIDED, f"{ident}'s mutant {number} has a status mutmut does not print")


def _check_night(night: Any) -> None:
    keys = {"date", "head", "jobs", "moved", "slices", "problems", "notes", "closed"}
    # The lost slices entered the line on 2026-10-21 (#1751); the lines the
    # workflow's artifacts hold from before have none, and still load.
    if isinstance(night, dict) and "lost" in night:
        keys.add("lost")
    rec = _keys(night, keys, "a night")
    lost = rec.get("lost", [])
    _check(isinstance(lost, list) and len(lost) == len(set(lost)) <= MAX_JOBS
           and all(type(n) is int and 0 <= n < MAX_JOBS for n in lost), "a night's lost slices")
    _text(rec["date"], _DATE, "a night's date")
    _text(rec["head"], _HEX40, "a night's head")
    _int(rec["jobs"], 1, MAX_JOBS, "a night's jobs")
    _int(rec["moved"], 0, MAX_MUTANTS * 10_000, "a night's progress")
    _check(isinstance(rec["closed"], bool), "a night's close is not a flag")
    for key in ("problems", "notes"):
        _check(isinstance(rec[key], list) and all(isinstance(p, str) for p in rec[key]),
               f"a night's {key} are not text")
    _check(isinstance(rec["slices"], list) and len(rec["slices"]) <= MAX_JOBS, "a night's slices")
    for line in rec["slices"]:
        slice_keys = {"slice", "planned", "decided", "stopped", "engine_s", "dropped_tests",
                      "subprocess_tests"}
        # The source-reading tests entered the line with the sample (#1827).
        if isinstance(line, dict) and "source_tests" in line:
            slice_keys.add("source_tests")
        s = _keys(line, slice_keys, "a night's slice")
        _int(s["slice"], 0, MAX_JOBS - 1, "a night's slice number")
        _int(s["planned"], 0, MAX_MUTANTS, "a night's planned units")
        _int(s["decided"], 0, MAX_MUTANTS * 10_000, "a night's decided mutants")
        _check(s["stopped"] in (None, "budget", "engine", "unmapped", "lane"), "a night's stop")
        _check(s["engine_s"] is None or (type(s["engine_s"]) in (int, float) and 0 <= s["engine_s"] < 1e6),
               "a night's engine time")
        _check(isinstance(s["dropped_tests"], list) and all(
            isinstance(x, str) and _TESTID.fullmatch(x) for x in s["dropped_tests"]), "a night's drops")
        _int(s["subprocess_tests"], 0, 10**6, "a night's skipped tests")
        if "source_tests" in s:
            _int(s["source_tests"], 0, 10**6, "a night's source-reading tests")


def check_state(data: Any) -> dict[str, Any]:
    """``data`` as a sweep state, every field's type and bounds checked: the
    state comes from an artifact, so nothing in it is trusted."""
    state = _keys(data, {"schema", "engine", "cycle", "cycle_started", "calibration", "units",
                         "last_complete", "nights"}, "the state")
    _check(state["schema"] == SCHEMA and type(state["schema"]) is int, f"not a schema {SCHEMA} state")
    if state["engine"] is not None:
        _text(state["engine"], _VERSION, "the engine version")
        _check(len(state["engine"]) <= 40, "the engine version is too long")
    _int(state["cycle"], 1, 10**6, "the cycle")
    _text(state["cycle_started"], _DATE, "the cycle's start")
    calibration = state["calibration"]
    low, high = CALIBRATION_RANGE
    _check(type(calibration) in (int, float) and math.isfinite(calibration) and low <= calibration <= high,
           f"the calibration is not a number from {low} to {high}")
    _check(isinstance(state["units"], dict), "the units are not a mapping")
    for ident, record in state["units"].items():
        check_unit(ident, record)
    last = state["last_complete"]
    if last is not None:
        last_keys = {"cycle", "started", "finished", "head", "engine", "modules", "survivors"}
        # The sample's size entered the record with the sample (#1827); a
        # cycle closed before carries none of the three.
        sample_keys = {"sampled", "population", "fraction"} & (set(last) if isinstance(last, dict) else set())
        rec = _keys(last, last_keys | sample_keys, "the last closed cycle")
        _int(rec["cycle"], 1, 10**6, "the last closed cycle's number")
        if "sampled" in rec:
            _int(rec["sampled"], 0, MAX_MUTANTS * 10_000, "the last closed cycle's sample")
        if "population" in rec:
            _int(rec["population"], 0, MAX_MUTANTS * 10_000, "the last closed cycle's population")
        if "fraction" in rec:
            _check(type(rec["fraction"]) in (int, float) and 0 < rec["fraction"] <= 1,
                   "the last closed cycle's fraction is not a share from 0 to 1")
        _text(rec["started"], _DATE, "the last closed cycle's start")
        _text(rec["finished"], _DATE, "the last closed cycle's end")
        _text(rec["head"], _HEX40, "the last closed cycle's head")
        _text(rec["engine"], _VERSION, "the last closed cycle's engine")
        _check(isinstance(rec["modules"], dict), "the last closed cycle's modules")
        for module, row in rec["modules"].items():
            _text(module, _PATH, f"module {module!r}")
            columns = {"killed", "survived", "timeout", "no_tests", "other"}
            if isinstance(row, dict) and "mutants" in row:
                columns.add("mutants")  # the module's population, with the sample (#1827)
            counts = _keys(row, columns, f"{module}'s counts")
            for column, n in counts.items():
                _int(n, 0, MAX_MUTANTS * 10_000, f"{module}'s {column}")
        _check(isinstance(rec["survivors"], list), "the last closed cycle's survivors")
        for entry in rec["survivors"]:
            _text(entry, _SURVIVOR, f"survivor {entry!r}")
    _check(isinstance(state["nights"], list) and len(state["nights"]) <= KEPT_NIGHTS, "the nights")
    for night in state["nights"]:
        _check_night(night)
    return dict(state)


def check_record(record: Any) -> None:
    """A slice's record, the fields the stitch reads checked as the state's are."""
    _check(isinstance(record, dict), "not a mapping")
    _check(record.get("schema") == SCHEMA, f"not a schema {SCHEMA} record")
    _int(record.get("slice"), 0, MAX_JOBS - 1, "its slice")
    _int(record.get("of"), 1, MAX_JOBS, "its slices")
    if record.get("head") is not None:
        _text(record["head"], _HEX40, "its head")
    _check(record.get("state_in") == "none" or (isinstance(record.get("state_in"), str)
                                                 and _HEX64.fullmatch(record["state_in"]) is not None),
           "its state digest is malformed")
    if record.get("engine") is not None:
        _text(record["engine"], _VERSION, "its engine version")
    _check(record.get("stopped") in (None, "budget", "engine", "unmapped", "lane"), "its stop is unknown")
    error = record.get("engine_error")
    # The stitch and the reports read it beside an engine stop alone, and
    # the lane reads a log's lines as str.splitlines does.
    _check(error is None or (record.get("stopped") == "engine" and isinstance(error, str)
                             and 0 < len(error) <= md.ENGINE_ERROR_CHARS and error.splitlines() == [error]),
           f"its engine error is not one line of at most {md.ENGINE_ERROR_CHARS} characters "
           "beside an engine stop")
    engine_s = record.get("engine_s", 0.0)
    _check(type(engine_s) in (int, float) and 0 <= engine_s < 1e6, "its engine time is out of range")
    _check(isinstance(record.get("planned"), list) and all(isinstance(p, dict) for p in record["planned"]),
           "its plan is not a list of pieces")
    for key in ("dropped_tests", "subprocess_tests", "source_tests", "deselected_tests"):
        _check(isinstance(record.get(key), list) and all(
            isinstance(x, str) and _TESTID.fullmatch(x) for x in record[key]), f"its {key}")
    counts = record.get("counts")
    _check(isinstance(counts, dict), "its counts are not a mapping")
    for ident, n in counts.items():
        _text(ident, _IDENT, f"its counted function {ident!r}")
        _int(n, 0, MAX_MUTANTS, f"its count of {ident}")
    results = record.get("results")
    _check(isinstance(results, dict), "its results are not a mapping")
    for ident, result in results.items():
        check_unit(ident, result)
        _check(result["mutants"] is not None, f"its result for {ident} has no count")


def load_state(path: Path | None, today: str) -> dict[str, Any]:
    """The state in ``path``, checked field by field, or the first cycle's
    when there is none."""
    if path is None or not path.exists():
        return empty_state(today)
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError as exc:
        raise StateError(f"{path} is not JSON: {exc}") from exc
    try:
        return check_state(data)
    except StateError as exc:
        raise StateError(f"{path} is not a sweep state this script wrote: {exc}") from exc


def pick_state_run(runs: Iterable[Mapping[str, Any]], repo_id: int,
                   has_state: Callable[[int], bool]) -> int | None:
    """The run whose state artifact the night carries on from: the newest
    completed run of this workflow, on this repository's ``main``, started by
    the schedule or a dispatch, that has an unexpired state artifact.  Every
    other run is left out: one from a fork (a pull request on a branch named
    ``main``) or another event could upload an artifact of the same name."""
    own = [r for r in runs
           if r.get("event") in STATE_EVENTS and r.get("head_branch") == "main"
           and r.get("status") == "completed"
           and isinstance(r.get("head_repository"), dict) and r["head_repository"].get("id") == repo_id
           and isinstance(r.get("repository"), dict) and r["repository"].get("id") == repo_id
           and r.get("path", "").endswith(f"/{WORKFLOW}")]
    for run in sorted(own, key=lambda r: (str(r.get("created_at")), int(r["id"])), reverse=True):
        if has_state(int(run["id"])):
            return int(run["id"])
    return None


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
              engine: str | None) -> dict[str, Any]:
    """The state with one record for each unit in the tree: a unit whose code
    changed starts afresh, a unit gone is dropped, and a new engine version
    starts every unit afresh."""
    same_engine = engine is None or state.get("engine") in (None, engine)
    records: dict[str, Any] = {}
    for unit in units:
        old = state["units"].get(unit.ident)
        if same_engine and old is not None and old.get("hash") == unit.hash:
            records[unit.ident] = {"hash": unit.hash, "mutants": old.get("mutants"),
                                   "statuses": dict(old.get("statuses", {}))}
        else:
            records[unit.ident] = _fresh(unit)
    return {**state, "engine": engine if engine is not None else state.get("engine"), "units": records}


def undecided(record: Mapping[str, Any]) -> list[int] | None:
    """A unit's undecided mutant numbers; None while its count is unknown."""
    count = record["mutants"]
    if count is None:
        return None
    return [n for n in range(1, count + 1) if str(n) not in record["statuses"]]


# ---------------------------------------------------------------------------
# The counts, and the sample
# ---------------------------------------------------------------------------


def uncounted(state: Mapping[str, Any], units: Iterable[SweepUnit]) -> list[SweepUnit]:
    """The units whose mutant count the state does not hold yet."""
    return [u for u in units if state["units"][u.ident]["mutants"] is None]


def engine_counts(engine: Sequence[str], env: Mapping[str, str], sources: Mapping[str, str],
                  units: Sequence[SweepUnit]) -> dict[str, int]:
    """Each unit's mutant count, by ident, from the engine's ``count``
    command (``scripts/mutate_diff.py``'s: mutmut's own visitor over the
    unit's file at the head), which is what ``mutmut run`` generates for it,
    so the unit's mutants are ``1`` to the count in the copy.  Nothing is
    counted twice: the state keeps a count by the unit's hash."""
    if not units:
        return {}
    keys: dict[str, list[str]] = {}
    for unit in units:
        keys.setdefault(unit.path, []).append(unit.key)
    request = json.dumps({"sources": {path: sources[path] for path in keys}, "units": keys})
    result = md._engine_call(engine, [md.COUNT_ARG], cwd=None, env=env, stdin=request,
                             timeout_s=COUNT_TIMEOUT_S)
    if result is None:
        raise md.LaneError(f"the engine's count did not finish in {COUNT_TIMEOUT_S:g} s")
    if result.returncode != 0:
        raise md.LaneError(f"the engine could not count the units: {result.stderr.strip()[-500:]}")
    try:
        counted = json.loads(result.stdout)
    except json.JSONDecodeError as exc:
        raise md.LaneError(f"the engine's count is not JSON: {exc}") from exc
    counts: dict[str, int] = {}
    for unit in units:
        n = counted.get(unit.path, {}).get(unit.key) if isinstance(counted, dict) else None
        if type(n) is not int or not 0 <= n <= MAX_MUTANTS:
            raise md.LaneError(f"the engine's count of {unit.ident} is missing or out of range: {n!r}")
        counts[unit.ident] = n
    return counts


def apply_counts(state: dict[str, Any], counts: Mapping[str, int]) -> None:
    for ident, n in counts.items():
        state["units"][ident]["mutants"] = n


def in_sample(cycle: int, ident: str, number: int) -> bool:
    """Whether mutant ``number`` of unit ``ident`` is in cycle ``cycle``'s
    sample: a hash of the three falls under ``SAMPLE_FRACTION``.  Every job
    of a night and every night of the cycle so draw the same sample, each
    mutant in it with the same chance, and the next cycle draws another."""
    digest = hashlib.blake2b(f"{cycle}:{ident}:{number}".encode("utf-8"), digest_size=8).digest()
    return int.from_bytes(digest, "big") < SAMPLE_FRACTION * 2**64


def sampled(state: Mapping[str, Any], unit: SweepUnit) -> list[int] | None:
    """The unit's mutant numbers in the cycle's sample; None while its count
    is unknown."""
    count = state["units"][unit.ident]["mutants"]
    if count is None:
        return None
    return [n for n in range(1, count + 1) if in_sample(int(state["cycle"]), unit.ident, n)]


def sampled_undecided(state: Mapping[str, Any], unit: SweepUnit) -> list[int] | None:
    """The unit's sampled mutants not yet decided; None while its count is
    unknown."""
    numbers = sampled(state, unit)
    if numbers is None:
        return None
    statuses = state["units"][unit.ident]["statuses"]
    return [n for n in numbers if str(n) not in statuses]


# ---------------------------------------------------------------------------
# A night's plan
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class Pick:
    """A job's share of one unit: the mutant numbers it runs."""

    unit: SweepUnit
    numbers: tuple[int, ...]


def rate(unit: SweepUnit, calibration: float = 1.0) -> float:
    """Estimated runner seconds a mutant of ``unit``."""
    base = CORE_RATE_S if unit.path.startswith(CORE) else OTHER_RATE_S
    return base * calibration


def plan(state: Mapping[str, Any], units: Sequence[SweepUnit], *, jobs: int,
         budget_s: float) -> list[list[Pick]]:
    """The night's work in ``jobs`` bins of one job's budget each.

    The sample's undecided mutants in the tree's order fill each bin to the
    job's budget less ``FIXED_S``, at ``rate`` a mutant, a unit splitting
    across bins by its mutants' numbers.  A bin's first piece is taken
    whatever its cost, so a bin with work open decides something.  Every
    unit is counted before the plan (:func:`engine_counts`): one that is not
    cannot be sampled, and stops the plan."""
    capacity = max(budget_s - FIXED_S, budget_s / 4)
    calibration = float(state.get("calibration") or 1.0)
    bins: list[list[Pick]] = [[] for _ in range(jobs)]
    current = 0
    room = capacity
    for unit in units:
        if current >= jobs:
            break
        todo = sampled_undecided(state, unit)
        if todo is None:
            raise StateError(f"{unit.ident} has no mutant count, so its sample cannot be planned")
        cost = rate(unit, calibration)
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
    """mutmut's arguments: each picked mutant by name."""
    return [f"{pick.unit.module}.{pick.unit.key}__mutmut_{n}" for pick in picks for n in pick.numbers]


def known_drops(state: Mapping[str, Any], tree: Path) -> list[str]:
    """Every test a kept night dropped from the oracle (it failed inside
    mutmut's copy with no mutant active) whose file ``tree`` still holds.
    The night deselects them from the start: a drop costs a stats pass, the
    pass stopping at the failure with nothing saved and the rerun starting it
    over, and the four tests of 3 November 2026 cost four slices their whole
    budget (#1827)."""
    found = {test for night in state.get("nights", []) for line in night.get("slices", [])
             for test in line.get("dropped_tests", [])}
    return sorted(test for test in found if (tree / test.split("::", 1)[0]).is_file())


# ---------------------------------------------------------------------------
# A night's slice: running the plan's bin
# ---------------------------------------------------------------------------


def slice_results(picks: Sequence[Pick], results: Mapping[str, str], *,
                  cut_short: bool, finished: bool) -> dict[str, Any]:
    """Each picked unit's mutant count and its decided mutants, from a
    listing ``mutmut results`` printed.  A unit's count is the number of its
    mutants mutmut lists (it generates every mutant of a unit it keeps, a
    file at a time).  A unit it lists nothing for has no mutant only when the
    run finished; from a run that stopped short, it has no count yet.  A
    mutant of a unit the bin does not hold means the narrowing went wrong."""
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
        if not statuses and not finished:
            continue
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


def _meminfo_kb(text: str) -> dict[str, int]:
    """``/proc/meminfo``'s fields, in kB."""
    fields: dict[str, int] = {}
    for line in text.splitlines():
        name, _, rest = line.partition(":")
        parts = rest.split()
        if parts and parts[0].isdigit():
            fields[name.strip()] = int(parts[0])
    return fields


def heartbeat_line(elapsed_s: float, status: str | None, meminfo: str | None,
                   loadavg: str | None) -> str:
    """One heartbeat line: the elapsed time as ``+H:MM``, then what the
    platform can say (the texts of ``/proc/meminfo`` and ``/proc/loadavg``)
    and the engine's last status, each part left out where it is absent."""
    minutes = int(elapsed_s) // 60
    parts = [f"heartbeat +{minutes // 60}:{minutes % 60:02d}"]
    mem = _meminfo_kb(meminfo) if meminfo else {}
    if "MemAvailable" in mem and "MemTotal" in mem:
        parts.append(f"mem avail {round(mem['MemAvailable'] / 1024):,} of {round(mem['MemTotal'] / 1024):,} MiB")
    if "SwapTotal" in mem and "SwapFree" in mem:
        parts.append(f"swap used {round((mem['SwapTotal'] - mem['SwapFree']) / 1024):,} of "
                     f"{round(mem['SwapTotal'] / 1024):,} MiB")
    if loadavg and len(loadavg.split()) >= 3:
        parts.append("load " + " ".join(loadavg.split()[:3]))
    if status:
        parts.append(f"engine: {status}")
    return " | ".join(parts)


def _attempt(log: Path) -> int:
    try:
        return int(log.stem.rsplit("-", 1)[-1])
    except ValueError:
        return -1


def engine_status(workdir: Path) -> str | None:
    """The last row of the newest engine log in ``workdir`` (the highest
    attempt), its spinner frame stripped: what mutmut was last doing."""
    logs = sorted(workdir.glob("mutmut-run-*.log"), key=_attempt)
    if not logs:
        return None
    with logs[-1].open("rb") as fh:
        fh.seek(0, io.SEEK_END)
        fh.seek(max(0, fh.tell() - 8192))
        text = fh.read().decode("utf-8", errors="replace")
    rows = [r.strip() for r in re.split(r"[\r\n]+", text) if r.strip()]
    if not rows:
        return None
    return re.sub(r"^[\u2800-\u28ff]\s*", "", rows[-1])[:STATUS_WIDTH] or None


def _proc_text(path: str) -> str | None:
    try:
        return Path(path).read_text(encoding="utf-8")
    except OSError:
        return None


class Heartbeat(threading.Thread):
    """A line to stdout every ``every_s`` seconds until stopped: the job log
    keeps them when the runner is lost, which uploads no record."""

    def __init__(self, every_s: float, workdir: Path) -> None:
        super().__init__(name="sweep-heartbeat", daemon=True)
        self.every_s = every_s
        self.workdir = workdir
        self.started_at = time.monotonic()
        self._stopping = threading.Event()

    def run(self) -> None:
        while not self._stopping.wait(self.every_s):
            print(heartbeat_line(time.monotonic() - self.started_at, engine_status(self.workdir),
                                 _proc_text("/proc/meminfo"), _proc_text("/proc/loadavg")), flush=True)

    def stop(self) -> None:
        self._stopping.set()
        self.join(timeout=max(5.0, self.every_s))


def run_slice(args: argparse.Namespace, *, repo: Path, workdir: Path, engine: list[str],
              today: str) -> dict[str, Any]:
    """Plan the night and run slice ``args.slice``'s bin: its record."""
    started = time.monotonic()
    head = md._git(repo, "rev-parse", "--verify", "HEAD^{commit}").strip()
    env = md._git_env()
    env["PYTHONDONTWRITEBYTECODE"] = "1"
    env["COLUMNS"] = "80"  # the width md.engine_failure reads pytest's rules at
    skips = workdir / "oracle-skips.txt"
    source_skips = workdir / "oracle-source-skips.txt"
    env[md.SKIPS_ENV] = str(skips)
    env[md.SOURCE_SKIPS_ENV] = str(source_skips)
    version = md._engine_version(engine, env)
    if not version:
        raise md.LaneError("the engine did not report its version")
    state_path = Path(args.state) if args.state else None
    sources = vera_sources(repo, head)
    units = inventory(sources)
    state = reconcile(load_state(state_path, today), units, version)
    counts = engine_counts(engine, env, sources, uncounted(state, units))
    apply_counts(state, counts)
    bins = plan(state, units, jobs=args.of, budget_s=args.budget)
    picks = bins[args.slice]
    record: dict[str, Any] = {
        "schema": SCHEMA, "slice": args.slice, "of": args.of, "head": head,
        "state_in": state_digest(state_path), "engine": version, "budget_s": args.budget,
        "date": today, "planned": [{"unit": p.unit.ident, "hash": p.unit.hash, "numbers": list(p.numbers)}
                                   for p in picks],
        "counts": counts, "results": {}, "stopped": None, "engine_exit": None, "engine_error": None,
        "engine_s": 0.0, "dropped_tests": [], "deselected_tests": [], "subprocess_tests": [],
        "source_tests": [], "selection": 0, "engine_tail": [],
    }
    if not picks:
        record["elapsed_s"] = round(time.monotonic() - started, 1)
        return record
    tree = workdir / "tree"
    tree.mkdir()
    md._extract(repo, head, tree)
    deselected = known_drops(state, tree)
    record["deselected_tests"] = deselected
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
    every = float(getattr(args, "heartbeat", HEARTBEAT_S))
    beat = Heartbeat(every, workdir) if every > 0 else None
    if beat is not None:
        beat.start()
    try:
        run, log, dropped = md.run_dropping(
            [*engine, "run", "--max-children", str(args.max_children), *engine_targets(picks)],
            tree=tree, pyproject=pyproject, budget_s=args.budget, workdir=workdir, env=env,
            config_for=lambda dropped: md.rewrite_config(
                config, only_mutate=files, extra_tests=selection, also_copy=also_copy,
                extra_args=[f"--deselect={test}" for test in [*deselected, *dropped]]))
    finally:
        if beat is not None:
            beat.stop()
    record["engine_s"] = round(time.monotonic() - started, 1)
    record["dropped_tests"] = dropped
    record["engine_error"] = run.error
    record["subprocess_tests"] = md.skipped_tests(skips)
    record["source_tests"] = md.skipped_tests(source_skips)
    record["engine_exit"] = run.returncode
    text = log.read_text(encoding="utf-8", errors="replace")
    no_tests = run.returncode == 1 and md.NO_TESTS_SENTENCE in text
    stopped = run.stopped or (None if run.returncode == 0 or no_tests else "engine")
    finished = stopped is None
    listed = md._engine_call(engine, ["results", "--all", "true"], cwd=tree, env=env)
    results: dict[str, str] | None = None
    # A listing that failed is the engine's failure even after a budget stop:
    # without it there is no evidence of any count or status.
    if listed is None or listed.returncode != 0:
        stopped = "engine"
    else:
        try:
            results = md.parse_results(listed.stdout)
        except md.ResultsError as exc:
            stopped = "engine"
            record["engine_tail"] = [str(exc)]
    if results is not None:
        if no_tests:
            results = {name: "no tests" for name in results}
        try:
            record["results"] = slice_results(picks, results, cut_short=run.stopped is not None,
                                              finished=finished)
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
    """What a slice moved on: its decided mutants (a count is bookkeeping,
    not progress)."""
    return decided_count(record)


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


def merge_counts(state: dict[str, Any], record: Mapping[str, Any], problems: list[str]) -> None:
    """Fold one slice's counts into the state: a count for a function the
    state holds uncounted.  Every slice counts with the same engine at the
    same head, so a count that differs from the state's, or one for a
    function the tree does not hold, is a problem."""
    where = f"slice {record.get('slice')}"
    for ident, n in record.get("counts", {}).items():
        rec = state["units"].get(ident)
        if rec is None:
            problems.append(f"{where} counted {ident}, which the tree does not hold")
        elif rec["mutants"] is None:
            rec["mutants"] = n
        elif rec["mutants"] != n:
            problems.append(f"{where} counted {n} mutants of {ident} where the state holds {rec['mutants']}")


def merge(state: dict[str, Any], record: Mapping[str, Any], problems: list[str]) -> int:
    """Fold one slice's results into the state, a function at a time; what
    it moved on: the mutants newly decided.  A function run at code the tree
    does not hold is a problem, and its results are left out; so is one
    mutmut lists more or fewer mutants of than the state counts, since the
    count is mutmut's own visitor's and the sample was drawn over it."""
    added = 0
    where = f"slice {record.get('slice')}"
    for ident, result in record.get("results", {}).items():
        rec = state["units"].get(ident)
        if rec is None or rec["hash"] != result["hash"]:
            problems.append(f"{where} ran {ident} at code the tree does not hold")
            continue
        if rec["mutants"] is None:
            rec["mutants"] = result["mutants"]
        elif rec["mutants"] != result["mutants"]:
            problems.append(f"{where}: mutmut lists {result['mutants']} mutants of {ident} where the state "
                            f"counts {rec['mutants']}")
            continue
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


def sampled_statuses(state: Mapping[str, Any], unit: SweepUnit) -> dict[str, str]:
    """The unit's decided mutants in the cycle's sample, by number.  A unit
    may hold decisions outside the sample too: a state carried over from
    the sweep that measured every mutant, a tree-order prefix rather than a
    draw.  They are kept, since a later cycle's sample may hold them, and
    never scored: the score is the sample's, or its interval means
    nothing."""
    numbers = sampled(state, unit) or []
    statuses = state["units"][unit.ident]["statuses"]
    return {str(n): statuses[str(n)] for n in numbers if str(n) in statuses}


def tally(state: Mapping[str, Any], units: Iterable[SweepUnit]) -> dict[str, dict[str, int]]:
    """Per-module counts of the sample's decided mutants, by summary column,
    and the module's mutants in all (``mutants``: the population its sample
    is of)."""
    modules: dict[str, dict[str, int]] = {}
    for unit in units:
        row = modules.setdefault(unit.path, dict.fromkeys(
            ("killed", "survived", "timeout", "no_tests", "other", "mutants"), 0))
        row["mutants"] += state["units"][unit.ident]["mutants"] or 0
        for status in sampled_statuses(state, unit).values():
            row[_column(status)] += 1
    return modules


def complete(state: Mapping[str, Any], units: Iterable[SweepUnit]) -> bool:
    """Whether every unit's count is known and every sampled mutant decided."""
    return all(sampled_undecided(state, u) == [] for u in units)


def close_cycle(state: dict[str, Any], units: Sequence[SweepUnit], *, head: str,
                today: str) -> bool:
    """Close the cycle when it is complete: its per-module totals, its
    survivors and its sample's size become ``last_complete``, and the next
    cycle starts."""
    if not complete(state, units):
        return False
    survivors = sorted(
        f"{u.module}.{u.key}__mutmut_{n}:{s}" for u in units
        for n, s in sampled_statuses(state, u).items() if s in ("survived", "timeout"))
    state["last_complete"] = {"cycle": state["cycle"], "started": state["cycle_started"],
                              "finished": today, "head": head, "engine": state["engine"],
                              "modules": tally(state, units), "survivors": survivors,
                              "sampled": sum(len(sampled(state, u) or []) for u in units),
                              "population": sum(state["units"][u.ident]["mutants"] or 0 for u in units),
                              "fraction": SAMPLE_FRACTION}
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


def _listed(numbers: Sequence[int]) -> str:
    """``1``, ``1 and 2``, ``1, 2 and 3``."""
    words = [str(n) for n in numbers]
    return words[0] if len(words) == 1 else ", ".join(words[:-1]) + " and " + words[-1]


def stitch(state_in: Mapping[str, Any], digest: str, records: Sequence[Mapping[str, Any]], *,
           jobs: int, head: str, units: Sequence[SweepUnit], today: str,
           ) -> tuple[dict[str, Any], dict[str, Any]]:
    """The night's records folded into the state: the new state and the
    night's line (what each slice did, and what the night failed at)."""
    problems: list[str] = []
    valid: list[Mapping[str, Any]] = []
    seen: set[int] = set()
    reported: set[int] = set()  # every slice a record came from, accepted or not
    engines = {r.get("engine") for r in records if isinstance(r, dict) and r.get("engine") is not None}
    if len(engines) > 1:
        problems.append(f"the slices ran different engines: {sorted(map(str, engines))}")
    for record in records:
        where = f"slice {record.get('slice') if isinstance(record, dict) else '?'}"
        number = record.get("slice") if isinstance(record, dict) else None
        if type(number) is int and 0 <= number < jobs:
            reported.add(number)
        try:
            check_record(record)
        except StateError as exc:
            problems.append(f"{where}: a malformed record: {exc}")
            continue
        # A lane that failed planned nothing and holds no result, so its head
        # (none, when the failure came before it was read) and its state
        # digest are nothing to check: the record says what failed.
        empty_lane = (record.get("stopped") == "lane" and not record.get("planned")
                      and not record.get("results"))
        if record.get("of") != jobs:
            problems.append(f"{where}: not a record of this night's {jobs} slices")
        elif not empty_lane and record.get("head") != head:
            problems.append(f"{where}: ran {record.get('head')}, not {head}")
        elif not empty_lane and record.get("state_in") != digest:
            problems.append(f"{where}: planned from another state")
        elif record["slice"] in seen:
            problems.append(f"{where}: two records")
        else:
            seen.add(record["slice"])
            valid.append(record)
    # A slice with no record at all: its job ended before it uploaded anything
    # (a hosted runner taken away under it, #1751).  A record the night
    # rejected is not that: the slice reported.  A lost slice's work waits for
    # the next night's plan and the night goes on; more than LOST_LIMIT_NIGHT
    # in a night is a hazard the night reports.
    lost = sorted(set(range(jobs)) - reported)
    notes: list[str] = [f"slice {n}: no record; its work waits for the next night" for n in lost]
    if len(lost) > LOST_LIMIT_NIGHT:
        problems.append(f"no record from slices {_listed(lost)}: more than {LOST_LIMIT_NIGHT} in a night")
    # A slice whose lane failed reports no engine; when none reports one,
    # the state keeps its own.
    engine: str | None = next((str(r["engine"]) for r in valid if r.get("engine")), None)
    state = reconcile(state_in, units, engine)
    if engine is not None and state_in.get("engine") not in (None, engine):
        # Every function starts afresh under another engine: the cycle does.
        notes.append(f"mutmut {state_in.get('engine')} gave way to {engine}: every function "
                     "starts afresh, and so does the cycle")
        state["cycle_started"] = today
    for record in valid:
        merge_counts(state, record, problems)
    added = 0
    for record in valid:
        added += merge(state, record, problems)
        if record.get("stopped") not in (None, "budget"):
            # What stopped it: a lane's reason, or the exception the engine's
            # own code raised, when it raised one.
            why = ((record.get("engine_tail") or [None])[0] if record["stopped"] == "lane"
                   else record.get("engine_error") if record["stopped"] == "engine" else None)
            problems.append(f"slice {record['slice']}: stopped by the {record['stopped']}"
                            + (f": {why}" if why else ""))
        elif record.get("stopped") == "budget" and record.get("planned") and decided_count(record) == 0:
            # The passes before the first mutant ran out the whole budget
            # (the four checker slices of 3 November 2026, #1827): a green
            # night must not hide a slice that measured nothing.
            problems.append(f"slice {record['slice']}: its budget ran out before its first mutant")
    if not problems and added == 0 and any(r.get("planned") for r in valid):
        problems.append("the night decided no mutant")
    # A lost slice may have held the night's whole plan, so this is read only
    # from a night every slice reported.
    if not lost and not any(r.get("planned") for r in valid) and not complete(state, units):
        problems.append("the night planned nothing while the cycle is open")
    calibrate(state, valid, {u.ident: u for u in units})
    closed = close_cycle(state, units, head=head, today=today) if not problems else False
    night = {"date": today, "head": head, "jobs": jobs, "moved": added, "lost": lost,
             "slices": [{"slice": r["slice"], "planned": len(r.get("planned", [])),
                         "decided": decided_count(r), "stopped": r.get("stopped"),
                         "engine_s": r.get("engine_s"), "dropped_tests": r.get("dropped_tests", []),
                         "subprocess_tests": len(r.get("subprocess_tests", [])),
                         "source_tests": len(r.get("source_tests", []))}
                        for r in sorted(valid, key=lambda r: r["slice"])],
             "problems": problems, "notes": notes, "closed": closed}
    state["nights"] = [*state.get("nights", []), night][-KEPT_NIGHTS:]
    return state, night


# ---------------------------------------------------------------------------
# The committed summary
# ---------------------------------------------------------------------------


def _pct(caught: int, total: int) -> float:
    return round(caught / total * 100, 1) if total else 0.0


def wilson(caught: int, total: int) -> tuple[float, float]:
    """The 95% Wilson interval of the share ``caught`` is of ``total``, in
    percentage points: what the sample says of the population's score."""
    if not total:
        return (0.0, 0.0)
    z = 1.959964
    p = caught / total
    denominator = 1 + z * z / total
    centre = (p + z * z / (2 * total)) / denominator
    half = z * math.sqrt(p * (1 - p) / total + z * z / (4 * total * total)) / denominator
    return (round(max(0.0, centre - half) * 100, 1), round(min(1.0, centre + half) * 100, 1))


def write_summary(state: Mapping[str, Any], directory: Path) -> float:
    """``mutation-summary.csv``, ``mutation.json`` and ``mutation-survivors.csv``
    from the last closed cycle, the score with its 95% interval.  A module's
    total is its sampled mutants an in-process test reaches with a known
    outcome (killed, survived, timeout): its ``no tests`` mutants are not
    observable in process, and its ``segfault`` and ``suspicious`` ones have
    no outcome to score; ``mutants`` is the module's population, which the
    sample's ``total`` is drawn from."""
    last = state.get("last_complete")
    if not last:
        raise StateError("no cycle has closed yet, so there is no summary to write")
    rows = []
    for module, row in last["modules"].items():
        total = row["killed"] + row["survived"] + row["timeout"]
        if total:
            low, high = wilson(row["killed"] + row["timeout"], total)
            rows.append((module, total, row["killed"], row["survived"], row["timeout"],
                         _pct(row["killed"] + row["timeout"], total), row.get("mutants", 0), low, high))
    if not rows:
        raise StateError("the closed cycle scored no mutant")
    rows.sort(key=lambda r: (-r[3], r[0]))
    total = sum(r[1] for r in rows)
    killed = sum(r[2] for r in rows)
    survived = sum(r[3] for r in rows)
    timeout = sum(r[4] for r in rows)
    score = _pct(killed + timeout, total)
    low, high = wilson(killed + timeout, total)
    population = last.get("population", sum(r[6] for r in rows))
    directory.mkdir(parents=True, exist_ok=True)
    lines = ["module,total,killed,survived,timeout,caught_pct,mutants,ci95_low,ci95_high"]
    lines += [",".join(str(v) for v in r) for r in rows]
    lines.append(f"TOTAL (vera),{total},{killed},{survived},{timeout},{score},{population},{low},{high}")
    (directory / "mutation-summary.csv").write_text("\n".join(lines) + "\n", encoding="utf-8")
    (directory / "mutation.json").write_text(json.dumps({
        "schemaVersion": 1, "label": "mutation", "message": f"{score}% ±{round((high - low) / 2, 1)}",
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
        error = record.get("engine_error") if record["stopped"] == "engine" else None
        out.append(f"Stopped by the {record['stopped']}" + (f": `{error}`." if error else "."))
        out.append("")
    if record.get("dropped_tests"):
        out.append("Dropped from the oracle (each failed inside mutmut's copy with no mutant "
                   "active):")
        out += [f"- `{t}`" for t in record["dropped_tests"]]
        out.append("")
    if record.get("deselected_tests"):
        out.append("Deselected from the oracle from the start, each dropped on an earlier night:")
        out += [f"- `{t}`" for t in record["deselected_tests"]]
        out.append("")
    if record.get("subprocess_tests"):
        out.append(f"{len(record['subprocess_tests'])} test(s) started a Python or `vera` process "
                   "and were no oracle in mutmut's copy (the record lists them).")
        out.append("")
    if record.get("source_tests"):
        out.append(f"{len(record['source_tests'])} test(s) read the compiler's source and were no "
                   "oracle in mutmut's copy (the record lists them).")
        out.append("")
    if record.get("engine_tail"):
        out += ["```", *record["engine_tail"], "```", ""]
    return "\n".join(out)


def render_night(state: Mapping[str, Any], night: Mapping[str, Any],
                 units: Sequence[SweepUnit]) -> str:
    known = [state["units"][u.ident] for u in units]
    population = sum(r["mutants"] or 0 for r in known)
    unknown = sum(1 for r in known if r["mutants"] is None)
    drawn = sum(len(sampled(state, u) or []) for u in units)
    open_ = sum(len(sampled_undecided(state, u) or []) for u in units)
    out = [f"## Mutation sweep: {night['date']}", "",
           f"`{night['head'][:12]}`, {night['jobs']} job(s): {night['moved']} mutant(s) decided tonight.  "
           f"Cycle {state['cycle']} (from {state['cycle_started']}): {drawn - open_} of {drawn} sampled "
           f"mutants decided, the sample {SAMPLE_FRACTION:.1%} of {population}"
           + (f", {unknown} of {len(units)} functions not yet counted" if unknown else "") + ".", ""]
    if night["slices"]:
        out += ["| Slice | Units | Decided | Stopped | Engine s |", "|---:|---:|---:|---|---:|"]
        out += [f"| {s['slice']} | {s['planned']} | {s['decided']} | {s['stopped'] or ''} | "
                f"{s['engine_s'] or 0:.0f} |" for s in night["slices"]]
        out.append("")
    if night.get("lost"):
        out.append(f"Slice(s) {', '.join(map(str, night['lost']))} sent no record (the job ended before it "
                   "uploaded one); their work waits for the next night.")
        out.append("")
    if night["problems"]:
        out.append("**Stopped short:**")
        out += [f"- {p}" for p in night["problems"]]
        out.append("")
    if night.get("notes"):
        out.append("**Noted:**")
        out += [f"- {n}" for n in night["notes"]]
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


def lane_record(slice_: int, of: int, *, head: str | None, state_path: Path | None,
                budget_s: float, why: str) -> dict[str, Any]:
    """The record of a slice whose lane failed: it planned nothing and decided
    nothing, and ``why`` is what the stitch reports."""
    return {"schema": SCHEMA, "slice": slice_, "of": of, "head": head,
            "state_in": state_digest(state_path), "engine": None, "budget_s": budget_s,
            "planned": [], "counts": {}, "results": {}, "stopped": "lane", "engine_tail": [why],
            "dropped_tests": [], "deselected_tests": [], "subprocess_tests": [], "source_tests": []}


def cmd_lane_failed(args: argparse.Namespace) -> int:
    """Write slice ``--slice``'s record as a lane that failed before the sweep
    ran (a step before it failed while the runner was still there), unless
    the sweep wrote one itself: the stitch then reports the slice rather than
    reading its missing record as a runner that was lost."""
    out = Path(args.out).resolve()
    path = out / f"slice-{args.slice}.json"
    if path.exists():
        print(f"{path} exists: the sweep wrote its own record")
        return 0
    out.mkdir(parents=True, exist_ok=True)
    head: str | None
    try:
        head = md._git(Path(args.repo).resolve(), "rev-parse", "--verify", "HEAD^{commit}").strip()
    except (md.LaneError, OSError):  # git itself may be what failed; the record says so with no head
        head = None
    record = lane_record(args.slice, args.of, head=head, state_path=_state_file(args.state),
                         budget_s=args.budget, why=args.why)
    path.write_text(json.dumps(record, indent=1, sort_keys=True, ensure_ascii=False) + "\n",
                    encoding="utf-8")
    report = render_slice(record)
    print(report)
    _write(args.summary, report)
    return 0


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
        record = lane_record(args.slice, args.of, head=None,
                             state_path=Path(args.state) if args.state else None,
                             budget_s=args.budget, why=f"{type(exc).__name__}: {exc}")
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


def _gh(gh: Sequence[str], path: str) -> Any:
    result = subprocess.run([*gh, "api", path], capture_output=True, text=True, encoding="utf-8",
                            env=md._git_env(), check=False, timeout=120)
    if result.returncode != 0:
        raise md.LaneError(f"gh api {path} failed: {result.stderr.strip()}")
    return json.loads(result.stdout)


def cmd_find_state(args: argparse.Namespace) -> int:
    """Print ``run=<id>``: the run whose state artifact the night carries on
    from (``pick_state_run``), or ``run=`` when there is none yet."""
    gh = list(args.gh) if args.gh else ["gh"]
    runs = _gh(gh, f"repos/{args.repo}/actions/workflows/{WORKFLOW}/runs"
                   "?branch=main&status=completed&per_page=100")["workflow_runs"]

    def has_state(run_id: int) -> bool:
        artifacts = _gh(gh, f"repos/{args.repo}/actions/runs/{run_id}/artifacts"
                            f"?name={STATE_ARTIFACT}")["artifacts"]
        return any(a.get("name") == STATE_ARTIFACT and a.get("expired") is False for a in artifacts)

    run = pick_state_run(runs, args.repo_id, has_state)
    if run is None:
        print("warning: no mutation-sweep-state artifact in this workflow's own runs; "
              "the night starts from no state", file=sys.stderr)
    print(f"run={run if run is not None else ''}")
    return 0


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
    last = state["last_complete"]
    sample = (f" of {last['sampled']} sampled from {last['population']} mutants"
              if "sampled" in last and "population" in last else "")
    print(f"cycle {last['cycle']}: {score}% caught{sample}; wrote "
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
    night.add_argument("--heartbeat", type=float, default=HEARTBEAT_S,
                       help=f"seconds between heartbeat lines while the engine runs, 0 for none "
                            f"(default {HEARTBEAT_S:g})")
    night.add_argument("--repo", default=str(ROOT), help="the repository (default: this one)")
    night.add_argument("--workdir", help="an empty or absent directory for the scratch tree")
    night.add_argument("--summary", help="append the Markdown summary here")
    night.add_argument("--engine", nargs="+", help="the mutmut command")
    lane = sub.add_parser("lane-failed", help="record a slice whose lane failed before the sweep ran")
    lane.add_argument("--slice", type=int, default=0, help="this job's slice (default 0)")
    lane.add_argument("--of", type=int, default=1, help="the night's slices (default 1)")
    lane.add_argument("--state", help="the directory holding the last state (none: cycle 1)")
    lane.add_argument("--out", required=True, help="the directory for slice-<n>.json")
    lane.add_argument("--budget", type=float, default=DEFAULT_BUDGET_S, help="the slice's budget, seconds")
    lane.add_argument("--repo", default=str(ROOT), help="the repository (default: this one)")
    lane.add_argument("--why", required=True, help="what failed, for the stitch's report")
    lane.add_argument("--summary", help="append the Markdown summary here")
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
    find = sub.add_parser("find-state", help="print the run whose state the night carries on from")
    find.add_argument("--repo", required=True, help="owner/name")
    find.add_argument("--repo-id", type=int, required=True, help="the repository's numeric id")
    find.add_argument("--gh", nargs="+", help="the gh command (default: gh)")
    matrix = sub.add_parser("matrix", help="print the workflow's matrix outputs")
    matrix.add_argument("--event", required=True, help="the event that started the run")
    matrix.add_argument("--requested", default="", help="the dispatch's jobs input")
    args = parser.parse_args(argv)
    if args.command in ("night", "stitch", "lane-failed") and not 0 <= getattr(args, "slice", 0) < args.of:
        parser.error("--slice must be at least 0 and less than --of")
    commands = {"night": cmd_night, "stitch": cmd_stitch, "summary": cmd_summary,
                "matrix": cmd_matrix, "find-state": cmd_find_state, "lane-failed": cmd_lane_failed}
    return commands[args.command](args)


if __name__ == "__main__":
    raise SystemExit(main())
