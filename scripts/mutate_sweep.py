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
   method of a top-level class), with a hash of its text, the lines it
   spans.  A unit's mutants are counted by mutmut's own visitor, asked
   through the engine's ``count`` command before the plan, in all and by the
   line it places each on (the mutated node's first line, which its
   covered-lines hook reads a node against), the lines numbered from the
   unit's first, so an edit above the unit in its file moves nothing.
2. The state, carried from night to night in the workflow's artifact: each
   unit's hash, its mutants by line, and its sampled window's verdicts once
   decided.  A unit whose text changed (a comment or a docstring included:
   either moves the lines below it) starts afresh, a unit gone from the
   tree is dropped, and a new engine version starts every unit afresh, since
   mutmut makes a function's mutants by its own rules.
3. The sample: a line of a unit is in the cycle's sample when a hash of the
   cycle, the unit and the line falls under ``SAMPLE_FRACTION``, and the
   sample is every mutant on a sampled line, so every job of a night and
   every night of the cycle draws the same sample, each mutant with the same
   chance, and the next cycle draws another.  mutmut generates a kept unit's
   mutants whole, every one into the copy, so a sample of mutants drawn one
   by one would need bins of hundreds of units to fill a job, and those bins
   spent hours generating and compiling the copy (#1829); a sample of lines
   reaches mutmut's generator through the covered-lines hook, and the copy
   holds the sample's mutants alone.
4. The night's plan: the sample's undecided mutants, each unit's window
   (its sampled lines) with the mutants an earlier night left undecided, in
   the tree's order (path, then line) up to the night's capacity, then
   spread over every one of the ``--of`` jobs, the dearest unit first into
   the least loaded bin.  Every job of the night computes the same plan from
   the same state, and job ``--slice`` runs its bin, handing mutmut each
   undecided mutant by its name and no other.
5. The run: PR #1727's machinery (``scripts/mutate_diff.py``) over a scratch
   tree of the head narrowed to the bin's units, the window file naming each
   file's sampled lines exactly, the oracle every test file the lane's rule
   admits (one that reaches the compiler in process, bar the subprocess, Node
   and tooling families), the copy holding the whole tree.  The engine counts
   what it generated against the window, and a unit's mutants are ``1`` to
   its window's count in the order of its lines; a survivor is named by the
   number mutmut gives the mutant in a run over the whole unit (the mutants
   on every earlier line counted in) and the line it sits on.  A test that
   starts a Python or ``vera`` process, or reads the compiler's source, is no
   oracle in the
   copy (``tests/mutation_oracle.py``); one that fails there with no mutant
   active is dropped from the run and reported, and every night after
   deselects it from the start.  An exception the engine's own code raises
   stops the slice instead, dropping no further test, and its record and the
   night's report name the exception and the engine's frame.
6. The stitch merges the night's slice records into the state, a mutant at
   a time: a window partly decided keeps its decided mutants, and becomes a
   decided window when its last mutant is decided.  When every sampled
   mutant is decided the cycle closes: its per-module totals are kept in the
   state and written as ``mutation-summary.csv`` and the README badge's
   ``mutation.json`` (``summary``), the score with its 95% interval, which a
   pull request commits, and the next cycle starts.

A mutant's run is capped at ``MUTANT_CAP_S`` of wall-clock time by the oracle
plugin (``tests/mutation_oracle.py``), which ends it and names it in a file;
the slice records it ``slow``, decided, counted apart, never caught and never
a survivor.  A budget stop is a normal stop.  A slice whose engine or lane
failed, more than LOST_LIMIT_NIGHT slices with no record, and a second night
in a row that decides no mutant exit 2, and the workflow files a tracking
issue; survivors are the measurement, never a failure.  A step that fails
before the sweep runs, while the runner is still there, writes a lane record
(``lane-failed``), reported like any other.  A slice whose record is missing
(its runner was lost before it could upload one) is noted and its work waits
for the next night.

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

#: Schema 3 (#1838): a unit's window decided a mutant at a time (``partial``,
#: until its last mutant is decided), a ``slow`` column, and each survivor a
#: record of its number, line, line text's hash and the tests it ran.  A
#: schema 2 state loads as schema 3 with no window partly decided, and its
#: cycle goes on; a schema 1 state (mutants decided by number) loads with its
#: nights, and every unit and its cycle start afresh.
SCHEMA = 3

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

#: The share of the tree's mutants a cycle measures: each line a unit's
#: mutants sit on is in the cycle's sample with this probability
#: (``in_sample``), with every mutant on it, so each mutant is in the sample
#: with the same chance and the score's interval is close to a proportion's
#: (a line holds a few mutants, so the sample is drawn in small clusters).
#: At 2% of about 113,000 mutants the sample is about 2,300, the whole-tree
#: score's 95% interval about ±2 points, and a night or two of seven jobs
#: decides it; a module's own interval follows its share.
SAMPLE_FRACTION = 0.02

#: The most lines a unit's mutants may sit on, and the furthest line.
MAX_LINES = 100_000

#: Estimated runner seconds a mutant at four workers, by family: the soundness
#: core's mutants run the verifier's tests under Z3 (0.05 to 0.2 a second on
#: the measuring machine), the rest about one a second.
CORE_RATE_S = 25.0
OTHER_RATE_S = 2.5
CORE = ("vera/verifier.py", "vera/smt.py", "vera/checker/", "vera/obligations/")

#: Seconds the engine's ``count`` of the uncounted units may take: the whole
#: tree took 46 s on the measuring machine, about two minutes on a runner.
COUNT_TIMEOUT_S = 1200

#: mutmut's parallel workers a slice runs.  Four workers held four survivors
#: of a front-end bin at once from +2:20 to +4:00 of 41947212953's slice 0,
#: with 469 MiB available and 1,231 MiB of swap, and the runners lost on 7
#: and 10 November 2026 were two such bins (#1838).
WORKERS = 2

#: Wall-clock seconds a mutant's run may take before the oracle plugin ends
#: it as ``slow``: four workers times the top of the p90 band of the cost
#: per decided mutant, 600 s, so a 100 to 125-minute stall is 40 minutes at
#: most.  mutmut's own wall bound, half its CPU limit, ``(est + 1) × 15`` s,
#: still fires first (a caught timeout) for a mutant whose covering tests
#: take under 159 s clean.
MUTANT_CAP_S = 2400

#: The variables naming the cap and the file the plugin names each mutant
#: it ends in (``tests/mutation_oracle.py``).
CAP_ENV = "MUTATION_ORACLE_CAP_S"
SLOW_ENV = "MUTATION_ORACLE_SLOW"

#: The status of a mutant the cap ended: decided, counted apart.
SLOW = "slow"

#: Statuses that leave a mutant to a later night: mutmut never ran it, or the
#: run stopped while it ran.  A mutant the engine marks interrupted is the
#: cap's only when the plugin's file names it; otherwise it waits.
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

#: The calibration's range; the stitch clamps to it.  It stood at 5.0, the
#: old ceiling, from 4 to 10 November 2026, while the tail cost 2.4 to 17
#: minutes of wall time a mutant at four workers (#1838).
CALIBRATION_RANGE = (0.2, 100.0)

#: Seconds between the heartbeat's looks at the engine: what the record's
#: phase times and memory figures are read at.
POLL_S = 10.0

#: The workflow whose runs carry the state, and the state artifact's name.
WORKFLOW = "mutation-nightly.yml"
STATE_ARTIFACT = "mutation-sweep-state"

#: The events whose runs may carry the state: the schedule and a dispatch,
#: both of which run this repository's own ``main``.
STATE_EVENTS = frozenset({"schedule", "workflow_dispatch"})

#: The statuses a state records: every one mutmut prints bar the undecided,
#: and the cap's.
DECIDED = (frozenset(md.STATUSES) - UNDECIDED) | {SLOW}


class StateError(ValueError):
    """The sweep's state, or a slice's record, is not one this script can use."""


# ---------------------------------------------------------------------------
# The inventory
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class SweepUnit:
    """A unit mutmut mutates: where it is (``start``, the first line it
    spans, a decorator's or the ``def``'s), and the hash of its text."""

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


def _identity(lines: Sequence[str]) -> str:
    """A unit's identity: the text of the lines it spans.  Its mutants are
    placed by line and the state numbers its lines from its first, so a
    change inside it, a comment, a docstring or a ``pragma: no mutate``
    included (each moves or changes what a line holds), starts it afresh,
    and an edit above it in the file moves nothing."""
    return hashlib.sha256("\n".join(lines).encode("utf-8")).hexdigest()[:16]


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
                               hash=_identity(lines[unit.start - 1:unit.end])))
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
#: A closed cycle's survivor: ``module.key__mutmut_n@line:status`` (schemas
#: 2 and 3), or without the line (a cycle closed under schema 1); ``slow``
#: since schema 3.
_SURVIVOR = re.compile(
    rf"(?:{_PART}\.)*{_PART}\.{_KEY}__mutmut_[1-9][0-9]*(?:@[1-9][0-9]*)?:(?:survived|timeout|slow)")
#: A schema 2 window's survivor: ``n@line:status``.
_WINDOW_SURVIVOR = re.compile(r"([1-9][0-9]*)@([1-9][0-9]*):(survived|timeout)")
_TESTID = re.compile(r"[^\x00-\x1f]{1,1000}")
_TESTFILE = re.compile(r"tests/[^\x00-\x1f:]{1,300}\.py")
#: The summary's columns of a decided window.
COLUMNS = ("killed", "survived", "timeout", "no_tests", "slow", "other")
#: Schema 2's columns, before ``slow``.
COLUMNS_2 = ("killed", "survived", "timeout", "no_tests", "other")
#: The statuses a window lists its mutants of, with their records.
LISTED = frozenset({"survived", "timeout", SLOW})
#: The most test files a survivor's record names.
MAX_FILES = 10_000


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


def check_lines(lines: Any, count: Any, what: str) -> None:
    """A unit's mutants by line: each line a number, each count at least
    one, and the counts summing to the unit's count."""
    _check(isinstance(lines, dict) and len(lines) <= MAX_LINES, f"{what}'s lines are not a mapping")
    total = 0
    for line, n in lines.items():
        _check(isinstance(line, str) and _NUMBER.fullmatch(line) is not None and int(line) <= MAX_LINES,
               f"{what}'s line {line!r} is out of range")
        total += _int(n, 1, MAX_MUTANTS, f"{what}'s mutants on line {line}")
    _check(count is not None and total == count, f"{what}'s lines do not sum to its count")


def check_survivor(entry: Any, what: str) -> None:
    """A listed mutant of a window: ``n``, the number mutmut gives it over
    the whole unit, ``line``, the unit's line it sits on (from its first),
    the hash of that line's text and the test files mutmut ran it against
    (each none for a survivor a schema 2 state recorded), and its status."""
    rec = _keys(entry, {"n", "line", "text_sha", "status", "files"}, what)
    _int(rec["n"], 1, MAX_MUTANTS, f"{what}'s number")
    _int(rec["line"], 1, MAX_LINES, f"{what}'s line")
    if rec["text_sha"] is not None:
        _text(rec["text_sha"], _HEX16, f"{what}'s line hash")
    _check(rec["status"] in LISTED, f"{what}'s status is not one a window lists")
    files = rec["files"]
    _check(files is None or (isinstance(files, list) and len(files) <= MAX_FILES and all(
        isinstance(f, str) and _TESTFILE.fullmatch(f) for f in files)), f"{what}'s test files")


def _check_survivors(survivors: Any, size: int, what: str) -> None:
    _check(isinstance(survivors, list) and len(survivors) <= size, f"{what}'s survivors")
    for entry in survivors:
        check_survivor(entry, f"{what}'s survivor")
    _check(len({s["n"] for s in survivors}) == len(survivors), f"{what} lists a mutant twice")


def check_window(window: Any, what: str) -> None:
    """A decided window: the summary's columns summing to its size, and its
    survivors and slow mutants, each a record (:func:`check_survivor`)."""
    rec = _keys(window, {*COLUMNS, "mutants", "survivors"}, f"{what}'s window")
    size = _int(rec["mutants"], 0, MAX_MUTANTS, f"{what}'s window size")
    _check(sum(_int(rec[c], 0, MAX_MUTANTS, f"{what}'s {c}") for c in COLUMNS) == size,
           f"{what}'s window columns do not sum to its size")
    _check_survivors(rec["survivors"], size, what)
    _check(len(rec["survivors"]) == rec["survived"] + rec["timeout"] + rec["slow"],
           f"{what}'s survivors are not its survived, timeout and slow mutants")


def _check_decided(decided: Any, size: int, what: str) -> None:
    """Window numbers (``1`` to ``size``) and their decided statuses."""
    _check(isinstance(decided, dict) and len(decided) <= size, f"{what}'s decided mutants")
    for number, status in decided.items():
        _check(isinstance(number, str) and _NUMBER.fullmatch(number) is not None and int(number) <= size,
               f"{what}'s mutant {number!r} is outside its window")
        _check(status in DECIDED, f"{what}'s mutant {number} has no decided status")


def check_partial(partial: Any, size: int, what: str) -> None:
    """A window partly decided: its decided mutants by window number (each
    short of the whole window) and the listed ones' records."""
    rec = _keys(partial, {"decided", "survivors"}, f"{what}'s partial window")
    _check_decided(rec["decided"], size, what)
    _check(len(rec["decided"]) < size, f"{what}'s partial window is whole")
    _check_survivors(rec["survivors"], size, what)
    _check(len(rec["survivors"]) == sum(1 for s in rec["decided"].values() if s in LISTED),
           f"{what}'s partial survivors are not its listed mutants")


def check_unit(ident: Any, record: Any, cycle: int | None = None) -> None:
    """One function's record: its ident, its code hash, its mutants in all
    and by line (both unknown until the engine counted it), its sampled
    window's verdicts once decided, and the mutants of it decided so far
    while it is not."""
    _text(ident, _IDENT, f"function {ident!r}")
    rec = _keys(record, {"hash", "mutants", "lines", "window", "partial"}, f"{ident}'s record")
    _text(rec["hash"], _HEX16, f"{ident}'s hash")
    count = rec["mutants"]
    if count is not None:
        _int(count, 0, MAX_MUTANTS, f"{ident}'s mutant count")
    if rec["lines"] is not None:
        check_lines(rec["lines"], count, ident)
    if rec["window"] is not None:
        _check(rec["lines"] is not None, f"{ident} has a decided window and no lines")
        _check(rec["partial"] is None, f"{ident} has a decided window and a partial one")
        check_window(rec["window"], ident)
    if rec["partial"] is not None:
        _check(rec["lines"] is not None, f"{ident} has a partial window and no lines")
        # The window is the cycle's sampled lines' mutants, which the state's
        # cycle and lines give; without the cycle, the unit's count bounds it.
        size = int(count or 0) if cycle is None else sum(
            int(n) for line, n in rec["lines"].items() if in_sample(cycle, ident, int(line)))
        check_partial(rec["partial"], size, ident)


def _check_night(night: Any) -> None:
    keys = {"date", "head", "jobs", "moved", "slices", "problems", "notes", "closed"}
    # The lost slices entered the line on 2026-10-21 (#1751), the schema
    # that wrote it with schema 3 (#1838); the lines the workflow's
    # artifacts hold from before have neither, and still load.
    for optional in ("lost", "schema"):
        if isinstance(night, dict) and optional in night:
            keys.add(optional)
    rec = _keys(night, keys, "a night")
    lost = rec.get("lost", [])
    _check(isinstance(lost, list) and len(lost) == len(set(lost)) <= MAX_JOBS
           and all(type(n) is int and 0 <= n < MAX_JOBS for n in lost), "a night's lost slices")
    _text(rec["date"], _DATE, "a night's date")
    _text(rec["head"], _HEX40, "a night's head")
    _int(rec["jobs"], 1, MAX_JOBS, "a night's jobs")
    if "schema" in rec:
        _int(rec["schema"], 3, SCHEMA, "the schema a night's line was written under")
    _int(rec["moved"], 0, MAX_MUTANTS * 10_000, "a night's progress")
    _check(isinstance(rec["closed"], bool), "a night's close is not a flag")
    for key in ("problems", "notes"):
        _check(isinstance(rec[key], list) and all(isinstance(p, str) for p in rec[key]),
               f"a night's {key} are not text")
    _check(isinstance(rec["slices"], list) and len(rec["slices"]) <= MAX_JOBS, "a night's slices")
    for line in rec["slices"]:
        slice_keys = {"slice", "planned", "decided", "stopped", "engine_s", "dropped_tests",
                      "subprocess_tests"}
        # The source-reading tests entered the line with the sample (#1827),
        # the slow mutants with schema 3 (#1838).
        for optional in ("source_tests", "slow"):
            if isinstance(line, dict) and optional in line:
                slice_keys.add(optional)
        s = _keys(line, slice_keys, "a night's slice")
        if "slow" in s:
            _int(s["slow"], 0, MAX_MUTANTS * 10_000, "a night's slow mutants")
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
    keys = {"schema", "engine", "cycle", "cycle_started", "calibration", "units", "last_complete", "nights"}
    if isinstance(data, dict) and "converted_from" in data:
        keys.add("converted_from")  # an older state read (convert_state); the stitch notes it
    state = _keys(data, keys, "the state")
    _check(state["schema"] == SCHEMA and type(state["schema"]) is int, f"not a schema {SCHEMA} state")
    if "converted_from" in state:
        _int(state["converted_from"], 1, SCHEMA - 1, "the schema the state was converted from")
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
        check_unit(ident, record, int(state["cycle"]))
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
            columns = set(COLUMNS_2)
            for optional in ("mutants", "slow"):  # the population (#1827), the slow (#1838)
                if isinstance(row, dict) and optional in row:
                    columns.add(optional)
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
    for ident, counted in counts.items():
        _text(ident, _IDENT, f"its counted function {ident!r}")
        rec = _keys(counted, {"mutants", "lines"}, f"its count of {ident}")
        _int(rec["mutants"], 0, MAX_MUTANTS, f"its count of {ident}")
        check_lines(rec["lines"], rec["mutants"], f"its count of {ident}")
    workers = record.get("workers", WORKERS)
    _int(workers, 1, 1024, "its workers")
    results = record.get("results")
    _check(isinstance(results, dict), "its results are not a mapping")
    for ident, result in results.items():
        what = f"its result for {ident}"
        _text(ident, _IDENT, f"its result for {ident!r}")
        rec = _keys(result, {"hash", "window", "lines", "decided", "survivors", "durations", "estimates"}, what)
        _text(rec["hash"], _HEX16, f"{what}: the hash")
        size = _int(rec["window"], 0, MAX_MUTANTS, f"{what}: the window")
        _check(isinstance(rec["lines"], list) and all(type(n) is int and 1 <= n <= MAX_LINES for n in rec["lines"])
               and rec["lines"] == sorted(set(rec["lines"])), f"{what}: the lines")
        _check_decided(rec["decided"], size, what)
        _check_survivors(rec["survivors"], size, what)
        _check(len(rec["survivors"]) == sum(1 for s in rec["decided"].values() if s in LISTED),
               f"{what}: the survivors are not its listed mutants")
        for key in ("durations", "estimates"):
            seconds = rec[key]
            _check(isinstance(seconds, dict) and set(seconds) <= set(rec["decided"]) and all(
                type(s) in (int, float) and math.isfinite(s) and 0 <= s < 1e6 for s in seconds.values()),
                f"{what}: its {key}")


def _convert_1(data: dict[str, Any], today: str) -> Any:
    """A schema 1 state (the sweep that decided mutants by number, to
    4 November 2026) as a schema 2 state: the engine, the calibration and
    the nights (the drop memory) carry over, and the cycle starts afresh,
    since the sample is now drawn by line.  Each unit keeps its hash and its
    count, its lines unknown and its window undecided, and the reconcile
    starts every one afresh all the same: a schema 1 hash is of the unit's
    ``ast``, a schema 2 hash of its text."""
    units = {}
    for ident, rec in data["units"].items():
        if not isinstance(rec, dict):
            return data
        units[ident] = {"hash": rec.get("hash"), "mutants": rec.get("mutants"), "lines": None, "window": None}
    cycle = data.get("cycle")
    return {"schema": 2, "engine": data.get("engine"),
            "cycle": cycle + 1 if type(cycle) is int else cycle, "cycle_started": today,
            "calibration": data.get("calibration"), "units": units,
            "last_complete": data.get("last_complete"), "nights": data.get("nights"), "converted_from": 1}


def _survivor_2(entry: Any) -> Any:
    """A schema 2 window's survivor, ``n@line:status``, as a record: what
    schema 2 did not keep (the line's text, the tests) is none."""
    match = _WINDOW_SURVIVOR.fullmatch(entry) if isinstance(entry, str) else None
    if match is None:
        return entry  # left to check_state
    return {"n": int(match.group(1)), "line": int(match.group(2)), "text_sha": None,
            "status": match.group(3), "files": None}


def _convert_2(data: dict[str, Any]) -> Any:
    """A schema 2 state as a schema 3 one: no window partly decided, every
    decided window with no slow mutant and its survivors as records, and
    everything else as it was, so the cycle goes on where it stood."""
    units = {}
    for ident, rec in data["units"].items():
        if not isinstance(rec, dict):
            return data
        window = rec.get("window")
        if isinstance(window, dict):
            survivors = window.get("survivors")
            window = {**window, "slow": 0,
                      "survivors": [_survivor_2(s) for s in survivors] if isinstance(survivors, list)
                      else survivors}
        units[ident] = {**rec, "window": window, "partial": None}
    return {**data, "schema": SCHEMA, "units": units, "converted_from": data.get("converted_from", 2)}


def convert_state(data: Any, today: str) -> Any:
    """An older state as a schema 3 one: schema 1 through schema 2
    (:func:`_convert_1`, :func:`_convert_2`), ``converted_from`` naming the
    schema it was.  Anything else is left to :func:`check_state`."""
    if not isinstance(data, dict) or not isinstance(data.get("units"), dict):
        return data
    if data.get("schema") == 1:
        data = _convert_1(data, today)
    if isinstance(data, dict) and data.get("schema") == 2 and isinstance(data.get("units"), dict):
        data = _convert_2(data)
    return data


def load_state(path: Path | None, today: str) -> dict[str, Any]:
    """The state in ``path``, checked field by field, or the first cycle's
    when there is none; an older state converted (:func:`convert_state`)."""
    if path is None or not path.exists():
        return empty_state(today)
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError as exc:
        raise StateError(f"{path} is not JSON: {exc}") from exc
    try:
        return check_state(convert_state(data, today))
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
    return {"hash": unit.hash, "mutants": None, "lines": None, "window": None, "partial": None}


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
                                   "lines": None if old.get("lines") is None else dict(old["lines"]),
                                   "window": None if old.get("window") is None else dict(old["window"]),
                                   "partial": None if old.get("partial") is None else {
                                       "decided": dict(old["partial"]["decided"]),
                                       "survivors": list(old["partial"]["survivors"])}}
        else:
            records[unit.ident] = _fresh(unit)
    return {**state, "engine": engine if engine is not None else state.get("engine"), "units": records}


# ---------------------------------------------------------------------------
# The counts, and the sample
# ---------------------------------------------------------------------------


def uncounted(state: Mapping[str, Any], units: Iterable[SweepUnit]) -> list[SweepUnit]:
    """The units whose mutants by line the state does not hold yet."""
    return [u for u in units if state["units"][u.ident]["lines"] is None]


def engine_counts(engine: Sequence[str], env: Mapping[str, str], sources: Mapping[str, str],
                  units: Sequence[SweepUnit]) -> dict[str, dict[str, Any]]:
    """Each unit's mutants, by ident, from the engine's ``count`` command
    (``scripts/mutate_diff.py``'s: mutmut's own visitor over the unit's file
    at the head): ``{"mutants": n, "lines": {line: k}}``, the lines being the
    ones mutmut places the mutants on, which its covered-lines hook reads a
    node against, so a window of some lines generates exactly their mutants.
    The engine names the file's lines; the state numbers a unit's from its
    first (``1`` is ``unit.start``), so an edit above the unit moves nothing.
    Nothing is counted twice: the state keeps a count by the unit's hash."""
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
    counts: dict[str, dict[str, Any]] = {}
    for unit in units:
        found = counted.get(unit.path, {}).get(unit.key) if isinstance(counted, dict) else None
        try:
            rec = _keys(found, {"mutants", "lines"}, unit.ident)
            _int(rec["mutants"], 0, MAX_MUTANTS, unit.ident)
            check_lines(rec["lines"], rec["mutants"], unit.ident)
        except StateError as exc:
            raise md.LaneError(f"the engine's count of {unit.ident} is missing or malformed: {exc}") from exc
        numbered: dict[str, int] = {}
        for line, n in rec["lines"].items():
            if int(line) < unit.start:
                raise md.LaneError(f"the engine placed a mutant of {unit.ident} on line {line}, above its "
                                   f"first line {unit.start}")
            numbered[str(int(line) - unit.start + 1)] = int(n)
        counts[unit.ident] = {"mutants": rec["mutants"], "lines": numbered}
    return counts


def apply_counts(state: dict[str, Any], counts: Mapping[str, Mapping[str, Any]]) -> None:
    for ident, counted in counts.items():
        state["units"][ident]["mutants"] = counted["mutants"]
        state["units"][ident]["lines"] = dict(counted["lines"])


def in_sample(cycle: int, ident: str, line: int) -> bool:
    """Whether line ``line`` of unit ``ident`` (its lines numbered from its
    first), and so every mutant on it, is in cycle ``cycle``'s sample: a
    hash of the three falls under ``SAMPLE_FRACTION``.  Every job of a night and every night of the cycle
    so draw the same sample, each mutant in it with the same chance, and
    the next cycle draws another."""
    digest = hashlib.blake2b(f"{cycle}:{ident}:{line}".encode("utf-8"), digest_size=8).digest()
    return int.from_bytes(digest, "big") < SAMPLE_FRACTION * 2**64


def sampled_lines(state: Mapping[str, Any], unit: SweepUnit) -> list[int] | None:
    """The unit's lines in the cycle's sample, in order; None while its
    mutants by line are unknown."""
    lines = state["units"][unit.ident]["lines"]
    if lines is None:
        return None
    return sorted(int(line) for line in lines if in_sample(int(state["cycle"]), unit.ident, int(line)))


def window_counts(state: Mapping[str, Any], unit: SweepUnit,
                  ) -> tuple[tuple[int, ...], tuple[int, ...], tuple[int, ...]]:
    """The unit's sampled window: its lines, the mutants on each, and for
    each the unit's mutants on every earlier line, sampled or not (what
    :meth:`Pick.full_number` adds to a window's number)."""
    lines = sampled_lines(state, unit) or []
    counts = state["units"][unit.ident]["lines"] or {}
    before: dict[int, int] = {}
    seen = 0
    for line in sorted(int(n) for n in counts):
        before[line] = seen
        seen += int(counts[str(line)])
    return tuple(lines), tuple(int(counts[str(line)]) for line in lines), tuple(before[line] for line in lines)


def undecided_numbers(state: Mapping[str, Any], unit: SweepUnit) -> tuple[int, ...] | None:
    """The window numbers (``1`` to its size, the numbers mutmut gives the
    window's mutants in a windowed run) of the unit's sampled mutants still
    to decide; None while its lines are unknown.  A cycle's window of a unit
    is fixed (its sampled lines and their mutants, at its hash), so a number
    names the same mutant on every night of the cycle."""
    rec = state["units"][unit.ident]
    if rec["lines"] is None:
        return None
    if rec["window"] is not None:
        return ()
    decided = (rec.get("partial") or {}).get("decided", {})
    return tuple(n for n in range(1, sum(window_counts(state, unit)[1]) + 1) if str(n) not in decided)


def sampled_undecided(state: Mapping[str, Any], unit: SweepUnit) -> int | None:
    """How many of the unit's sampled mutants are still to decide: none once
    its window is decided; None while its lines are unknown."""
    todo = undecided_numbers(state, unit)
    return None if todo is None else len(todo)




# ---------------------------------------------------------------------------
# A night's plan
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class Pick:
    """A job's piece of work: one unit's sampled window, its lines, the
    mutants on each and the unit's mutants before each, and the window
    numbers still to decide (``todo``; none given: every one)."""

    unit: SweepUnit
    lines: tuple[int, ...]
    counts: tuple[int, ...]
    before: tuple[int, ...]
    todo: tuple[int, ...] | None = None

    @property
    def mutants(self) -> int:
        """The window's size: what mutmut generates for the unit."""
        return sum(self.counts)

    @property
    def numbers(self) -> tuple[int, ...]:
        """The window numbers the engine is handed."""
        return tuple(range(1, self.mutants + 1)) if self.todo is None else self.todo

    def _locate(self, number: int) -> tuple[int, int]:
        """Which of the window's lines mutant ``number`` sits on, and which
        of that line's mutants it is: mutmut numbers the mutants it
        generates from one in the order of their lines (the visitor records
        a node's mutations on visiting it, before its children's)."""
        seen = 0
        for index, count in enumerate(self.counts):
            if number <= seen + count:
                return index, number - seen
            seen += count
        raise StateError(f"{self.unit.ident}: mutant {number} is past its window of {seen}")

    def line_of(self, number: int) -> int:
        """The line mutant ``number`` of the window sits on."""
        return self.lines[self._locate(number)[0]]

    def full_number(self, number: int) -> int:
        """The number mutmut gives mutant ``number`` of the window in a run
        over the whole unit: the unit's mutants on every earlier line, then
        its place on its own line, whose mutants the window holds whole."""
        index, place = self._locate(number)
        return self.before[index] + place


def rate(unit: SweepUnit, calibration: float = 1.0) -> float:
    """Estimated runner seconds a mutant of ``unit``."""
    base = CORE_RATE_S if unit.path.startswith(CORE) else OTHER_RATE_S
    return base * calibration


def plan(state: Mapping[str, Any], units: Sequence[SweepUnit], *, jobs: int,
         budget_s: float) -> list[list[Pick]]:
    """The night's work in ``jobs`` bins.

    The units with sampled mutants undecided are taken in the tree's order
    while their estimated cost (their undecided mutants at ``rate``) fits the
    night, ``jobs`` times a job's budget less ``FIXED_S``; the first is taken
    whatever it costs.  The night's units are then spread over every job,
    each unit whole, the dearest first into the bin holding least (the lower
    bin on a tie), so every job has work while the units outnumber them and
    the bins' estimated costs are close; each bin keeps the tree's order.
    One rate per family cannot describe a bin whose undecided mutants are
    the dearest of their units (mutmut runs a bin's cheapest first), so a
    bin can still be over-planned; the record of each mutant as it is
    decided is what makes that harmless, since the next night plans what is
    left.  Every unit is counted before the plan (:func:`engine_counts`):
    one that is not cannot be sampled, and stops the plan."""
    capacity = max(budget_s - FIXED_S, budget_s / 4)
    calibration = float(state.get("calibration") or 1.0)
    taken: list[tuple[Pick, float]] = []
    total = 0.0
    for unit in units:
        todo = undecided_numbers(state, unit)
        if todo is None:
            raise StateError(f"{unit.ident} has no mutants by line, so its sample cannot be planned")
        if not todo:
            continue
        cost = len(todo) * rate(unit, calibration)
        if taken and total + cost > jobs * capacity:
            break
        lines, counts, before = window_counts(state, unit)
        taken.append((Pick(unit=unit, lines=lines, counts=counts, before=before, todo=todo), cost))
        total += cost
    bins: list[list[int]] = [[] for _ in range(jobs)]
    loads = [0.0] * jobs
    for index in sorted(range(len(taken)), key=lambda i: (-taken[i][1], i)):
        target = min(range(jobs), key=lambda j: (loads[j], j))
        bins[target].append(index)
        loads[target] += taken[index][1]
    return [[taken[i][0] for i in sorted(b)] for b in bins]


def mutant_name(pick: Pick, number: int) -> str:
    """The name mutmut gives mutant ``number`` of the pick's window in a
    windowed run: the window's mutants are numbered from one in the order of
    their lines (:func:`scripts.mutate_diff.count_units`)."""
    return f"{pick.unit.module}.{pick.unit.key}__mutmut_{number}"


def engine_targets(picks: Sequence[Pick]) -> list[str]:
    """mutmut's arguments: each undecided mutant of each pick by its name.
    mutmut runs exactly the mutants a run names, and reads its clean run's
    tests off the names (``tests_for_mutant_names``): a name adds its
    function's covering tests, where a glob such as ``key__mutmut_*`` names
    no function, adds none, and leaves the clean run to the whole selection
    (#1838)."""
    return [mutant_name(pick, n) for pick in picks for n in pick.numbers]


def window_lines(picks: Sequence[Pick]) -> dict[str, list[int]]:
    """The window file's lines: each file's sampled lines, over its picked
    units, as the file numbers them (a pick's are the unit's, from its
    first)."""
    lines: dict[str, set[int]] = {}
    for pick in picks:
        lines.setdefault(pick.unit.path, set()).update(pick.unit.start + line - 1 for line in pick.lines)
    return {path: sorted(found) for path, found in sorted(lines.items())}


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


def line_hash(text: str) -> str:
    """A line's identity in a survivor's record: the hash of its text."""
    return hashlib.sha256(text.encode("utf-8")).hexdigest()[:16]


def slice_results(picks: Sequence[Pick], results: Mapping[str, str],
                  generated: Mapping[tuple[str, str], tuple[int, int]], *,
                  cut_short: bool, finished: bool, slow: Iterable[str] = (),
                  line_text: Callable[[SweepUnit, int], str | None] | None = None,
                  files: Mapping[str, list[str]] | None = None,
                  seconds: Mapping[str, tuple[float | None, float | None]] | None = None,
                  ) -> dict[str, Any]:
    """The mutants of each picked window the run decided, from a listing
    ``mutmut results`` printed and the engine's count of what it generated
    against the window (``scripts/mutate_diff.py``'s window record), each
    by its window number: of the numbers the night handed the engine, every
    one listed with a decided status the budget did not cut short.  A
    mutant the engine left undecided that ``slow`` names (the oracle
    plugin's file) is ``slow``; one the engine marks interrupted that the
    file does not name waits for another night, and a verdict the engine
    completed stands whether the file names the mutant or not.  A survivor,
    a timeout and a slow mutant are each listed with the hash of their line's text (``line_text``, the
    unit's line from its first), the test files mutmut ran them against
    (``files``, by unit), and each decided mutant with its duration and
    mutmut's estimate (``seconds``, by name).  The engine generating more or
    fewer mutants of a unit than its window holds, a mutant of a unit the
    bin does not hold, or a numbering with gaps means the narrowing, the
    window or the counts went wrong."""
    slow = set(slow)
    seconds = seconds or {}
    owners = {(p.unit.module, p.unit.key): p for p in picks}
    listed: dict[str, dict[int, str]] = {p.unit.ident: {} for p in picks}
    for name, status in results.items():
        pick = owners.get(md.unit_of_mutant(name))
        if pick is None:
            raise StateError(f"a result for a function the night did not plan: {name}")
        listed[pick.unit.ident][md._mutant_number(name)] = status
    out: dict[str, Any] = {}
    for pick in picks:
        held, inside = generated.get((pick.unit.path, pick.unit.key), (None, None))
        statuses = listed[pick.unit.ident]
        if inside is None:
            if statuses or finished:
                raise StateError(f"the engine did not count {pick.unit.ident}'s window")
            continue
        if inside != pick.mutants:
            raise StateError(f"the engine generated {inside} mutants of {pick.unit.ident} where its "
                             f"window holds {pick.mutants}")
        entry: dict[str, Any] = {"hash": pick.unit.hash, "window": inside, "lines": list(pick.lines),
                                 "decided": {}, "survivors": [], "durations": {}, "estimates": {}}
        if not statuses:
            if finished and inside:
                raise StateError(f"mutmut listed nothing for {pick.unit.ident}'s {inside} mutants")
            if not inside:
                out[pick.unit.ident] = entry  # nothing to decide: decided
            continue
        if sorted(statuses) != list(range(1, inside + 1)):
            raise StateError(f"mutmut listed {len(statuses)} mutants of {pick.unit.ident} where the window "
                             f"holds {inside}, or numbered them with gaps")
        for number in pick.numbers:
            name = mutant_name(pick, number)
            # The cap's timer cannot be cancelled once its wait has returned,
            # so a run can finish with its own verdict after the plugin named
            # it: the file decides only a mutant the engine left undecided.
            status = SLOW if name in slow and statuses[number] in UNDECIDED else statuses[number]
            if status in UNDECIDED or (cut_short and status in CUT_SHORT):
                continue  # the mutant waits for another night
            entry["decided"][str(number)] = status
            duration, estimate = seconds.get(name, (None, None))
            if duration is not None:
                entry["durations"][str(number)] = round(float(duration), 3)
            if estimate is not None:
                entry["estimates"][str(number)] = round(float(estimate), 3)
            if status in LISTED:
                line = pick.line_of(number)
                text = line_text(pick.unit, line) if line_text is not None else None
                ran = (files or {}).get(pick.unit.ident)
                entry["survivors"].append({"n": pick.full_number(number), "line": line,
                                           "text_sha": None if text is None else line_hash(text),
                                           "status": status, "files": None if ran is None else list(ran)})
        if entry["decided"]:
            out[pick.unit.ident] = entry
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


#: The engine's phases, by the spinner title its log shows while in each,
#: and the key the record's ``phases`` holds each one's start under.
PHASES = (("Running stats", "stats_s"), ("Running clean tests", "clean_s"),
          ("Running forced fail test", "forced_s"), ("Running mutation testing", "mutants_s"))

#: mutmut's progress line: mutants decided (bar the not checked) of all.
_PROGRESS = re.compile(r"^(\d+)/(\d+)\s")


class Watch:
    """What the heartbeat saw of a slice, for its record: when each of the
    engine's phases started and its first mutant was decided, seconds from
    the slice's start; the engine's last status and its count of decided
    mutants at it; and the runner's lowest available memory and highest
    swap in use, MiB."""

    def __init__(self) -> None:
        self.phases: dict[str, float | None] = {key: None for _, key in PHASES}
        self.phases["first_mutant_s"] = None
        self.status: str | None = None
        self.engine_decided: int | None = None
        self.mem_floor_mib: int | None = None
        self.swap_peak_mib: int | None = None

    def observe(self, elapsed_s: float, status: str | None, meminfo: str | None) -> None:
        at = round(elapsed_s, 1)
        if status:
            self.status = status
            for title, key in PHASES:
                if status.startswith(title) and self.phases[key] is None:
                    self.phases[key] = at
            progress = _PROGRESS.match(status)
            if progress is not None:
                if self.phases["mutants_s"] is None:
                    self.phases["mutants_s"] = at
                self.engine_decided = int(progress.group(1))
                if self.engine_decided > 0 and self.phases["first_mutant_s"] is None:
                    self.phases["first_mutant_s"] = at
        mem = _meminfo_kb(meminfo) if meminfo else {}
        if "MemAvailable" in mem:
            avail = round(mem["MemAvailable"] / 1024)
            self.mem_floor_mib = avail if self.mem_floor_mib is None else min(self.mem_floor_mib, avail)
        if "SwapTotal" in mem and "SwapFree" in mem:
            used = round((mem["SwapTotal"] - mem["SwapFree"]) / 1024)
            self.swap_peak_mib = used if self.swap_peak_mib is None else max(self.swap_peak_mib, used)

    def fields(self) -> dict[str, Any]:
        return {"phases": dict(self.phases), "engine_status": self.status,
                "engine_decided": self.engine_decided, "mem_floor_mib": self.mem_floor_mib,
                "swap_peak_mib": self.swap_peak_mib}


class Heartbeat(threading.Thread):
    """A line to stdout every ``every_s`` seconds until stopped: the job log
    keeps them when the runner is lost, which uploads no record.  Between
    lines it looks at the engine every ``POLL_S`` seconds (``watch``)."""

    def __init__(self, every_s: float, workdir: Path, watch: Watch | None = None,
                 started_at: float | None = None) -> None:
        super().__init__(name="sweep-heartbeat", daemon=True)
        self.every_s = every_s
        self.workdir = workdir
        self.watch = watch if watch is not None else Watch()
        self.started_at = time.monotonic() if started_at is None else started_at
        self._stopping = threading.Event()

    def run(self) -> None:
        poll = min(self.every_s, POLL_S)
        printed = time.monotonic()
        while not self._stopping.wait(poll):
            now = time.monotonic()
            status, meminfo = engine_status(self.workdir), _proc_text("/proc/meminfo")
            self.watch.observe(now - self.started_at, status, meminfo)
            if now - printed >= self.every_s - 1e-3:
                printed = now
                print(heartbeat_line(now - self.started_at, status, meminfo, _proc_text("/proc/loadavg")),
                      flush=True)

    def stop(self) -> None:
        self._stopping.set()
        self.join(timeout=max(5.0, self.every_s))


def slow_mutants(path: Path) -> set[str]:
    """The mutants the oracle plugin ended at the cap: the first field of
    each line of its file (``name<TAB>seconds``)."""
    if not path.exists():
        return set()
    return {line.split("\t", 1)[0].strip() for line in path.read_text(encoding="utf-8").splitlines()
            if line.strip()}


def tested_files(stats: Path) -> dict[str, list[str]]:
    """The test files mutmut's stats pass recorded reaching each function,
    by its mangled name (``mutants/mutmut-stats.json``): what each of its
    mutants ran against.  None recorded, or no stats file: none."""
    try:
        data = json.loads(stats.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return {}
    by_name = data.get("tests_by_mangled_function_name") if isinstance(data, dict) else None
    if not isinstance(by_name, dict):
        return {}
    return {str(name): sorted({str(t).removeprefix("mutants/").split("::", 1)[0] for t in tests
                               if _TESTFILE.fullmatch(str(t).removeprefix("mutants/").split("::", 1)[0])})
            for name, tests in by_name.items() if isinstance(tests, list)}


def mutant_seconds(tree: Path, paths: Iterable[str]) -> dict[str, tuple[float | None, float | None]]:
    """Each mutant's duration and mutmut's estimate of it (the clean time of
    its covering tests), by name, from mutmut's meta file for each path,
    which it writes at every result, so a budget stop keeps them."""
    out: dict[str, tuple[float | None, float | None]] = {}
    for path in paths:
        try:
            meta = json.loads((tree / "mutants" / f"{path}.meta").read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError):
            continue
        durations = meta.get("durations_by_key") or {}
        estimates = meta.get("estimated_durations_by_key") or {}
        for name in set(durations) | set(estimates):
            d, e = durations.get(name), estimates.get(name)
            out[str(name)] = (float(d) if isinstance(d, (int, float)) else None,
                              float(e) if isinstance(e, (int, float)) else None)
    return out


def run_slice(args: argparse.Namespace, *, repo: Path, workdir: Path, engine: list[str],
              today: str) -> dict[str, Any]:
    """Plan the night and run slice ``args.slice``'s bin: its record."""
    started = time.monotonic()
    head = md._git(repo, "rev-parse", "--verify", "HEAD^{commit}").strip()
    env = md._git_env()
    # The copy caches bytecode (scripts/mutate_diff.py says why, #1829).
    env.pop("PYTHONDONTWRITEBYTECODE", None)
    env["COLUMNS"] = "80"  # the width md.engine_failure reads pytest's rules at
    skips = workdir / "oracle-skips.txt"
    source_skips = workdir / "oracle-source-skips.txt"
    env[md.SKIPS_ENV] = str(skips)
    env[md.SOURCE_SKIPS_ENV] = str(source_skips)
    env[md.FAILURES_ENV] = str(workdir / "oracle-failures.txt")
    # The cap on each mutant's run (tests/mutation_oracle.py), and the file
    # the plugin names each mutant it ends in.
    slow_file = workdir / "oracle-slow.txt"
    env[CAP_ENV] = f"{float(getattr(args, 'mutant_cap', MUTANT_CAP_S)):g}"
    env[SLOW_ENV] = str(slow_file)
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
        "date": today, "planned": [{"unit": p.unit.ident, "hash": p.unit.hash, "lines": list(p.lines),
                                    "mutants": p.mutants, "todo": list(p.numbers)} for p in picks],
        "counts": counts, "results": {}, "stopped": None, "engine_exit": None, "engine_error": None,
        "engine_s": 0.0, "dropped_tests": [], "deselected_tests": [], "subprocess_tests": [],
        "source_tests": [], "selection": 0, "engine_tail": [], "workers": int(args.max_children),
        "slow": [], **Watch().fields(),
    }
    if not picks:
        record["elapsed_s"] = round(time.monotonic() - started, 1)
        return record
    tree = workdir / "tree"
    tree.mkdir()
    md._extract(repo, head, tree)
    deselected = known_drops(state, tree)
    record["deselected_tests"] = deselected
    # The window: each file's sampled lines, exactly, which the engine makes
    # mutmut generate alone (scripts/mutate_diff.py's install_window) and
    # counts per unit for the check against each pick.
    counts_file = workdir / "window-counts.json"
    window_file = workdir / "window.json"
    window_file.write_text(json.dumps({"context": 0, "record": str(counts_file), "exact": True,
                                       "lines": window_lines(picks)}, indent=1) + "\n", encoding="utf-8")
    env[md.WINDOW_ENV] = str(window_file)
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
    watch = Watch()
    beat = Heartbeat(every, workdir, watch, started) if every > 0 else None
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
    watch.observe(time.monotonic() - started, engine_status(workdir), _proc_text("/proc/meminfo"))
    record.update(watch.fields())
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
    generated = md.read_window_counts(counts_file)
    if generated is None and results is not None:
        # Nothing says the engine generated the window's mutants alone.
        stopped = "engine"
        record["engine_tail"] = ["the engine wrote no count of what it generated against the window"]
    elif results is not None and generated is not None:
        if no_tests:
            results = {name: "no tests" for name in results}
        slow = slow_mutants(slow_file)
        record["slow"] = sorted(slow)
        ran = tested_files(tree / "mutants" / "mutmut-stats.json")

        def line_text(unit: SweepUnit, line: int) -> str | None:
            rows = sources[unit.path].splitlines()
            at = unit.start + line - 1
            return rows[at - 1] if 1 <= at <= len(rows) else None

        try:
            record["results"] = slice_results(
                picks, results, generated, cut_short=run.stopped is not None, finished=finished,
                slow=slow, line_text=line_text,
                files={p.unit.ident: ran.get(f"{p.unit.module}.{p.unit.key}", []) for p in picks},
                seconds=mutant_seconds(tree, files))
        except StateError as exc:
            stopped = md.failed(stopped, "unmapped")  # it outranks a budget stop, as in the diff lane
            record["engine_tail"] = [str(exc)]
    record["stopped"] = stopped
    if stopped not in (None, "budget") and not record["engine_tail"]:
        record["engine_tail"] = md._tail(log)
    record["elapsed_s"] = round(time.monotonic() - started, 1)
    return record


def decided_count(record: Mapping[str, Any]) -> int:
    """The mutants a slice decided, one by one."""
    return sum(len(r["decided"]) for r in record.get("results", {}).values())


def slow_count(record: Mapping[str, Any]) -> int:
    """The mutants of a slice the cap ended."""
    return sum(1 for r in record.get("results", {}).values() for s in r["decided"].values() if s == SLOW)


def slice_exit(record: Mapping[str, Any]) -> int:
    """2 when the slice's engine or lane failed, or its listing mapped a
    mutant to no planned window; 0 otherwise, a budget stop included."""
    return 2 if record.get("stopped") not in (None, "budget") else 0


# ---------------------------------------------------------------------------
# The stitch: the night's slices into the state
# ---------------------------------------------------------------------------


def merge_counts(state: dict[str, Any], record: Mapping[str, Any], problems: list[str]) -> None:
    """Fold one slice's counts into the state: a count for a function the
    state holds uncounted.  Every slice counts with the same engine at the
    same head, so a count that differs from the state's, or one for a
    function the tree does not hold, is a problem."""
    where = f"slice {record.get('slice')}"
    for ident, counted in record.get("counts", {}).items():
        rec = state["units"].get(ident)
        if rec is None:
            problems.append(f"{where} counted {ident}, which the tree does not hold")
        elif rec["lines"] is None and rec["mutants"] in (None, counted["mutants"]):
            rec["mutants"], rec["lines"] = counted["mutants"], dict(counted["lines"])
        elif rec["mutants"] != counted["mutants"] or rec["lines"] != counted["lines"]:
            problems.append(f"{where} counted {counted['mutants']} mutants of {ident} where the state holds "
                            f"{rec['mutants']}, or on other lines")


def merge(state: dict[str, Any], record: Mapping[str, Any], units: Mapping[str, SweepUnit],
          problems: list[str]) -> int:
    """Fold one slice's results into the state, a mutant at a time; what it
    moved on: the mutants newly decided.  A window's decided mutants gather
    in its ``partial`` record, by window number, and fold into its decided
    window (:func:`fold_window`) once every one is decided.  A function run
    at code the tree does not hold, a window of other lines than the cycle's
    sample, or one of another size than the state's lines give is a problem,
    and that result is left out; a mutant decided twice counts once."""
    added = 0
    where = f"slice {record.get('slice')}"
    for ident, result in record.get("results", {}).items():
        rec = state["units"].get(ident)
        unit = units.get(ident)
        if rec is None or unit is None or rec["hash"] != result["hash"]:
            problems.append(f"{where} ran {ident} at code the tree does not hold")
            continue
        if rec["lines"] is None:
            problems.append(f"{where} ran {ident}, which the state holds uncounted")
            continue
        lines, counts, before = window_counts(state, unit)
        if list(lines) != list(result["lines"]) or sum(counts) != result["window"]:
            problems.append(f"{where} ran {ident} over lines {_listed(result['lines']) or 'none'}, "
                            f"{result['window']} mutants, where the cycle's sample is lines "
                            f"{_listed(lines) or 'none'}, {sum(counts)} mutants")
            continue
        if rec["window"] is not None:
            continue
        partial = rec["partial"] or {"decided": {}, "survivors": []}
        listed = {s["n"]: s for s in result["survivors"]}
        pick = Pick(unit=unit, lines=lines, counts=counts, before=before)
        for number, status in sorted(result["decided"].items(), key=lambda kv: int(kv[0])):
            if number in partial["decided"]:
                continue
            partial["decided"][number] = status
            added += 1
            if status in LISTED:
                n = pick.full_number(int(number))
                partial["survivors"].append(listed.get(n) or {
                    "n": n, "line": pick.line_of(int(number)), "text_sha": None, "status": status,
                    "files": None})
        size = int(result["window"])
        if len(partial["decided"]) == size:
            rec["window"], rec["partial"] = fold_window(partial, size), None
        else:
            rec["partial"] = partial
    return added


def fold_window(partial: Mapping[str, Any], size: int) -> dict[str, Any]:
    """A window whose every mutant is decided, as the decided window the
    summary reads: its columns, its size and its listed mutants by number."""
    columns = dict.fromkeys(COLUMNS, 0)
    for status in partial["decided"].values():
        columns[_column(status)] += 1
    return {**columns, "mutants": size, "survivors": sorted(partial["survivors"], key=lambda s: s["n"])}


def _column(status: str) -> str:
    """Where a decided mutant counts in the committed summary."""
    if status in ("killed", "caught by type check"):
        return "killed"
    if status in ("timeout", "survived", SLOW):
        return status
    if status == "no tests":
        return "no_tests"
    return "other"


def tally(state: Mapping[str, Any], units: Iterable[SweepUnit]) -> dict[str, dict[str, int]]:
    """Per-module counts of the sample's decided mutants, by summary column,
    and the module's mutants in all (``mutants``: the population its sample
    is of)."""
    modules: dict[str, dict[str, int]] = {}
    for unit in units:
        row = modules.setdefault(unit.path, dict.fromkeys((*COLUMNS, "mutants"), 0))
        rec = state["units"][unit.ident]
        row["mutants"] += rec["mutants"] or 0
        if rec["window"] is not None:
            for column in COLUMNS:
                row[column] += int(rec["window"][column])
    return modules


def complete(state: Mapping[str, Any], units: Iterable[SweepUnit]) -> bool:
    """Whether every unit's lines are known and every sampled window decided."""
    return all(sampled_undecided(state, u) == 0 for u in units)


def close_cycle(state: dict[str, Any], units: Sequence[SweepUnit], *, head: str,
                today: str) -> bool:
    """Close the cycle when it is complete: its per-module totals, its
    survivors (``module.key__mutmut_n@line:status``, ``n`` the number mutmut
    gives the mutant over the whole unit, the line the file's at ``head``)
    and its sample's size become ``last_complete``, and the next cycle
    starts with every window undecided."""
    if not complete(state, units):
        return False
    survivors = []
    for u in units:
        for entry in (state["units"][u.ident]["window"] or {}).get("survivors", []):
            survivors.append(f"{u.module}.{u.key}__mutmut_{entry['n']}@{u.start + entry['line'] - 1}:"
                             f"{entry['status']}")
    survivors.sort()
    state["last_complete"] = {"cycle": state["cycle"], "started": state["cycle_started"],
                              "finished": today, "head": head, "engine": state["engine"],
                              "modules": tally(state, units), "survivors": survivors,
                              "sampled": sum(sum(window_counts(state, u)[1]) for u in units),
                              "population": sum(state["units"][u.ident]["mutants"] or 0 for u in units),
                              "fraction": SAMPLE_FRACTION}
    state["cycle"] += 1
    state["cycle_started"] = today
    for rec in state["units"].values():
        rec["window"] = rec["partial"] = None
    return True


def calibrate(state: dict[str, Any], records: Sequence[Mapping[str, Any]],
              units: Mapping[str, SweepUnit]) -> None:
    """Fold the night's measured cost into ``calibration``, the factor on
    ``rate``: each decided mutant's recorded duration over the slice's
    workers (a job's seconds) against its estimate, moved halfway to it."""
    spent = estimate = 0.0
    for record in records:
        workers = int(record.get("workers", WORKERS))
        for ident, result in record.get("results", {}).items():
            unit = units.get(ident)
            if unit is None:
                continue
            for number, seconds in result.get("durations", {}).items():
                if number in result["decided"]:
                    spent += float(seconds) / workers
                    estimate += rate(unit)
    if estimate > 0:
        low, high = CALIBRATION_RANGE
        old = float(state.get("calibration") or 1.0)
        state["calibration"] = round(min(max((old + spent / estimate) / 2, low), high), 3)


def _listed(numbers: Sequence[int]) -> str:
    """``1``, ``1 and 2``, ``1, 2 and 3``."""
    words = [str(n) for n in numbers]
    return words[0] if len(words) == 1 else ", ".join(words[:-1]) + " and " + words[-1]


def empty_night(nights: Sequence[Mapping[str, Any]]) -> bool:
    """Whether the last night the state holds decided no mutant while its
    cycle was open: its line moved nothing, closed nothing, and had work
    planned or a slice lost.  Only a line schema 3 wrote says so: under
    schema 2 a line's ``moved`` counted whole windows alone, and the nights
    of 9 and 10 November 2026 read 0 though their engines decided mutants."""
    if not nights:
        return False
    last = nights[-1]
    return (last.get("schema", 2) >= 3 and last.get("moved") == 0 and not last.get("closed")
            and (any(s.get("planned") for s in last.get("slices", [])) or bool(last.get("lost"))))


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
    converted = state.pop("converted_from", None)
    if converted == 1:
        notes.append("the state was the sweep's that decided mutants by number: its nights carry over, "
                     "and every function and the cycle start afresh with the sample drawn by line")
    elif converted == 2:
        notes.append("the state was schema 2, which decided a window whole: its decided windows carry "
                     "over, and from tonight each mutant is kept as it is decided")
    if engine is not None and state_in.get("engine") not in (None, engine):
        # Every function starts afresh under another engine: the cycle does.
        notes.append(f"mutmut {state_in.get('engine')} gave way to {engine}: every function "
                     "starts afresh, and so does the cycle")
        state["cycle_started"] = today
    for record in valid:
        merge_counts(state, record, problems)
    by_ident = {u.ident: u for u in units}
    added = 0
    for record in valid:
        added += merge(state, record, by_ident, problems)
        if record.get("stopped") not in (None, "budget"):
            # What stopped it: a lane's reason, or the exception the engine's
            # own code raised, when it raised one.
            why = ((record.get("engine_tail") or [None])[0] if record["stopped"] == "lane"
                   else record.get("engine_error") if record["stopped"] == "engine" else None)
            problems.append(f"slice {record['slice']}: stopped by the {record['stopped']}"
                            + (f": {why}" if why else ""))
        elif record.get("stopped") == "budget":
            # A budget stop is a normal stop: what the slice decided is kept,
            # mutant by mutant, and the rest is planned again.
            notes.append(f"slice {record['slice']}: stopped by the budget with {decided_count(record)} "
                         f"mutant(s) decided; the rest of its bin waits for the next night")
    if (added == 0 and (any(r.get("planned") for r in valid) or lost) and not complete(state, units)
            and empty_night(state_in.get("nights", []))):
        # One night that decides nothing is weather (a bin of slow
        # mutants, a lost runner); a second in a row measures nothing.
        problems.append("the night decided no mutant, and neither did the night before it")
    # A lost slice may have held the night's whole plan, so this is read only
    # from a night every slice reported.
    if not lost and not any(r.get("planned") for r in valid) and not complete(state, units):
        problems.append("the night planned nothing while the cycle is open")
    calibrate(state, valid, {u.ident: u for u in units})
    # Only validated records merge, so a lost or failed slice cannot close
    # a cycle wrongly: the cycle closes when its sample is decided.
    closed = close_cycle(state, units, head=head, today=today)
    night = {"date": today, "head": head, "jobs": jobs, "moved": added, "lost": lost, "schema": SCHEMA,
             "slices": [{"slice": r["slice"], "planned": len(r.get("planned", [])),
                         "decided": decided_count(r), "stopped": r.get("stopped"),
                         "engine_s": r.get("engine_s"), "dropped_tests": r.get("dropped_tests", []),
                         "subprocess_tests": len(r.get("subprocess_tests", [])),
                         "source_tests": len(r.get("source_tests", [])), "slow": slow_count(r)}
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
        name, at, line = name.partition("@")
        module, key = md.unit_of_mutant(name)
        inventory_lines.append(f"{module},{key}__mutmut_{md._mutant_number(name)}{'@L' + line if at else ''},{status}")
    (directory / "mutation-survivors.csv").write_text("\n".join(inventory_lines) + "\n",
                                                      encoding="utf-8")
    return score


# ---------------------------------------------------------------------------
# The reports
# ---------------------------------------------------------------------------


def render_slice(record: Mapping[str, Any]) -> str:
    counts: Counter[str] = Counter()
    for result in record.get("results", {}).values():
        counts.update(_column(status) for status in result["decided"].values())
    planned = sum(len(p.get("todo", ())) for p in record.get("planned", []))
    out = [f"## Mutation sweep: slice {record['slice']} of {record['of']}", "",
           f"`{str(record['head'])[:12]}`, mutmut {record.get('engine') or '(not run)'}, "
           f"{record.get('workers', WORKERS)} worker(s), "
           f"budget {record['budget_s']:g} s, {record.get('elapsed_s', 0):.0f} s elapsed; "
           f"{planned} sampled mutant(s) of {len(record['planned'])} window(s) planned, "
           f"{decided_count(record)} decided"
           + (f", the oracle {record['selection']} test files" if record.get("selection") else "")
           + ".", ""]
    if counts:
        out.append(", ".join(f"{column.replace('_', ' ')}: {n}" for column, n in sorted(counts.items())))
        out.append("")
    phases = record.get("phases") or {}
    if any(v is not None for v in phases.values()):
        out.append("Phases, minutes from the slice's start: " + ", ".join(
            f"{key.removesuffix('_s').replace('_', ' ')} {value / 60:.0f}"
            for key, value in phases.items() if value is not None) + ".")
        out.append("")
    if record.get("mem_floor_mib") is not None:
        out.append(f"Lowest available memory {record['mem_floor_mib']:,} MiB, most swap in use "
                   f"{record.get('swap_peak_mib') or 0:,} MiB; the engine's last count "
                   f"{record.get('engine_decided')}.")
        out.append("")
    if record.get("slow"):
        out.append("Ended at the cap of a mutant's run, `slow` (counted apart, never caught): "
                   + ", ".join(f"`{name}`" for name in record["slow"]) + ".")
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


#: The night's rules, as the stitch's summary states them.
RULES = ("The night's rules: each mutant is kept as the engine decides it, and a budget stop is a "
         "normal stop whose undecided mutants the next night plans.  A night is red for a slice its "
         "engine or its lane stopped, a listing that maps a mutant to no planned window, more than "
         f"{LOST_LIMIT_NIGHT} slices with no record, records that disagree (another head, state, "
         "night or engine), a plan with nothing in it while the cycle is open, or a second night in a "
         "row that decides no mutant.  A mutant whose run reaches the cap is `slow`: decided, counted "
         "apart, never caught.  The cycle closes when its sample is decided.")


def render_night(state: Mapping[str, Any], night: Mapping[str, Any],
                 units: Sequence[SweepUnit]) -> str:
    known = [state["units"][u.ident] for u in units]
    population = sum(r["mutants"] or 0 for r in known)
    unknown = sum(1 for r in known if r["lines"] is None)
    drawn = sum(sum(window_counts(state, u)[1]) for u in units)
    open_ = sum(sampled_undecided(state, u) or 0 for u in units)
    windows = sum(1 for u in units if window_counts(state, u)[0])
    decided = sum(1 for u in units if state["units"][u.ident]["window"] is not None)
    out = [f"## Mutation sweep: {night['date']}", "",
           f"`{night['head'][:12]}`, {night['jobs']} job(s): {night['moved']} mutant(s) decided tonight.  "
           f"Cycle {state['cycle']} (from {state['cycle_started']}): {decided} of {windows} sampled windows "
           f"decided, {drawn - open_} of {drawn} sampled mutants, the sample {SAMPLE_FRACTION:.1%} of {population}"
           + (f", {unknown} of {len(units)} functions not yet counted" if unknown else "") + ".", ""]
    if night["slices"]:
        out += ["| Slice | Windows | Mutants decided | Slow | Stopped | Engine s |",
                "|---:|---:|---:|---:|---|---:|"]
        out += [f"| {s['slice']} | {s['planned']} | {s['decided']} | {s.get('slow', 0)} | "
                f"{s['stopped'] or ''} | {s['engine_s'] or 0:.0f} |" for s in night["slices"]]
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
    out += [RULES, ""]
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
    night.add_argument("--max-children", type=int, default=WORKERS,
                       help=f"mutmut's parallel workers (default {WORKERS})")
    night.add_argument("--mutant-cap", type=float, default=MUTANT_CAP_S,
                       help=f"wall-clock seconds a mutant's run may take before it is ended as slow "
                            f"(default {MUTANT_CAP_S})")
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
