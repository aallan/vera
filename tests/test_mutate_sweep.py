"""Tests for scripts/mutate_sweep.py, the nightly mutation sweep over all of vera/.

The sweep measures every function mutmut mutates, a slice a night in parallel
jobs, so no run is a marathon.  Its state, carried from night to night in the
workflow's artifact, records each function's code hash, mutant count and
decided mutants.  What is tested here:

- the inventory: the units mutmut mutates, their code identity and size;
- the state: loading, saving, and reconciling it with the tree (a function
  whose code changed, a new engine, a function gone);
- a night's plan: the undecided work in the tree's order, in one bin a job,
  a function whose count is known split by its mutants' numbers and one whose
  count is not taken whole, the same for every job of the night;
- a slice's results, read off ``mutmut results``, and the stitch that folds
  the night's slices into the state, with what stops a night short;
- closing a cycle, and the committed summary and badge it yields;
- the workflow, read as data;
- a night end to end, against a stand-in engine and against mutmut itself.
"""

from __future__ import annotations

import importlib.util
import json
import os
import shutil
import subprocess
import sys
from pathlib import Path
from typing import Any

import pytest
import yaml

from tests.mutation_engine import starts_the_engine

ROOT = Path(__file__).resolve().parent.parent
WORKFLOW = ROOT / ".github" / "workflows" / "mutation-nightly.yml"
DIFF_WORKFLOW = ROOT / ".github" / "workflows" / "mutation-diff.yml"
#: Both mutation lanes' install step: uv, as ci.yml's lock check installs
#: it, then uv.lock's environment, whose ``bin`` every later step runs from.
LOCKED_INSTALL = ['pip install "uv>=0.5,<2"', "uv sync --locked --extra mutation --python 3.12",
                  'echo "$GITHUB_WORKSPACE/.venv/bin" >> "$GITHUB_PATH"']
SEP = "ǁ"
H = "0" * 16  # a code hash
HEAD = "a" * 40

#: The night of 28 October 2026's engine log (``test_mutate_diff.py``'s
#: ``NIGHT_LOG``, pytest's and pluggy's frames left out): mutmut 3.8.0's stats
#: collector reads ``item._nodeid``, which pytest 9.2.0 dropped, at every
#: test's teardown.
ENGINE_FAILURE_LOG = """\
.E
==================================== ERRORS ====================================
_________________________ ERROR at teardown of test_f __________________________
Traceback (most recent call last):
  File "/venv/lib/python3.12/site-packages/_pytest/runner.py", line 361, in from_call
    result: TResult | None = func()
  File "/venv/lib/python3.12/site-packages/mutmut/runners/harness.py", line 157, in pytest_runtest_teardown
    state().tests_by_mangled_function_name[function].add(strip_prefix(item._nodeid, prefix="mutants/"))
AttributeError: 'Function' object has no attribute '_nodeid'. Did you mean: 'nodeid'?
=========================== short test summary info ============================
ERROR tests/test_m.py::test_f - AttributeError: 'Function' object has no attr...
!!!!!!!!!!!!!!!!!!!!!!!!!! stopping after 1 failures !!!!!!!!!!!!!!!!!!!!!!!!!!!
1 passed, 1 error in 0.01s
failed to collect stats. runner returned 1
"""
ENGINE_ERROR = ("AttributeError: 'Function' object has no attribute '_nodeid'. Did you mean: 'nodeid'? "
                "(mutmut/runners/harness.py:157)")


def _load() -> Any:
    path = ROOT / "scripts" / "mutate_sweep.py"
    spec = importlib.util.spec_from_file_location("mutate_sweep", path)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    sys.modules["mutate_sweep"] = module
    spec.loader.exec_module(module)
    return module


sw = _load()


@pytest.fixture(autouse=True)
def _every_mutant_in_the_sample(monkeypatch: pytest.MonkeyPatch) -> None:
    """The plan, the stitch and the cycle are tested over every mutant; the
    sample's own tests set a share of their own."""
    monkeypatch.setattr(sw, "SAMPLE_FRACTION", 1.0)


def _u(path: str, key: str, start: int = 1, code: str = H) -> Any:
    return sw.SweepUnit(path=path, key=key, start=start, hash=code)


A = _u("vera/a.py", "x_f", 1)
B = _u("vera/a.py", f"x{SEP}C{SEP}m", 20)
C = _u("vera/b.py", "x_g", 1)
UNITS = [A, B, C]  # the tree's order
CORE_UNIT = _u("vera/verifier.py", "x_v", 1)


def _lines(n: int | None) -> dict[str, int] | None:
    """A unit's mutants by line: one on each of lines 1 to n (None: uncounted)."""
    return None if n is None else {str(i): 1 for i in range(1, n + 1)}


def _state(**counts: int | None) -> dict[str, Any]:
    """A reconciled state, each unit's mutants given by its key, one a line
    on lines 1 to n (None: uncounted)."""
    state = sw.reconcile(sw.empty_state("2026-10-16"), UNITS, "3.8.0")
    for unit in UNITS:
        n = counts.get(unit.key.split(SEP)[-1].removeprefix("x_"))
        state["units"][unit.ident]["mutants"] = n
        state["units"][unit.ident]["lines"] = _lines(n)
    return state


#: The status a test's column stands for.
STATUS_OF = {"killed": "killed", "survived": "survived", "timeout": "timeout", "no_tests": "no tests",
             "slow": "slow", "other": "suspicious"}


def _listed(size: int, columns: dict[str, int], survivors: tuple[str, ...]) -> tuple[dict[str, str], list[Any]]:
    """A window's decided mutants by number and its listed ones' records:
    each ``n@line:status`` given at its number, the rest of the columns'
    mutants at the lowest numbers left, in the columns' order (a test unit
    holds one mutant a line from its first, so a number is its line)."""
    left = dict(columns)
    decided: dict[str, str] = {}
    records: list[Any] = []
    for entry in survivors:
        record = sw._survivor_2(entry)
        if not isinstance(record, dict):
            records.append(record)  # malformed on purpose
            continue
        decided[str(record["n"])] = record["status"]
        left[record["status"]] -= 1
        records.append(record)
    free = iter(n for n in range(1, size + 1) if str(n) not in decided)
    for column in sw.COLUMNS:
        for _ in range(left.get(column, 0)):
            n = next(free)
            decided[str(n)] = STATUS_OF[column]
            if STATUS_OF[column] in sw.LISTED:
                records.append({"n": n, "line": n, "text_sha": None, "status": STATUS_OF[column], "files": None})
    return dict(sorted(decided.items(), key=lambda kv: int(kv[0]))), sorted(
        records, key=lambda r: r["n"] if isinstance(r, dict) else 0)


def _window(killed: int = 0, survived: int = 0, timeout: int = 0, no_tests: int = 0, other: int = 0,
            survivors: tuple[str, ...] = (), slow: int = 0) -> dict[str, Any]:
    """A decided window: its columns, summing to its size, and its listed
    mutants' records (``n@line:status`` where a test names them)."""
    columns = {"killed": killed, "survived": survived, "timeout": timeout, "no_tests": no_tests, "slow": slow,
               "other": other}
    size = sum(columns.values())
    _, records = _listed(size, columns, survivors)
    return {**columns, "mutants": size, "survivors": records}


def _decide(state: dict[str, Any], unit: Any, **window: Any) -> None:
    """Decide the unit's sampled window with the given columns."""
    state["units"][unit.ident]["window"] = _window(**window)


def _res(unit: Any, *, hash_: str = H, lines: list[int] | None = None, survivors: tuple[str, ...] = (),
         window: int | None = None, **columns: int) -> dict[str, Any]:
    """A slice's result for a unit's window: the columns' mutants decided,
    the window their sum unless given, over lines 1 to the window unless
    given."""
    columns = {c: columns.get(c, 0) for c in sw.COLUMNS}
    size = sum(columns.values()) if window is None else window
    decided, records = _listed(size, columns, survivors)
    return {"hash": hash_, "window": size, "lines": list(range(1, size + 1)) if lines is None else lines,
            "decided": decided, "survivors": records, "durations": {}, "estimates": {}}


def _bins(picks: list[list[Any]]) -> list[list[tuple[str, tuple[int, ...]]]]:
    return [[(p.unit.key, p.lines) for p in b] for b in picks]


# ---------------------------------------------------------------------------
# The inventory
# ---------------------------------------------------------------------------


SOURCE = '''\
def plain(x):
    """A docstring."""
    return x + 1


@property
def decorated(self):
    return 1


def blocked(x):  # pragma: no mutate block
    return x


class Box:
    def method(self, y):
        return [y, y * 2, y - 3, y // 4]
'''


class TestInventory:
    def test_the_units_are_the_ones_mutmut_mutates_in_the_files_order(self) -> None:
        units = sw.units_of(SOURCE, "vera/m.py")
        assert [(u.key, u.start) for u in units] == [("x_plain", 1), (f"x{SEP}Box{SEP}method", 16)]

    def test_a_units_identity_is_its_text_and_an_edit_above_it_changes_nothing(self) -> None:
        """The state numbers a unit's lines from its first, so the identity
        changes with anything that moves or changes what a line of the unit
        holds (its docstring, a comment, its layout, its code) and with
        nothing above it in the file (PR #1831 review)."""
        (plain,) = [u for u in sw.units_of(SOURCE, "m.py") if u.key == "x_plain"]
        (moved,) = [u for u in sw.units_of("import os\n\n\n" + SOURCE, "m.py") if u.key == "x_plain"]
        assert (moved.hash, moved.start) == (plain.hash, plain.start + 3)
        for edit in (SOURCE.replace('    """A docstring."""\n', ""), SOURCE.replace("x + 1", "x+1  # one more"),
                     SOURCE.replace("    return x + 1\n", "    # a comment\n    return x + 1\n"),
                     SOURCE.replace("x + 1", "x + 2")):
            (other,) = [u for u in sw.units_of(edit, "m.py") if u.key == "x_plain"]
            assert other.hash != plain.hash, edit

    def test_a_pragma_line_enters_a_units_identity(self) -> None:
        """`# pragma: no mutate` changes mutmut's mutants and not the code, so
        it must change the identity, or a decided function is never redone."""
        (plain,) = [u for u in sw.units_of(SOURCE, "m.py") if u.key == "x_plain"]
        marked = SOURCE.replace("    return x + 1\n", "    return x + 1  # pragma: no mutate\n")
        (pragma,) = [u for u in sw.units_of(marked, "m.py") if u.key == "x_plain"]
        assert pragma.hash != plain.hash

    def test_the_inventory_is_in_the_trees_order(self) -> None:
        units = sw.inventory({"vera/b.py": "def z():\n    return 1\n",
                              "vera/a.py": "def y():\n    return 2\n\n\ndef x():\n    return 3\n"})
        assert [(u.path, u.key) for u in units] == [("vera/a.py", "x_y"), ("vera/a.py", "x_x"),
                                                    ("vera/b.py", "x_z")]


# ---------------------------------------------------------------------------
# The state
# ---------------------------------------------------------------------------


class TestState:
    def test_no_state_is_the_start_of_cycle_one(self, tmp_path: Path) -> None:
        state = sw.load_state(tmp_path / "absent" / sw.STATE_FILE, "2026-10-16")
        assert state["cycle"] == 1 and state["units"] == {} and state["cycle_started"] == "2026-10-16"
        assert sw.state_digest(tmp_path / "absent" / sw.STATE_FILE) == "none"

    def test_a_state_round_trips(self, tmp_path: Path) -> None:
        state = _state(f=4)
        _decide(state, A, killed=3, survived=1, survivors=("4@4:survived",))
        path = sw.save_state(state, tmp_path)
        assert sw.load_state(path, "x") == state
        assert len(sw.state_digest(path)) == 64

    def test_a_state_of_another_schema_or_none_at_all_is_refused(self, tmp_path: Path) -> None:
        path = tmp_path / sw.STATE_FILE
        path.write_text(json.dumps({"schema": 99, "units": {}}), encoding="utf-8")
        with pytest.raises(sw.StateError):
            sw.load_state(path, "x")
        path.write_text("{not json", encoding="utf-8")
        with pytest.raises(sw.StateError):
            sw.load_state(path, "x")

    def test_a_function_whose_code_changed_starts_afresh(self) -> None:
        state = _state(f=4, m=3)
        _decide(state, A, killed=4)
        _decide(state, B, killed=3)
        state = sw.reconcile(state, [_u("vera/a.py", "x_f", 1, code="1" * 16), B, C], "3.8.0")
        assert state["units"][A.ident] == {"hash": "1" * 16, "mutants": None, "lines": None, "window": None,
                                           "partial": None}
        assert state["units"][B.ident] == {"hash": H, "mutants": 3, "lines": _lines(3), "window": _window(killed=3),
                                           "partial": None}

    def test_a_new_engine_starts_every_function_afresh(self) -> None:
        """mutmut makes a function's mutants by its own rules, so a count,
        its lines and a decided window mean nothing under another version."""
        state = _state(f=4)
        _decide(state, A, killed=4)
        state = sw.reconcile(state, UNITS, "3.9.0")
        assert state["engine"] == "3.9.0"
        assert all(r == {"hash": H, "mutants": None, "lines": None, "window": None, "partial": None}
                   for r in state["units"].values())

    def test_a_function_gone_from_the_tree_is_dropped(self) -> None:
        state = sw.reconcile(_state(), [A, B], "3.8.0")
        assert C.ident not in state["units"]


def _written_state() -> dict[str, Any]:
    """A state as the stitch writes it: a closed cycle, a night, a count."""
    state = _state(f=4, m=3, g=5)
    for unit, n in {A: 4, B: 3}.items():
        _decide(state, unit, killed=n)
    _decide(state, C, killed=4, survived=1, survivors=("5@5:survived",))
    written, night = sw.stitch(state, "none", [_record(0, 1, {}, planned=0)], jobs=1, head=HEAD, units=UNITS,
                               today="2026-10-17")
    assert night["closed"]
    _decide(written, A, killed=2)
    _decide(written, C, killed=4, survived=1, survivors=("5@5:survived",))
    written["units"][B.ident]["partial"] = {"decided": {"1": "killed", "3": "survived"}, "survivors": [
        {"n": 3, "line": 3, "text_sha": "0" * 16, "status": "survived", "files": ["tests/test_a.py"]}]}
    return json.loads(json.dumps(written))


def _set(*path: Any) -> Any:
    """A change at ``path[:-1]`` to the value ``path[-1]``."""
    def change(state: dict[str, Any]) -> None:
        target: Any = state
        for key in path[:-2]:
            target = target[key]
        target[path[-2]] = path[-1]
    return change


BAD_STATES: dict[str, tuple[Any, str]] = {
    "another schema": (_set("schema", 4), "not a schema 3 state"),
    "a field it does not have": (_set("extra", 1), "the state does not have exactly the fields"),
    "an engine that is not a version": (_set("engine", "3.8.0; touch /tmp/x"), "the engine version is malformed"),
    "a cycle of zero": (_set("cycle", 0), "the cycle is not a whole number"),
    "a cycle that is a flag": (_set("cycle", True), "the cycle is not a whole number"),
    "a start that is not a date": (_set("cycle_started", "yesterday"), "the cycle's start is malformed"),
    "a calibration out of range": (_set("calibration", 101.0), "the calibration is not a number from 0.2 to 100.0"),
    "a calibration that is not a number": (_set("calibration", float("nan")), "the calibration is not a number"),
    "a function outside vera/": (lambda s: s["units"].update({"../etc/x.py::x_f": s["units"][A.ident]}),
                                 "function '../etc/x.py::x_f' is malformed"),
    "a hash that is not hex": (_set("units", A.ident, "hash", "zz"), "vera/a.py::x_f's hash is malformed"),
    "a mutant count over the limit": (_set("units", A.ident, "mutants", sw.MAX_MUTANTS + 1),
                                      "vera/a.py::x_f's mutant count is not a whole number from 0 to 100000"),
    "a negative mutant count": (_set("units", A.ident, "mutants", -1), "vera/a.py::x_f's mutant count"),
    "lines that do not sum to the count": (_set("units", A.ident, "lines", "9", 1),
                                           "vera/a.py::x_f's lines do not sum to its count"),
    "a line with no mutant": (_set("units", A.ident, "lines", "1", 0), "vera/a.py::x_f's mutants on line 1"),
    "a line of zero": (lambda s: s["units"][A.ident]["lines"].update({"0": 1}), "line '0' is out of range"),
    "a line in other digits": (lambda s: s["units"][A.ident]["lines"].update({"\u00b2": 1}),
                               "line '\u00b2' is out of range"),
    "a date in other digits": (_set("cycle_started", "\u0662\u0660\u0662\u0666-\u0661\u0660-\u0661\u0666"),
                               "the cycle's start is malformed"),
    "a window whose columns do not sum to it": (_set("units", A.ident, "window", "mutants", 9),
                                                "window columns do not sum to its size"),
    "a window with a column that is not a count": (_set("units", A.ident, "window", "killed", "many"),
                                                   "vera/a.py::x_f's killed is not a whole number"),
    "a window's survivor that is not a record": (_set("units", A.ident, "window", "survivors", ["x; rm"]),
                                                 "vera/a.py::x_f's survivor does not have exactly the fields"),
    "a window's survivor of another status": (
        lambda s: s["units"][C.ident]["window"]["survivors"][0].update(status="killed"),
        "vera/b.py::x_g's survivor's status is not one a window lists"),
    "a window's survivor's test file outside tests/": (
        lambda s: s["units"][C.ident]["window"]["survivors"][0].update(files=["../x.py"]),
        "vera/b.py::x_g's survivor's test files"),
    "a window whose survivors are not its survived": (
        lambda s: s["units"][C.ident]["window"]["survivors"].clear(),
        "vera/b.py::x_g's survivors are not its survived, timeout, slow, memory and lost mutants"),
    "a window's memory column of zero": (_set("units", C.ident, "window", "memory", 0),
                                         "vera/b.py::x_g's memory is not a whole number from 1"),
    "a loss at the limit": (lambda s: s["units"][B.ident].update(losses={"2": sw.LOSS_LIMIT}),
                            "losses of mutant 2 is not a whole number from 1 to 1"),
    "a loss of a decided mutant": (lambda s: s["units"][B.ident].update(losses={"1": 1}),
                                   "loss of mutant '1' is not of an undecided mutant"),
    "a loss beside a decided window": (lambda s: s["units"][A.ident].update(losses={"1": 1}),
                                       "has losses outside an open window"),
    "losses that are empty": (lambda s: s["units"][B.ident].update(losses={}), "'s losses"),
    "a night's lost plan that is not a digest": (_set("nights", 0, "lost_plans", {"0": "plan"}),
                                                 "a night's lost plans"),
    "a night's lost plan of a slice out of range": (_set("nights", 0, "lost_plans", {"99": "0" * 16}),
                                                    "a night's lost plans"),
    "a partial window and a decided one": (_set("units", A.ident, "partial", {"decided": {}, "survivors": []}),
                                           "has a decided window and a partial one"),
    "a partial window's mutant outside the window": (
        lambda s: s["units"][B.ident].update(partial={"decided": {"9": "killed"}, "survivors": []}),
        "vera/a.py::xǁCǁm's mutant '9' is outside its window"),
    "a partial window's undecided status": (
        lambda s: s["units"][B.ident].update(partial={"decided": {"1": "not checked"}, "survivors": []}),
        "vera/a.py::xǁCǁm's mutant 1 has no decided status"),
    "a partial window that is whole": (
        lambda s: s["units"][B.ident].update(
            partial={"decided": {"1": "killed", "2": "killed", "3": "killed"}, "survivors": []}),
        "vera/a.py::xǁCǁm's partial window is whole"),
    "a decided window and no lines": (_set("units", A.ident, "lines", None), "has a decided window and no lines"),
    "a schema the state was not converted from": (_set("converted_from", 3), "the schema the state was converted from"),
    "a closed cycle's head that is not a commit": (_set("last_complete", "head", "main"),
                                                   "the last closed cycle's head is malformed"),
    "a closed cycle's negative count": (_set("last_complete", "modules", "vera/a.py", "killed", -1),
                                        "vera/a.py's killed is not a whole number"),
    "a survivor that is not a mutant": (lambda s: s["last_complete"]["survivors"].append("x; rm:survived"),
                                        "survivor 'x; rm:survived' is malformed"),
    "a night's head that is not a commit": (_set("nights", 0, "head", "abc"), "a night's head is malformed"),
    "a night's lost slice out of range": (_set("nights", 0, "lost", [sw.MAX_JOBS]), "a night's lost slices"),
    "a night's lost slice listed twice": (_set("nights", 0, "lost", [0, 0]), "a night's lost slices"),
    "a night's source-reading count that is negative": (
        _set("nights", 0, "slices", 0, "source_tests", -1), "a night's source-reading tests"),
    "a closed cycle's fraction over one": (_set("last_complete", "fraction", 1.5),
                                           "the last closed cycle's fraction"),
    "a closed cycle's negative sample": (_set("last_complete", "sampled", -1), "the last closed cycle's sample"),
    "a module's negative population": (_set("last_complete", "modules", "vera/a.py", "mutants", -1),
                                       "vera/a.py's mutants is not a whole number"),
    "too many nights": (lambda s: s.update(nights=s["nights"] * (sw.KEPT_NIGHTS + 1)), "the nights"),
}


def _carried() -> dict[str, Any]:
    state = _state(f=4)
    _decide(state, A, killed=4)
    return state


def _lane_failed() -> dict[str, Any]:
    record = _record(0, 1, {}, stopped="lane")
    record["engine"] = None
    return record


#: Every path the stitch can take, problem or not: the state it starts
#: from, and the night's records.
STITCH_PATHS: dict[str, tuple[Any, Any]] = {
    "a first night with no record": (lambda: sw.empty_state("2026-10-16"), lambda: []),
    "a carried state with no record": (_carried, lambda: []),
    "a first night whose every slice failed": (lambda: sw.empty_state("2026-10-16"), lambda: [_lane_failed()]),
    "a carried state whose every slice failed": (_carried, lambda: [_lane_failed()]),
    "a malformed record": (lambda: sw.empty_state("2026-10-16"),
                           lambda: [{**_record(0, 1, {}), "head": "main"}]),
    "a window of another size than the sample": (_carried, lambda: [_record(0, 1, {A.ident: _res(A, killed=3)})]),
    "a first night that decides": (lambda: sw.empty_state("2026-10-16"),
                                   lambda: [_record(0, 1, {A.ident: _res(A, killed=4)})]),
}


class TestTheStitchesOwnState:
    """Whatever the night did, the state the stitch keeps is one the next
    night loads: a state it refuses would stop every night after."""

    @pytest.mark.parametrize("start,records", list(STITCH_PATHS.values()), ids=list(STITCH_PATHS))
    def test_the_next_night_loads_it(self, start: Any, records: Any, tmp_path: Path) -> None:
        state, _ = sw.stitch(start(), "none", records(), jobs=1, head=HEAD, units=UNITS, today="2026-10-17")
        assert sw.load_state(sw.save_state(state, tmp_path), "x") == state


class TestStateChecks:
    """The state comes from an artifact, so every field is checked."""

    def test_a_state_the_stitch_wrote_loads(self, tmp_path: Path) -> None:
        state = _written_state()
        assert sw.load_state(sw.save_state(state, tmp_path), "x") == state

    def test_a_night_line_from_before_the_lost_field_loads(self, tmp_path: Path) -> None:
        """The states in the workflow's artifacts predate the field, and a
        state the script refuses stops every night (#1751)."""
        state = _written_state()
        assert "lost" in state["nights"][0]
        del state["nights"][0]["lost"]
        assert sw.load_state(sw.save_state(state, tmp_path), "x") == state

    def test_a_state_from_before_the_sample_loads(self, tmp_path: Path) -> None:
        """The states in the workflow's artifacts predate the sample's
        fields (#1827): a slice line's source-reading count, a closed cycle's
        sample, population and fraction, and a module's population."""
        state = _written_state()
        del state["nights"][0]["slices"][0]["source_tests"]
        for key in ("sampled", "population", "fraction"):
            del state["last_complete"][key]
        for row in state["last_complete"]["modules"].values():
            del row["mutants"]
        assert sw.load_state(sw.save_state(state, tmp_path), "x") == state

    @pytest.mark.parametrize("change,why", list(BAD_STATES.values()), ids=list(BAD_STATES))
    def test_a_state_out_of_bounds_is_refused(self, change: Any, why: str, tmp_path: Path) -> None:
        state = _written_state()
        change(state)
        with pytest.raises(sw.StateError) as caught:
            sw.load_state(sw.save_state(state, tmp_path), "x")
        assert why in str(caught.value)

    def test_a_schema_one_state_loads_converted_and_the_stitch_notes_it(self, tmp_path: Path) -> None:
        """The artifact of the sweep that decided mutants by number (to
        4 November 2026, #1829): each unit keeps its hash and its count, its
        lines and window unknown; the engine, the calibration and the nights
        (the drop memory) carry over; the cycle starts afresh; and the state
        the stitch writes is a plain schema 3 state."""
        old = {"schema": 1, "engine": "3.8.0", "cycle": 1, "cycle_started": "2026-10-28", "calibration": 1.5,
               "units": {A.ident: {"hash": H, "mutants": 4, "statuses": {"1": "killed", "3": "survived"}},
                         C.ident: {"hash": H, "mutants": None, "statuses": {}}},
               "last_complete": None,
               "nights": [{"date": "2026-11-03", "head": HEAD, "jobs": 7, "moved": 3, "lost": [6],
                           "slices": [{"slice": 0, "planned": 2, "decided": 3, "stopped": "budget",
                                       "engine_s": 100.0, "dropped_tests": ["tests/test_m.py::test_f"],
                                       "subprocess_tests": 1}],
                           "problems": [], "notes": [], "closed": False}]}
        path = tmp_path / sw.STATE_FILE
        path.write_text(json.dumps(old), encoding="utf-8")
        state = sw.load_state(path, "2026-11-05")
        assert state["schema"] == 3 and state["converted_from"] == 1
        assert (state["cycle"], state["cycle_started"], state["engine"], state["calibration"]) == (
            2, "2026-11-05", "3.8.0", 1.5)
        assert state["units"][A.ident] == {"hash": H, "mutants": 4, "lines": None, "window": None, "partial": None}
        assert state["units"][C.ident] == {"hash": H, "mutants": None, "lines": None, "window": None,
                                           "partial": None}
        assert state["nights"] == old["nights"]
        written, night = sw.stitch(state, sw.state_digest(path), [_record(0, 1, {}, planned=0, digest=sw.state_digest(path))],
                                   jobs=1, head=HEAD, units=UNITS, today="2026-11-05")
        assert "converted_from" not in written and night["notes"] == [
            "the state was the sweep's that decided mutants by number: its nights carry over, and every "
            "function and the cycle start afresh with the sample drawn by line"]
        assert sw.load_state(sw.save_state(written, tmp_path / "out"), "x") == written
        bad = dict(old, units={A.ident: "not a record"})
        path.write_text(json.dumps(bad), encoding="utf-8")
        with pytest.raises(sw.StateError, match="not a schema 3 state"):
            sw.load_state(path, "2026-11-05")

    def test_a_partial_window_is_bounded_by_the_cycles_sample(self, tmp_path: Path,
                                                             monkeypatch: pytest.MonkeyPatch) -> None:
        """A partial window holding every sampled mutant is a decided window
        recorded in the wrong place: the cycle would read it complete while
        the tally reads nothing of it, so the state refuses it."""
        monkeypatch.setattr(sw, "in_sample", lambda cycle, ident, line: line <= 2)
        state = _written_state()
        state["units"][B.ident]["partial"] = {"decided": {"1": "killed", "2": "killed"}, "survivors": []}
        with pytest.raises(sw.StateError, match="partial window is whole"):
            sw.load_state(sw.save_state(state, tmp_path), "x")
        state["units"][B.ident]["partial"] = {"decided": {"3": "killed"}, "survivors": []}
        with pytest.raises(sw.StateError, match="mutant '3' is outside its window"):
            sw.load_state(sw.save_state(state, tmp_path), "x")
        state["units"][B.ident]["partial"] = {"decided": {"2": "killed"}, "survivors": []}
        assert sw.load_state(sw.save_state(state, tmp_path), "x")["units"][B.ident]["partial"]

    def test_an_engine_error_is_one_line_beside_an_engine_stop_and_nowhere_else(self) -> None:
        """The stitch and the reports read ``engine_error`` only beside
        ``stopped == "engine"``, so a record carrying it beside another stop
        holds an exception nothing shows; and one line is one line as
        ``str.splitlines`` reads it (U+2028 and U+0085 break a line)."""
        record = _record(0, 1, {}, stopped="engine")
        record["engine_error"] = ENGINE_ERROR
        sw.check_record(record)
        for stopped in (None, "budget", "unmapped", "lane"):
            record["stopped"] = stopped
            with pytest.raises(sw.StateError, match="its engine error"):
                sw.check_record(record)
        record["stopped"] = "engine"
        for broken in (f"{ENGINE_ERROR[:20]} {ENGINE_ERROR[20:]}", f"{ENGINE_ERROR[:20]}\x85{ENGINE_ERROR[20:]}",
                       ENGINE_ERROR + "\n"):
            record["engine_error"] = broken
            with pytest.raises(sw.StateError, match="its engine error"):
                sw.check_record(record)

    @pytest.mark.parametrize("field,value", [
        ("head", "main"), ("state_in", "../x"), ("stopped", "maybe"), ("engine_s", -1),
        ("results", {A.ident: _res(A, hash_="zz", killed=1)}),
        ("results", {A.ident: {**_res(A, killed=1), "window": None}}),
        ("results", {A.ident: {**_res(A, killed=2), "lines": [2, 1]}}),
        ("results", {A.ident: {**_res(A, killed=2), "statuses": {"killed": 3}}}),
        ("results", {A.ident: _res(A, killed=1, survivors=("x",))}),
        ("dropped_tests", ["a\nb"]), ("source_tests", ["a\nb"]), ("deselected_tests", "x"),
        ("counts", [1]), ("counts", {"../x.py::x_f": {"mutants": 1, "lines": {"1": 1}}}),
        ("counts", {A.ident: {"mutants": -1, "lines": {}}}), ("counts", {A.ident: 4}),
        ("counts", {A.ident: {"mutants": 2, "lines": {"1": 1}}}),
        ("engine_error", ["AttributeError: x"]), ("engine_error", "AttributeError: x\n(mutmut/x.py:1)"),
        ("engine_error", "x" * 501),
    ])
    def test_a_malformed_slice_record_stops_the_night_short(self, field: str, value: Any) -> None:
        record = _record(0, 1, {A.ident: _res(A, killed=4)})
        if field == "engine_error":
            record["stopped"] = "engine"  # the one stop the field may stand beside: its shape refuses it
        record[field] = value
        state, night = _stitch([record], jobs=1)
        assert night["problems"][0].startswith("slice 0: a malformed record")
        assert state["units"][A.ident]["window"] is None
        assert night["lost"] == []  # a malformed record is still a record


REPO_ID = 1234
WORKFLOW_PATH = ".github/workflows/mutation-nightly.yml"


def _run(run_id: int, created: str, *, event: str = "schedule", head_repo: int = REPO_ID,
         path: str = WORKFLOW_PATH) -> dict[str, Any]:
    return {"id": run_id, "event": event, "head_branch": "main", "status": "completed",
            "created_at": created, "head_repository": {"id": head_repo}, "repository": {"id": REPO_ID},
            "path": path}


class TestFindState:
    """The night carries on from its own workflow's last state, never from an
    artifact another run could have uploaded under the same name."""

    def test_the_newest_own_run_with_a_state_is_taken(self) -> None:
        runs = [_run(1, "2026-10-14T21:00:00Z"), _run(3, "2026-10-16T21:00:00Z"),
                _run(2, "2026-10-15T21:00:00Z", event="workflow_dispatch")]
        assert sw.pick_state_run(runs, REPO_ID, lambda run: True) == 3

    def test_a_forks_run_on_a_branch_named_main_is_never_taken(self) -> None:
        runs = [_run(9, "2026-10-17T00:00:00Z", head_repo=666), _run(3, "2026-10-16T21:00:00Z")]
        assert sw.pick_state_run(runs, REPO_ID, lambda run: True) == 3

    def test_a_run_of_another_event_or_workflow_is_never_taken(self) -> None:
        runs = [_run(8, "2026-10-17T02:00:00Z", event="pull_request"),
                _run(7, "2026-10-17T01:00:00Z", path=".github/workflows/ci.yml"),
                _run(3, "2026-10-16T21:00:00Z")]
        assert sw.pick_state_run(runs, REPO_ID, lambda run: True) == 3

    def test_a_run_without_a_live_state_gives_way_to_the_one_before(self) -> None:
        runs = [_run(2, "2026-10-15T21:00:00Z"), _run(3, "2026-10-16T21:00:00Z")]
        assert sw.pick_state_run(runs, REPO_ID, lambda run: run != 3) == 2
        assert sw.pick_state_run([], REPO_ID, lambda run: True) is None

    def test_a_failed_lookup_fails_and_never_reads_as_no_state(
        self, tmp_path: Path, capsys: pytest.CaptureFixture[str],
    ) -> None:
        fake = tmp_path / "failing_gh.py"
        fake.write_text("import sys\nprint('HTTP 502', file=sys.stderr)\nsys.exit(1)\n", encoding="utf-8")
        with pytest.raises(sw.md.LaneError):
            sw.main(["find-state", "--repo", "o/r", "--repo-id", str(REPO_ID), "--gh", sys.executable, str(fake)])
        assert "run=" not in capsys.readouterr().out

    def test_the_command_asks_for_this_workflows_completed_runs_on_main(
        self, tmp_path: Path, capsys: pytest.CaptureFixture[str],
    ) -> None:
        log = tmp_path / "gh.jsonl"
        fake = tmp_path / "fake_gh.py"
        fake.write_text(
            "import json, sys\n"
            f"open({str(log)!r}, 'a', encoding='utf-8').write(json.dumps(sys.argv[1:]) + '\\n')\n"
            "path = sys.argv[2]\n"
            f"runs = {json.dumps({'workflow_runs': [_run(5, '2026-10-16T21:00:00Z'), _run(6, '2026-10-17T21:00:00Z', head_repo=666)]})}\n"
            "arts = {'artifacts': [{'name': 'mutation-sweep-state', 'expired': False}]}\n"
            "print(json.dumps(runs if '/workflows/' in path else arts))\n", encoding="utf-8")
        assert sw.main(["find-state", "--repo", "o/r", "--repo-id", str(REPO_ID),
                        "--gh", sys.executable, str(fake)]) == 0
        assert capsys.readouterr().out == "run=5\n"
        calls = [json.loads(line) for line in log.read_text(encoding="utf-8").splitlines()]
        assert calls == [
            ["api", "repos/o/r/actions/workflows/mutation-nightly.yml/runs?branch=main&status=completed&per_page=100"],
            ["api", "repos/o/r/actions/runs/5/artifacts?name=mutation-sweep-state"]]


# ---------------------------------------------------------------------------
# A night's plan
# ---------------------------------------------------------------------------


def _plan(state: dict[str, Any], *, jobs: int = 1, mutants: int, units: list[Any] = UNITS) -> list[list[Any]]:
    """The plan with a job's capacity of ``mutants`` mutants outside the core
    (the class sets ``FIXED_S`` to 0, so the budget is all capacity)."""
    return sw.plan(state, units, jobs=jobs, budget_s=mutants * sw.OTHER_RATE_S)


class TestPlan:
    @pytest.fixture(autouse=True)
    def _no_fixed_passes(self, monkeypatch: pytest.MonkeyPatch) -> None:
        monkeypatch.setattr(sw, "FIXED_S", 0)

    def test_the_fixed_passes_come_out_of_a_jobs_budget(self, monkeypatch: pytest.MonkeyPatch) -> None:
        """The stats pass and the clean run come before the first mutant; a
        quarter of the budget is left to mutants whatever they cost, and a
        job's first window is taken whole whatever it costs."""
        monkeypatch.setattr(sw, "FIXED_S", 30)
        assert _bins(sw.plan(_state(f=4, m=3, g=5), UNITS, jobs=1, budget_s=40)) == [[("x_f", (1, 2, 3, 4))]]
        assert _bins(sw.plan(_state(f=4, m=3, g=5), UNITS, jobs=1, budget_s=20)) == [[("x_f", (1, 2, 3, 4))]]

    def test_the_plan_takes_the_tree_in_order_up_to_a_jobs_capacity(self) -> None:
        bins = _plan(_state(f=4, m=3, g=5), mutants=7)
        assert _bins(bins) == [[("x_f", (1, 2, 3, 4)), (f"x{SEP}C{SEP}m", (1, 2, 3))]]

    def test_the_nights_units_are_spread_over_every_job_the_dearest_first(self) -> None:
        """A unit goes whole into one job; the night's units go the dearest
        first into the job holding least, so every job has work while the
        units outnumber them (#1838: on four nights three of seven jobs
        planned nothing while 362 mutants waited)."""
        bins = _plan(_state(f=4, m=3, g=5), jobs=3, mutants=5)
        assert _bins(bins) == [[("x_g", (1, 2, 3, 4, 5))], [("x_f", (1, 2, 3, 4))], [(f"x{SEP}C{SEP}m", (1, 2, 3))]]
        two = _plan(_state(f=4, m=3, g=5), jobs=2, mutants=10)
        assert _bins(two) == [[("x_g", (1, 2, 3, 4, 5))], [("x_f", (1, 2, 3, 4)), (f"x{SEP}C{SEP}m", (1, 2, 3))]]

    def test_a_function_without_its_lines_stops_the_plan(self) -> None:
        """Every unit is counted before the plan, by mutmut's own visitor
        through the engine; one that is not cannot be sampled."""
        with pytest.raises(sw.StateError, match="has no mutants by line"):
            _plan(_state(f=4), jobs=2, mutants=6)  # m and g uncounted

    def test_the_nights_first_unit_is_taken_whatever_it_costs(self) -> None:
        """A night with work open decides something, so it cannot stall; the
        units after one past the night's capacity wait."""
        state = sw.reconcile(sw.empty_state("d"), [CORE_UNIT, C], "3.8.0")
        state["units"][CORE_UNIT.ident].update(mutants=3, lines=_lines(3))
        state["units"][C.ident].update(mutants=1, lines=_lines(1))
        bins = sw.plan(state, [CORE_UNIT, C], jobs=2, budget_s=1)
        assert _bins(bins) == [[("x_v", (1, 2, 3))], []]

    def test_only_the_cycles_sample_is_planned(self, monkeypatch: pytest.MonkeyPatch) -> None:
        """The plan holds each unit's sampled lines and no other, in the
        tree's order, less the windows decided."""
        monkeypatch.setattr(sw, "SAMPLE_FRACTION", 0.5)
        state = _state(f=40, m=40, g=40)
        drawn = {u.key: tuple(line for line in range(1, 41) if sw.in_sample(1, u.ident, line)) for u in UNITS}
        assert all(5 <= len(lines) <= 35 for lines in drawn.values()), drawn
        assert _bins(_plan(state, mutants=200))[0] == [(u.key, drawn[u.key]) for u in UNITS]
        (pick,) = [p for p in _plan(state, mutants=200)[0] if p.unit is A]
        assert pick.counts == (1,) * len(drawn["x_f"]) and pick.mutants == len(drawn["x_f"])
        _decide(state, A, killed=len(drawn["x_f"]))
        assert _bins(_plan(state, mutants=200))[0][0] == (B.key, drawn[B.key])

    def test_decided_windows_are_not_planned_again(self) -> None:
        state = _state(f=4, m=3, g=5)
        _decide(state, A, killed=4)
        _decide(state, B, killed=2, survived=1, survivors=("2@2:survived",))
        bins = _plan(state, mutants=4)
        assert _bins(bins) == [[("x_g", (1, 2, 3, 4, 5))]]  # the first piece, whatever it costs

    def test_every_job_of_the_night_computes_the_same_disjoint_bins(self) -> None:
        state = _state(f=4, m=3, g=5)
        first, second = _plan(state, jobs=3, mutants=4), _plan(json.loads(json.dumps(state)), jobs=3, mutants=4)
        assert _bins(first) == _bins(second) == [[("x_g", (1, 2, 3, 4, 5))], [("x_f", (1, 2, 3, 4))],
                                                 [(f"x{SEP}C{SEP}m", (1, 2, 3))]]
        flat = [n for b in first for n in sw.engine_targets(b)]
        assert len(flat) == len(set(flat)) == 12
        assert [sw.engine_targets(b) for b in first] == [sw.engine_targets(b) for b in second]

    def test_the_calibration_scales_a_jobs_share(self) -> None:
        state = _state(f=4, m=3, g=5)
        state["calibration"] = 2.0
        assert _bins(_plan(state, mutants=8)) == [[("x_f", (1, 2, 3, 4))]]

    def test_the_targets_are_the_undecided_mutants_by_name_and_the_window_their_lines(self) -> None:
        """mutmut is handed each undecided mutant by the number it gives it in
        the windowed run (``1`` to the window's size, in the order of its
        lines), never a glob."""
        picks = [sw.Pick(unit=A, lines=(2, 7), counts=(1, 2), before=(1, 4)),
                 sw.Pick(unit=B, lines=(5,), counts=(3,), before=(0,), todo=(2,)),
                 sw.Pick(unit=C, lines=(1,), counts=(1,), before=(0,))]
        assert sw.engine_targets(picks) == ["vera.a.x_f__mutmut_1", "vera.a.x_f__mutmut_2", "vera.a.x_f__mutmut_3",
                                            f"vera.a.x{SEP}C{SEP}m__mutmut_2", "vera.b.x_g__mutmut_1"]
        assert sw.window_lines(picks) == {"vera/a.py": [2, 7, 24], "vera/b.py": [1]}  # B starts at line 20
        assert (picks[0].mutants, [picks[0].line_of(n) for n in (1, 2, 3)]) == (3, [2, 7, 7])
        assert [picks[0].full_number(n) for n in (1, 2, 3)] == [2, 5, 6]
        with pytest.raises(sw.StateError, match="past its window"):
            picks[0].line_of(4)

    def test_a_windows_numbers_map_back_to_mutmuts_over_the_whole_function(
        self, monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        """A window numbers its mutants from one, so a survivor is named by
        the number mutmut gives the mutant in a run over the whole function,
        the mutants on every earlier line counted in, which holds since mutmut
        places a function's mutants in the order of their lines (the engine's
        test of that order in test_mutate_diff.py)."""
        state = _state()
        state["units"][A.ident].update(mutants=9, lines={"2": 3, "5": 2, "9": 4})
        monkeypatch.setattr(sw, "in_sample", lambda cycle, ident, line: line in (5, 9))
        assert sw.window_counts(state, A) == ((5, 9), (2, 4), (3, 5))
        ((pick,),) = sw.plan(state, [A], jobs=1, budget_s=1e9)
        assert pick == sw.Pick(unit=A, lines=(5, 9), counts=(2, 4), before=(3, 5), todo=(1, 2, 3, 4, 5, 6))
        assert [pick.line_of(n) for n in range(1, 7)] == [5, 5, 9, 9, 9, 9]
        assert [pick.full_number(n) for n in range(1, 7)] == [4, 5, 6, 7, 8, 9]
        with pytest.raises(sw.StateError, match="mutant 7 is past its window of 6"):
            pick.full_number(7)

    def test_the_clean_run_is_the_bins_covering_tests(self, monkeypatch: pytest.MonkeyPatch) -> None:
        """mutmut reads its clean run's tests off the names it is handed
        (``tests_for_mutant_names``): a name adds its function's covering
        tests, where a glob, matched against the functions' names, which
        hold no ``__mutmut_``, adds none and leaves the clean run to the
        whole selection, 40 to 80 minutes of each slice (#1838)."""
        pytest.importorskip("mutmut")
        import mutmut.__main__ as engine
        from mutmut.state import state

        record = state().tests_by_mangled_function_name
        monkeypatch.setattr(state(), "tests_by_mangled_function_name", type(record)(set))
        state().tests_by_mangled_function_name.update({
            "vera.a.x_f": {"tests/test_a.py::test_f"}, f"vera.a.x{SEP}C{SEP}m": {"tests/test_a.py::test_m"},
            "vera.b.x_g": {"tests/test_b.py::test_g"}, "vera.a.x_f_twin": {"tests/test_a.py::test_twin"}})
        bins = _plan(_state(f=4, m=3, g=5), jobs=2, mutants=10)
        assert [engine.tests_for_mutant_names(sw.engine_targets(b)) for b in bins] == [
            {"tests/test_b.py::test_g"}, {"tests/test_a.py::test_f", "tests/test_a.py::test_m"}]

    def test_after_a_partial_night_the_plan_names_only_the_undecided(self) -> None:
        """A window partly decided keeps its decided mutants, and the next
        night hands the engine the rest by name and no other: slice 3's
        window of 9 November 2026, `_verify_fn_contracts`, 39 of its 48
        decided and none recorded, planned the same 48 the next night."""
        state = _state(f=6, m=3, g=5)
        state["units"][A.ident]["partial"] = {"decided": {"1": "killed", "2": "killed", "5": "survived"},
                                              "survivors": [{"n": 5, "line": 5, "text_sha": None,
                                                             "status": "survived", "files": None}]}
        _decide(state, B, killed=3)
        (bin_,) = _plan(state, mutants=100)
        assert [(p.unit.key, p.todo) for p in bin_] == [("x_f", (3, 4, 6)), ("x_g", (1, 2, 3, 4, 5))]
        assert sw.engine_targets(bin_) == ["vera.a.x_f__mutmut_3", "vera.a.x_f__mutmut_4", "vera.a.x_f__mutmut_6",
                                           *(f"vera.b.x_g__mutmut_{n}" for n in range(1, 6))]
        assert bin_[0].mutants == 6  # the window mutmut generates is whole: its numbers stay put
        assert sw.sampled_undecided(state, A) == 3 and not sw.complete(state, UNITS)

    def test_the_same_window_planned_twice_gives_the_same_names(self, monkeypatch: pytest.MonkeyPatch) -> None:
        """A number names one mutant on every night of the cycle: the window
        is the unit's sampled lines at its hash, and mutmut numbers its
        mutants from one in the order of those lines."""
        monkeypatch.setattr(sw, "SAMPLE_FRACTION", 0.5)
        state = _state(f=40, m=40, g=40)
        first = [sw.engine_targets(b) for b in _plan(state, jobs=2, mutants=200)]
        state["units"][A.ident]["partial"] = {"decided": {"1": "killed"}, "survivors": []}
        second = [sw.engine_targets(b) for b in _plan(json.loads(json.dumps(state)), jobs=2, mutants=200)]
        assert sorted(n for b in second for n in b) == sorted(n for b in first for n in b if n != "vera.a.x_f__mutmut_1")


def _real_state() -> dict[str, Any]:
    """The committed excerpt of the live schema 2 state of run 42747253700
    (cycle 2, the night of 10 November 2026): every unit whose sampled window
    was still undecided, the 62 windows and 362 mutants the four stuck bins
    held, and every unit of three modules with decided windows."""
    return json.loads((ROOT / "tests" / "fixtures" / "mutation_sweep_state_42747253700_excerpt.json"
                       ).read_text(encoding="utf-8"))


def _units_of(state: dict[str, Any]) -> list[Any]:
    """The state's units in the tree's order, each at its recorded hash."""
    units = [sw.SweepUnit(path=i.split("::")[0], key=i.split("::")[1], start=1, hash=r["hash"])
             for i, r in state["units"].items()]
    return sorted(units, key=lambda u: (u.path, u.key))


class TestTheRealTail:
    """The plan of the night of 11 November 2026, from the live state."""

    @pytest.fixture(autouse=True)
    def _the_committed_sample(self, monkeypatch: pytest.MonkeyPatch) -> None:
        monkeypatch.setattr(sw, "SAMPLE_FRACTION", 0.02)

    def test_the_tail_is_spread_over_every_job_of_the_night(self, tmp_path: Path) -> None:
        path = tmp_path / sw.STATE_FILE
        path.write_text(json.dumps(_real_state()), encoding="utf-8")
        state = sw.load_state(path, "2026-11-11")
        units = _units_of(state)
        bins = sw.plan(state, units, jobs=sw.JOBS, budget_s=sw.DEFAULT_BUDGET_S)
        planned = [p for b in bins for p in b]
        assert (len(planned), sum(p.mutants for p in planned)) == (62, 362)
        assert all(bins), [len(b) for b in bins]  # every job of the night has work
        names = [n for b in bins for n in sw.engine_targets(b)]
        assert len(names) == len(set(names)) == 362
        cost = [sum(len(p.numbers) * sw.rate(p.unit, state["calibration"]) for p in b) for b in bins]
        dearest = max(len(p.numbers) * sw.rate(p.unit, state["calibration"]) for p in planned)
        assert max(cost) - min(cost) <= dearest, cost  # balanced: within one unit of each other

    def test_the_live_schema_two_state_reads_as_schema_three_with_its_totals(self, tmp_path: Path) -> None:
        """The state of 10 November 2026 carries over: no window partly
        decided, every decided window's columns, survivors and mutants as
        they were, so the cycle goes on where it stood, and the stitch notes
        the conversion once."""
        raw = _real_state()
        assert raw["schema"] == 2
        path = tmp_path / sw.STATE_FILE
        path.write_text(json.dumps(raw), encoding="utf-8")
        state = sw.load_state(path, "2026-11-11")
        assert state["schema"] == 3 and state["converted_from"] == 2
        assert {k: v for k, v in state.items() if k not in ("schema", "units", "converted_from")} == {
            k: v for k, v in raw.items() if k not in ("schema", "units")}
        units = _units_of(state)
        before: dict[str, dict[str, int]] = {}
        for ident, rec in raw["units"].items():
            row = before.setdefault(ident.split("::")[0], dict.fromkeys((*sw.COLUMNS_2, "mutants"), 0))
            row["mutants"] += rec["mutants"] or 0
            for column in sw.COLUMNS_2:
                row[column] += (rec["window"] or {}).get(column, 0)
        after = sw.tally(state, units)
        assert {m: {k: v for k, v in row.items() if k != "slow"} for m, row in after.items()} == before
        assert all(row["slow"] == 0 for row in after.values())
        assert all(r["partial"] is None for r in state["units"].values())
        for ident, rec in raw["units"].items():
            if rec["window"] is not None:
                assert [f"{s['n']}@{s['line']}:{s['status']}" for s in state["units"][ident]["window"]["survivors"]
                        ] == rec["window"]["survivors"]
        decided = sum(1 for r in state["units"].values() if r["window"] is not None)
        raw_decided = sum(1 for r in raw["units"].values() if r["window"] is not None)
        assert decided == raw_decided and sum(sw.sampled_undecided(state, u) or 0 for u in units) == 362
        written, night = sw.stitch(state, sw.state_digest(path), [], jobs=sw.JOBS, head=HEAD, units=units,
                                   today="2026-11-11")
        assert "converted_from" not in written and "the state was schema 2, which decided a window whole: its " \
            "decided windows carry over, and from tonight each mutant is kept as it is decided" in night["notes"]
        assert sw.load_state(sw.save_state(written, tmp_path / "out"), "x") == written

    def test_the_first_schema_three_night_that_decides_nothing_is_not_the_second(self, tmp_path: Path) -> None:
        """The live state's last night line, 10 November 2026, reads `moved 0`
        under schema 2's whole-window count though its engines decided
        mutants, so it cannot be the first of two empty nights: the first
        schema 3 night that decides nothing is weather, and only the next
        one, after a line schema 3 wrote, is red."""
        raw = _real_state()
        assert raw["nights"][-1]["moved"] == 0 and "schema" not in raw["nights"][-1]
        path = tmp_path / sw.STATE_FILE
        path.write_text(json.dumps(raw), encoding="utf-8")
        state = sw.load_state(path, "2026-11-11")
        units = _units_of(state)
        bins = sw.plan(state, units, jobs=sw.JOBS, budget_s=sw.DEFAULT_BUDGET_S)
        digest = sw.state_digest(path)

        def stopped(n: int) -> dict[str, Any]:
            return {**_record(n, sw.JOBS, {}, digest=digest, stopped="budget", counts={}),
                    "planned": [{"unit": p.unit.ident} for p in bins[n]]}

        first, night = sw.stitch(state, digest, [stopped(n) for n in range(sw.JOBS)], jobs=sw.JOBS, head=HEAD,
                                 units=units, today="2026-11-11")
        assert night["problems"] == [] and night["moved"] == 0 and night["schema"] == 3
        path.write_text(json.dumps(first), encoding="utf-8")
        digest = sw.state_digest(path)
        _, night = sw.stitch(sw.load_state(path, "x"), digest, [stopped(n) for n in range(sw.JOBS)], jobs=sw.JOBS,
                             head=HEAD, units=units, today="2026-11-12")
        assert night["problems"] == ["the night decided no mutant, and neither did the night before it"]


# ---------------------------------------------------------------------------
# The sample, and the counts it is drawn over
# ---------------------------------------------------------------------------


class TestSample:
    """Each line a unit's mutants sit on is in a cycle's sample by a hash of
    the cycle, the unit and the line, ``SAMPLE_FRACTION`` of them, with every
    mutant on it, so every job of a night and every night of the cycle draw
    the same sample, each mutant in it with the same chance, and the next
    cycle draws another."""

    def test_the_committed_share_is_two_percent(self) -> None:
        assert _load().SAMPLE_FRACTION == 0.02  # the suite's fixture sets 1.0 on the loaded module

    def test_the_draw_is_the_same_everywhere_and_the_fractions_share(self, monkeypatch: pytest.MonkeyPatch) -> None:
        monkeypatch.setattr(sw, "SAMPLE_FRACTION", 0.02)
        drawn = [line for line in range(1, 20001) if sw.in_sample(1, A.ident, line)]
        assert drawn == [line for line in range(1, 20001) if sw.in_sample(1, A.ident, line)]
        assert 0.015 <= len(drawn) / 20000 <= 0.025, len(drawn)
        monkeypatch.setattr(sw, "SAMPLE_FRACTION", 0.0)
        assert not any(sw.in_sample(1, A.ident, line) for line in range(1, 1001))

    def test_the_next_cycle_and_another_unit_draw_other_samples(self, monkeypatch: pytest.MonkeyPatch) -> None:
        monkeypatch.setattr(sw, "SAMPLE_FRACTION", 0.5)
        first = {line for line in range(1, 2001) if sw.in_sample(1, A.ident, line)}
        second = {line for line in range(1, 2001) if sw.in_sample(2, A.ident, line)}
        assert 900 <= len(first) <= 1100 and 900 <= len(second) <= 1100
        assert 400 <= len(first & second) <= 600  # two halves drawn apart share about a quarter
        assert {line for line in range(1, 2001) if sw.in_sample(1, C.ident, line)} != first

    def test_a_units_window_is_its_sampled_lines_with_every_mutant_on_them(self, monkeypatch: pytest.MonkeyPatch) -> None:
        monkeypatch.setattr(sw, "SAMPLE_FRACTION", 0.5)
        assert sw.sampled_lines(_state(), A) is None and sw.sampled_undecided(_state(), A) is None
        assert sw.sampled_lines(_state(f=0), A) == [] and sw.sampled_undecided(_state(f=0), A) == 0
        state = _state(f=100)
        state["units"][A.ident]["lines"] = {str(line): line % 3 + 1 for line in range(1, 101)}
        lines = sw.sampled_lines(state, A)
        assert lines and lines == sorted(set(lines)) and all(1 <= line <= 100 for line in lines)
        drawn, counts, before = sw.window_counts(state, A)
        assert drawn == tuple(lines) and counts == tuple(line % 3 + 1 for line in lines)
        assert sw.sampled_undecided(state, A) == sum(counts)
        _decide(state, A, killed=sum(counts))
        assert sw.sampled_undecided(state, A) == 0 and sw.window_counts(state, A) == (drawn, counts, before)


COUNTER = '''
import json, os, sys
if sys.argv[1:] == ["--version"]:
    print("mutmut, version 3.8.1")
    sys.exit(0)
if sys.argv[1:] != ["count"]:
    sys.exit(9)
if os.environ.get("COUNTER_EXIT"):
    print("the visitor is not there", file=sys.stderr)
    sys.exit(int(os.environ["COUNTER_EXIT"]))
if os.environ.get("COUNTER_SLEEP"):
    import time
    time.sleep(float(os.environ["COUNTER_SLEEP"]))
request = json.load(sys.stdin)
with open(os.environ["COUNTER_SEEN"], "w", encoding="utf-8") as fh:
    json.dump(request, fh)
reply = os.environ.get("COUNTER_REPLY")
def start(k):  # the file's line the unit starts on: the test units' B (a method) at 20, the rest at 1
    return 20 if k.startswith("xǁ") else 1
print(reply if reply else json.dumps({p: {k: {"mutants": len(k), "lines": {str(start(k)): len(k) - 1,
                                                                            str(start(k) + 8): 1}} for k in keys}
                                      for p, keys in request["units"].items()}))
'''


class TestCounts:
    """A unit's mutant count is mutmut's own visitor's, asked through the
    engine's ``count`` command for the units the state holds uncounted."""

    def _engine(self, tmp_path: Path) -> list[str]:
        script = tmp_path / "counter.py"
        script.write_text(COUNTER, encoding="utf-8")
        return [sys.executable, str(script)]

    def test_the_uncounted_units_are_counted_by_file_and_the_rest_left_alone(
        self, tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        seen = tmp_path / "seen.json"
        monkeypatch.setenv("COUNTER_SEEN", str(seen))
        state = _state(f=4)
        sources = {"vera/a.py": "a", "vera/b.py": "b", "vera/c.py": "c"}
        assert sw.uncounted(state, UNITS) == [B, C]
        counts = sw.engine_counts(self._engine(tmp_path), os.environ, sources, [B, C])
        assert counts == {B.ident: {"mutants": 5, "lines": {"1": 4, "9": 1}},
                          C.ident: {"mutants": 3, "lines": {"1": 2, "9": 1}}}
        assert json.loads(seen.read_text(encoding="utf-8")) == {
            "sources": {"vera/a.py": "a", "vera/b.py": "b"},
            "units": {"vera/a.py": [B.key], "vera/b.py": ["x_g"]}}
        sw.apply_counts(state, counts)
        assert sw.uncounted(state, UNITS) == []
        assert state["units"][C.ident] == {"hash": H, "mutants": 3, "lines": {"1": 2, "9": 1}, "window": None,
                                           "partial": None}
        assert sw.engine_counts(self._engine(tmp_path), os.environ, sources, []) == {}

    def test_a_mutant_the_engine_places_above_the_units_first_line_fails_the_lane(
        self, tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        """The state numbers a unit's lines from its first, so a line the
        file numbers below the unit's start has no number there."""
        monkeypatch.setenv("COUNTER_SEEN", str(tmp_path / "seen.json"))
        monkeypatch.setenv("COUNTER_REPLY", json.dumps({"vera/a.py": {B.key: {"mutants": 1, "lines": {"5": 1}}}}))
        with pytest.raises(sw.md.LaneError, match="on line 5, above its first line 20"):
            sw.engine_counts(self._engine(tmp_path), os.environ, {"vera/a.py": "a"}, [B])

    @pytest.mark.parametrize("env,why", [
        ({"COUNTER_EXIT": "4"}, "could not count"),
        ({"COUNTER_REPLY": "not json"}, "is not JSON"),
        ({"COUNTER_REPLY": '{"vera/b.py": {}}'}, "missing or malformed"),
        ({"COUNTER_REPLY": '{"vera/b.py": {"x_g": {"mutants": -1, "lines": {}}}}'}, "missing or malformed"),
        ({"COUNTER_REPLY": '{"vera/b.py": {"x_g": {"mutants": 3, "lines": {"1": 2}}}}'}, "do not sum"),
        ({"COUNTER_REPLY": '{"vera/b.py": {"x_g": {"mutants": 1, "lines": {"0": 1}}}}'}, "out of range"),
        ({"COUNTER_REPLY": '{"vera/b.py": {"x_g": 3}}'}, "missing or malformed"),
        ({"COUNTER_REPLY": "[]"}, "missing or malformed"),
    ])
    def test_a_count_the_engine_cannot_give_fails_the_lane(
        self, env: dict[str, str], why: str, tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        for key, value in env.items():
            monkeypatch.setenv(key, value)
        monkeypatch.setenv("COUNTER_SEEN", str(tmp_path / "seen.json"))
        with pytest.raises(sw.md.LaneError, match=why):
            sw.engine_counts(self._engine(tmp_path), os.environ, {"vera/b.py": "b"}, [C])

    def test_a_count_that_does_not_finish_fails_the_lane(self, tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
        monkeypatch.setenv("COUNTER_SLEEP", "10")
        monkeypatch.setenv("COUNTER_SEEN", str(tmp_path / "seen.json"))
        monkeypatch.setattr(sw, "COUNT_TIMEOUT_S", 0.5)
        with pytest.raises(sw.md.LaneError, match="did not finish"):
            sw.engine_counts(self._engine(tmp_path), os.environ, {"vera/b.py": "b"}, [C])


# ---------------------------------------------------------------------------
# A slice's results, and the stitch
# ---------------------------------------------------------------------------


# Window mutant 1 on line 3 (two mutants on earlier lines), 2 and 3 on line 7 (three earlier).
PICK_A = sw.Pick(unit=A, lines=(3, 7), counts=(1, 2), before=(2, 3))
PICK_C = sw.Pick(unit=C, lines=(5,), counts=(1,), before=(0,))
GENERATED = {("vera/a.py", "x_f"): (10, 3), ("vera/b.py", "x_g"): (4, 1)}  # held in all, in the window


def _survivor(n: int, line: int, status: str, text_sha: str | None = None,
              files: list[str] | None = None) -> dict[str, Any]:
    return {"n": n, "line": line, "text_sha": text_sha, "status": status, "files": files}


class TestSliceResults:
    def test_each_mutant_is_decided_and_its_survivors_sit_on_their_lines(self) -> None:
        out = sw.slice_results([PICK_A, PICK_C], {
            "vera.a.x_f__mutmut_1": "killed", "vera.a.x_f__mutmut_2": "survived", "vera.a.x_f__mutmut_3": "timeout",
            "vera.b.x_g__mutmut_1": "no tests"}, GENERATED, cut_short=False, finished=True,
            line_text=lambda unit, line: f"line {line} of {unit.key}",
            files={A.ident: ["tests/test_a.py", "tests/test_b.py"]},
            seconds={"vera.a.x_f__mutmut_1": (1.25, 3.0), "vera.a.x_f__mutmut_2": (40.0, 3.0)})
        assert out == {
            A.ident: {"hash": H, "window": 3, "lines": [3, 7],
                      "decided": {"1": "killed", "2": "survived", "3": "timeout"},
                      "survivors": [_survivor(4, 7, "survived", sw.line_hash("line 7 of x_f"),
                                              ["tests/test_a.py", "tests/test_b.py"]),
                                    _survivor(5, 7, "timeout", sw.line_hash("line 7 of x_f"),
                                              ["tests/test_a.py", "tests/test_b.py"])],
                      "durations": {"1": 1.25, "2": 40.0}, "estimates": {"1": 3.0, "2": 3.0}},
            C.ident: {"hash": H, "window": 1, "lines": [5], "decided": {"1": "no tests"}, "survivors": [],
                      "durations": {}, "estimates": {}}}
        for result in out.values():
            sw.check_record(_record(0, 1, {A.ident: result}, counts={}))

    def test_a_partial_windows_decided_mutants_are_kept(self) -> None:
        """mutmut runs a bin's cheapest mutants first, across the bin, so a
        budget stop leaves windows partly decided; each decided mutant is
        kept, and only the undecided wait (#1838: slice 1 decided 13 to 21
        of its mutants on three nights and recorded none)."""
        listing = {"vera.a.x_f__mutmut_1": "killed", "vera.a.x_f__mutmut_2": "not checked",
                   "vera.a.x_f__mutmut_3": "check was interrupted by user", "vera.b.x_g__mutmut_1": "killed"}
        out = sw.slice_results([PICK_A, PICK_C], listing, GENERATED, cut_short=True, finished=False)
        assert {i: r["decided"] for i, r in out.items()} == {A.ident: {"1": "killed"}, C.ident: {"1": "killed"}}

    def test_only_the_numbers_handed_to_the_engine_are_read(self) -> None:
        """A mutant an earlier night decided is not named tonight, so mutmut
        leaves it `not checked`, and a status for it is not read."""
        pick = sw.Pick(unit=A, lines=(3, 7), counts=(1, 2), before=(2, 3), todo=(3,))
        listing = {"vera.a.x_f__mutmut_1": "killed", "vera.a.x_f__mutmut_2": "not checked",
                   "vera.a.x_f__mutmut_3": "survived"}
        out = sw.slice_results([pick], listing, GENERATED, cut_short=False, finished=True)
        assert out[A.ident]["decided"] == {"3": "survived"} and [s["n"] for s in out[A.ident]["survivors"]] == [5]

    def test_a_status_a_budget_stop_can_leave_waits_for_a_run_it_did_not_stop(self) -> None:
        listing = {"vera.a.x_f__mutmut_1": "segfault", "vera.a.x_f__mutmut_2": "suspicious",
                   "vera.a.x_f__mutmut_3": "timeout"}
        stopped = sw.slice_results([PICK_A], listing, GENERATED, cut_short=True, finished=False)
        assert stopped[A.ident]["decided"] == {"3": "timeout"}  # the segfault and suspicious are the stop's
        decided = sw.slice_results([PICK_A], listing, GENERATED, cut_short=False, finished=True)[A.ident]
        assert decided["decided"] == {"1": "segfault", "2": "suspicious", "3": "timeout"}
        assert decided["survivors"] == [_survivor(5, 7, "timeout")]  # the window's mutant 3, the fifth of the unit

    def test_a_mutant_the_cap_ended_is_slow_and_one_interrupted_otherwise_waits(self) -> None:
        """The oracle plugin's file names each mutant it ended at the cap:
        a mutant the engine left undecided that the file names is `slow`
        (mutmut reads the plugin's exit 2 as interrupted).  One the engine
        marks interrupted that the file does not name is undecided: never
        slow, never caught.  The timer cannot be withdrawn once its wait has
        returned, so a run can end with its own verdict after the plugin
        named it: that verdict stands."""
        listing = {"vera.a.x_f__mutmut_1": "check was interrupted by user",
                   "vera.a.x_f__mutmut_2": "check was interrupted by user", "vera.a.x_f__mutmut_3": "killed"}
        out = sw.slice_results([PICK_A], listing, GENERATED, cut_short=False, finished=True,
                               slow={"vera.a.x_f__mutmut_1", "vera.a.x_f__mutmut_3"})
        assert out[A.ident]["decided"] == {"1": "slow", "3": "killed"}  # killed and named stays killed
        assert out[A.ident]["survivors"] == [_survivor(3, 3, "slow")]
        for engine in ("survived", "timeout", "no tests"):
            done = sw.slice_results([PICK_A], {**listing, "vera.a.x_f__mutmut_1": engine}, GENERATED,
                                    cut_short=False, finished=True, slow={"vera.a.x_f__mutmut_1"})
            assert done[A.ident]["decided"]["1"] == engine
        stopped = sw.slice_results([PICK_A], {**listing, "vera.a.x_f__mutmut_1": "not checked"}, GENERATED,
                                   cut_short=True, finished=False, slow={"vera.a.x_f__mutmut_1"})
        assert stopped[A.ident]["decided"] == {"1": "slow", "3": "killed"}  # the cap ended it before the stop

    def test_the_slow_file_is_read_by_its_first_field(self, tmp_path: Path) -> None:
        path = tmp_path / "slow.txt"
        assert sw.slow_mutants(path) == set()
        path.write_text("vera.a.x_f__mutmut_1\t2400.3\n\nvera.b.x_g__mutmut_2\t2401.0\n", encoding="utf-8")
        assert sw.slow_mutants(path) == {"vera.a.x_f__mutmut_1", "vera.b.x_g__mutmut_2"}

    def test_the_meta_and_stats_files_give_durations_estimates_and_test_files(self, tmp_path: Path) -> None:
        (tmp_path / "mutants" / "vera").mkdir(parents=True)
        (tmp_path / "mutants" / "vera" / "a.py.meta").write_text(json.dumps({
            "exit_code_by_key": {}, "durations_by_key": {"vera.a.x_f__mutmut_1": 2.5},
            "estimated_durations_by_key": {"vera.a.x_f__mutmut_1": 1.0, "vera.a.x_f__mutmut_2": 1.0}}),
            encoding="utf-8")
        assert sw.mutant_seconds(tmp_path, ["vera/a.py", "vera/b.py"]) == {
            "vera.a.x_f__mutmut_1": (2.5, 1.0), "vera.a.x_f__mutmut_2": (None, 1.0)}
        stats = tmp_path / "mutants" / "mutmut-stats.json"
        stats.write_text(json.dumps({"tests_by_mangled_function_name": {
            "vera.a.x_f": ["tests/test_a.py::test_1", "mutants/tests/test_a.py::test_2", "tests/test_b.py::C::t"]}}),
            encoding="utf-8")
        assert sw.tested_files(stats) == {"vera.a.x_f": ["tests/test_a.py", "tests/test_b.py"]}
        assert sw.tested_files(tmp_path / "absent.json") == {}

    def test_a_window_the_engine_generated_otherwise_than_counted_is_refused(self) -> None:
        listing = {"vera.a.x_f__mutmut_1": "killed", "vera.a.x_f__mutmut_2": "killed"}
        with pytest.raises(sw.StateError, match="generated 2 mutants of vera/a.py::x_f where its window holds 3"):
            sw.slice_results([PICK_A], listing, {("vera/a.py", "x_f"): (10, 2)}, cut_short=False, finished=True)
        with pytest.raises(sw.StateError, match="did not count vera/a.py::x_f's window"):
            sw.slice_results([PICK_A], listing, {}, cut_short=False, finished=True)
        assert sw.slice_results([PICK_A], {}, {}, cut_short=True, finished=False) == {}  # stopped before its file

    def test_a_listing_short_of_the_window_or_with_a_gap_is_refused(self) -> None:
        with pytest.raises(sw.StateError, match="listed 2 mutants of vera/a.py::x_f where the window holds 3"):
            sw.slice_results([PICK_A], {"vera.a.x_f__mutmut_1": "killed", "vera.a.x_f__mutmut_3": "killed"},
                             GENERATED, cut_short=False, finished=True)
        with pytest.raises(sw.StateError, match="listed nothing for vera/a.py::x_f's 3 mutants"):
            sw.slice_results([PICK_A], {}, GENERATED, cut_short=False, finished=True)
        empty = sw.Pick(unit=B, lines=(), counts=(), before=())
        out = sw.slice_results([empty], {}, {("vera/a.py", B.key): (6, 0)}, cut_short=False, finished=True)
        assert out[B.ident]["window"] == 0 and out[B.ident]["lines"] == []

    def test_a_result_for_a_function_the_night_did_not_plan_is_refused(self) -> None:
        with pytest.raises(sw.StateError, match="did not plan"):
            sw.slice_results([PICK_A], {"vera.b.x_g__mutmut_1": "killed"}, GENERATED, cut_short=False, finished=True)


def _record(slice_: int, of: int, results: dict[str, Any], *, head: str = HEAD,
            digest: str = "none", stopped: str | None = None, planned: int = 1,
            counts: dict[str, Any] | None = None) -> dict[str, Any]:
    """A slice's record; its counts, unless given, are the ones its results
    imply (one mutant a line over each window's lines), as a slice counts
    before it plans."""
    if counts is None:
        counts = {ident: {"mutants": r["window"], "lines": {str(line): 1 for line in r["lines"]}}
                  for ident, r in results.items() if isinstance(r, dict) and isinstance(r.get("lines"), list)}
    return {"schema": sw.SCHEMA, "slice": slice_, "of": of, "head": head, "state_in": digest,
            "engine": "3.8.0", "budget_s": 100.0, "planned": [{"unit": "u"}] * planned,
            "counts": counts, "results": results, "stopped": stopped, "engine_s": sw.FIXED_S + 10.0,
            "dropped_tests": [], "deselected_tests": [], "subprocess_tests": [], "source_tests": []}


def _night_line(date: str, lost: list[int] | None = None) -> dict[str, Any]:
    """A night's line as the stitch writes it; ``lost`` absent is a line from
    before the field, as a state an earlier version kept has them."""
    line: dict[str, Any] = {"date": date, "head": HEAD, "jobs": 2, "moved": 0, "slices": [],
                            "problems": [], "notes": [], "closed": False}
    if lost is not None:
        line["lost"] = lost
    return line


def _stitch(records: list[dict[str, Any]], state: dict[str, Any] | None = None, *, jobs: int = 2,
            ) -> tuple[dict[str, Any], dict[str, Any]]:
    return sw.stitch(state or sw.empty_state("2026-10-16"), "none", records, jobs=jobs, head=HEAD,
                     units=UNITS, today="2026-10-17")


class TestStitch:
    def test_the_nights_slices_fold_into_the_state(self) -> None:
        state, night = _stitch([
            _record(0, 2, {A.ident: _res(A, killed=2, survived=2, survivors=("3@3:survived", "4@4:survived"))}),
            _record(1, 2, {C.ident: _res(C, killed=2)}),
        ])
        assert night["problems"] == [] and night["moved"] == 6  # the decided mutants
        assert state["units"][A.ident] == {
            "hash": H, "mutants": 4, "lines": _lines(4),
            "window": _window(killed=2, survived=2, survivors=("3@3:survived", "4@4:survived")), "partial": None}
        assert state["units"][C.ident]["window"] == _window(killed=2) and state["units"][B.ident]["lines"] is None
        assert state["nights"][-1] is night

    def test_a_slice_of_another_head_or_another_state_stops_the_night_short(self) -> None:
        good = _record(0, 2, {A.ident: _res(A, killed=4)})
        _, night = _stitch([good, _record(1, 2, {}, head="e" * 40)])
        assert any("ran eeee" in p for p in night["problems"])
        assert night["lost"] == [] and night["notes"] == []  # it reported; a rejected record is not a lost slice
        _, night = _stitch([good, _record(1, 2, {}, digest="f" * 64)])
        assert any("another state" in p for p in night["problems"])
        assert night["lost"] == [] and night["notes"] == []

    def test_a_missing_slice_is_noted_and_its_work_waits_for_the_next_night(self) -> None:
        """A slice with no record is one whose job ended before it uploaded
        anything: a hosted runner taken away under it (the nights of 19 and
        20 October 2026, #1751).  The night keeps what the other slices
        decided, says so, and stays green; the lost slice's work is planned
        again the next night."""
        state, night = _stitch([_record(0, 2, {A.ident: _res(A, killed=4)})])
        assert night["problems"] == [] and night["lost"] == [1]
        assert night["notes"] == ["slice 1: no record; its work waits for the next night"]
        assert state["units"][A.ident]["window"]["killed"] == 4 and state["nights"][-1]["lost"] == [1]
        assert "no record" in sw.render_night(state, night, UNITS)

    def test_two_missing_slices_in_a_night_are_weather_and_a_third_stops_it_short(self) -> None:
        """A hosted runner is lost under about 7% of the sweep's 4.5-hour
        jobs, so two of seven in a night is within the weather; three is an
        outage (#1827)."""
        good = _record(0, 4, {A.ident: _res(A, killed=4)})
        _, night = _stitch([good, _record(3, 4, {})], jobs=4)
        assert night["lost"] == [1, 2] and night["problems"] == []
        assert night["notes"] == ["slice 1: no record; its work waits for the next night",
                                  "slice 2: no record; its work waits for the next night"]
        _, night = _stitch([good], jobs=4)
        assert night["lost"] == [1, 2, 3]
        assert night["problems"] == ["no record from slices 1, 2 and 3: more than 2 in a night"]

    def test_a_lane_that_failed_before_planning_is_reported_whatever_its_head_or_state(self) -> None:
        """A step before the sweep that fails while the runner is still there
        writes a lane record (the workflow's `lane-failed` step), which may
        carry no head and a state digest of none: it planned nothing and
        holds no result, so there is nothing for those to be wrong about, and
        the stitch reports the lane and its reason."""
        good = _record(0, 2, {A.ident: _res(A, killed=4)})
        failed = _record(1, 2, {}, stopped="lane", digest="f" * 64, planned=0)
        failed["head"], failed["engine"], failed["engine_tail"] = None, None, ["a step before the sweep failed"]
        state, night = _stitch([good, failed])
        assert night["problems"] == ["slice 1: stopped by the lane: a step before the sweep failed"]
        assert night["lost"] == [] and state["units"][A.ident]["window"]["killed"] == 4

    def test_a_night_whose_plan_sat_in_the_lost_slice_is_not_a_night_that_planned_nothing(self) -> None:
        state = _state(f=4)  # work remains, and slice 0, which held it, sent no record
        _, night = _stitch([_record(1, 2, {}, planned=0)], state)
        assert night["lost"] == [0] and night["problems"] == []

    def test_lost_slices_over_many_nights_are_weather(self) -> None:
        """Four lost slices over seven nights is the expected count at the
        measured rate, not a hazard (#1827): only a night's own count can
        stop it short, and a night line from before the field counts none."""
        good = _record(0, 2, {A.ident: _res(A, killed=4)})
        state = sw.empty_state("2026-10-10")
        state["nights"] = [_night_line(f"2026-10-1{d}", [d % 2]) for d in range(1, 7)]
        _, night = _stitch([good], json.loads(json.dumps(state)))
        assert night["lost"] == [1] and night["problems"] == []
        state["nights"] = [_night_line(f"2026-10-{d:02d}") for d in range(1, 10)]
        _, night = _stitch([good], json.loads(json.dumps(state)))
        assert night["lost"] == [1] and night["problems"] == []

    def test_a_slice_its_engine_stopped_stops_the_night_short_and_its_results_still_count(self) -> None:
        state, night = _stitch([
            _record(0, 2, {A.ident: _res(A, killed=4)}),
            _record(1, 2, {}, stopped="engine")])
        assert night["problems"] == ["slice 1: stopped by the engine"]
        assert state["units"][A.ident]["window"]["killed"] == 4

    def test_the_engines_own_exception_is_named_in_the_nights_problems_and_reports(self) -> None:
        """A slice whose engine raised in its own code names the exception
        and the engine's frame, and the night's line and report carry it
        (the tracking issue links the stitch's report)."""
        failed = _record(1, 2, {}, stopped="engine")
        failed["engine_error"] = ENGINE_ERROR
        state, night = _stitch([
            _record(0, 2, {A.ident: _res(A, killed=4)}), failed])
        assert night["problems"] == [f"slice 1: stopped by the engine: {ENGINE_ERROR}"]
        assert f"- slice 1: stopped by the engine: {ENGINE_ERROR}" in sw.render_night(state, night, UNITS)
        assert f"Stopped by the engine: `{ENGINE_ERROR}`." in sw.render_slice(failed)
        assert "Stopped by the engine.\n" in sw.render_slice(_record(1, 2, {}, stopped="engine"))

    def test_two_nights_in_a_row_that_decide_nothing_stop_short_and_one_does_not(self) -> None:
        """One night that decides nothing is weather (a bin of slow mutants,
        a lost runner) and keeps what it has; a second in a row measures
        nothing, and is red.  Survivors never are."""
        state = _state(f=4)
        first, night = _stitch([_record(0, 1, {})], state, jobs=1)
        assert night["problems"] == [] and night["moved"] == 0
        _, night = _stitch([_record(0, 1, {})], json.loads(json.dumps(first)), jobs=1)
        assert night["problems"] == ["the night decided no mutant, and neither did the night before it"]
        decided, night = _stitch([_record(0, 1, {A.ident: _res(A, window=4, killed=1)})],
                                 json.loads(json.dumps(first)), jobs=1)
        assert night["problems"] == [] and night["moved"] == 1
        _, night = _stitch([_record(0, 1, {})], json.loads(json.dumps(decided)), jobs=1)
        assert night["problems"] == []  # the night before decided a mutant
        lost = json.loads(json.dumps(state))
        lost["nights"] = [{**_night_line("2026-11-09", [0]), "moved": 0, "schema": 3}]
        _, night = _stitch([_record(0, 1, {})], lost, jobs=1)
        assert night["problems"] == ["the night decided no mutant, and neither did the night before it"]
        # Counting a function with no mutant decides it: a night whose plan
        # was empty because the counts left nothing to run closes the cycle.
        state = _state(f=4)
        _decide(state, A, killed=4)
        counted = _record(0, 1, {}, planned=0,
                          counts={B.ident: {"mutants": 0, "lines": {}}, C.ident: {"mutants": 0, "lines": {}}})
        _, night = _stitch([counted], state, jobs=1)
        assert night["problems"] == [] and night["closed"]
        _, night = _stitch([_record(0, 1, {A.ident: _res(A, survived=4, survivors=tuple(
            f"{n}@{n}:survived" for n in range(1, 5)))})], jobs=1)
        assert night["problems"] == []

    def test_a_slices_counts_fold_into_the_state_and_a_disagreement_stops_the_night_short(self) -> None:
        """Every slice counts the uncounted units with the same engine at the
        same head, so the counts agree; one that does not, or one for a
        function the tree does not hold, is a problem."""
        state = _state(f=4)
        counted = _record(0, 2, {A.ident: _res(A, killed=4)})
        counted["counts"] = {B.ident: {"mutants": 3, "lines": _lines(3)}, C.ident: {"mutants": 0, "lines": {}}}
        other = _record(1, 2, {})
        other["counts"] = {B.ident: {"mutants": 3, "lines": _lines(3)}}
        merged, night = _stitch([counted, other], json.loads(json.dumps(state)))
        assert night["problems"] == []
        assert (merged["units"][B.ident]["lines"], merged["units"][C.ident]["mutants"]) == (_lines(3), 0)
        other["counts"] = {B.ident: {"mutants": 3, "lines": {"1": 1, "2": 2}},
                           "vera/z.py::x_q": {"mutants": 1, "lines": {"1": 1}}}
        _, night = _stitch([counted, other], json.loads(json.dumps(state)))
        assert night["problems"] == [f"slice 1 counted 3 mutants of {B.ident} where the state holds 3, "
                                     "or on other lines",
                                     "slice 1 counted vera/z.py::x_q, which the tree does not hold"]

    def test_nights_whose_only_planned_slice_was_lost_are_empty_nights_too(self) -> None:
        """A night whose every planned slice sent no record decided nothing
        as surely as one whose slices did: the second such night in a row is
        red, so losing the one working slice cannot stay green for ever."""
        state = _state(f=4)
        first, night = _stitch([_record(1, 2, {}, planned=0)], state)
        assert night["lost"] == [0] and night["problems"] == []
        _, night = _stitch([_record(1, 2, {}, planned=0)], json.loads(json.dumps(first)))
        assert night["problems"] == ["the night decided no mutant, and neither did the night before it"]

    def test_a_budget_stop_is_a_normal_stop_and_its_partial_work_is_kept(self) -> None:
        """The rule "its budget ran out before its first mutant" fired on
        nine slice-nights of 7 to 10 November 2026 whose engines had decided
        9 to 39 mutants each, in windows none of which was whole (#1838).  A
        budget stop keeps each mutant it decided, the night notes it, and it
        is no problem, decided or not."""
        good = _record(0, 2, {A.ident: _res(A, killed=4)})
        partial = _record(1, 2, {C.ident: _res(C, window=5, killed=1, survived=1, survivors=("4@4:survived",))},
                          stopped="budget", counts={C.ident: {"mutants": 5, "lines": _lines(5)}})
        state, night = _stitch([good, partial])
        assert night["problems"] == [] and night["moved"] == 6
        assert night["notes"] == ["slice 1: stopped by the budget with 2 mutant(s) decided; the rest of its bin "
                                  "waits for the next night"]
        assert state["units"][C.ident]["window"] is None
        assert state["units"][C.ident]["partial"] == {"decided": {"1": "killed", "4": "survived"},
                                                      "survivors": [_survivor(4, 4, "survived")]}
        assert sw.slice_exit(partial) == 0
        _, night = _stitch([good, _record(1, 2, {}, stopped="budget")])
        assert night["problems"] == [] and sw.slice_exit(_record(1, 2, {}, stopped="budget")) == 0

    def test_a_partial_window_is_completed_by_a_later_record_and_no_mutant_counts_twice(self) -> None:
        """The window's decided mutants gather night by night, a mutant
        decided twice counting once, and fold into a decided window with the
        last one."""
        state = _state(f=4)
        first = _record(0, 1, {A.ident: _res(A, window=4, killed=1, survivors=("3@3:survived",), survived=1)},
                        stopped="budget", counts={})
        state, night = _stitch([first], state, jobs=1)
        assert night["moved"] == 2 and state["units"][A.ident]["partial"]["decided"] == {"1": "killed",
                                                                                          "3": "survived"}
        assert sw.undecided_numbers(state, A) == (2, 4)
        second = {"hash": H, "window": 4, "lines": [1, 2, 3, 4], "survivors": [_survivor(4, 4, "slow")],
                  "decided": {"1": "killed", "2": "killed", "4": "slow"}, "durations": {}, "estimates": {}}
        state, night = _stitch([_record(0, 1, {A.ident: second}, counts={})], json.loads(json.dumps(state)), jobs=1)
        assert night["moved"] == 2  # mutant 1 again counts once
        assert state["units"][A.ident]["partial"] is None
        assert state["units"][A.ident]["window"] == {
            "killed": 2, "survived": 1, "timeout": 0, "no_tests": 0, "slow": 1, "other": 0, "mutants": 4,
            "survivors": [_survivor(3, 3, "survived"), _survivor(4, 4, "slow")]}

    def test_the_cycle_closes_when_its_sample_is_decided_whatever_else_the_night_did(self) -> None:
        """Only validated records merge, so a lost or failed slice cannot
        close a cycle wrongly; a night with a problem that decides the last
        mutant closes it."""
        state = _state(f=4)
        _, night = _stitch([_record(0, 3, {A.ident: _res(A, killed=4)}), _record(1, 3, {}, stopped="engine")],
                           state, jobs=3)
        assert night["problems"] == ["slice 1: stopped by the engine"] and night["lost"] == [2]
        assert not night["closed"]  # m and g are uncounted
        state = _state(f=4, m=0, g=0)
        _, night = _stitch([_record(0, 3, {A.ident: _res(A, killed=4)}), _record(1, 3, {}, stopped="engine")],
                           state, jobs=3)
        assert night["problems"] == ["slice 1: stopped by the engine"] and night["closed"]

    def test_a_night_whose_every_slice_failed_keeps_the_state(self) -> None:
        """A slice whose lane failed records no engine version; a night of
        them must not read that as a new engine and start every function
        afresh."""
        state = _state(f=4)
        _decide(state, A, killed=4)
        failed = _record(0, 1, {}, stopped="lane")
        failed["engine"] = None
        state["cycle_started"] = "2026-10-01"
        kept, night = _stitch([failed], json.loads(json.dumps(state)), jobs=1)
        assert night["problems"] == ["slice 0: stopped by the lane"] and night["notes"] == []
        assert kept["engine"] == "3.8.0" and kept["cycle_started"] == "2026-10-01"
        assert kept["units"][A.ident] == {"hash": H, "mutants": 4, "lines": _lines(4), "window": _window(killed=4),
                                          "partial": None}

    def test_a_first_night_whose_every_slice_failed_leaves_a_state_that_loads(self, tmp_path: Path) -> None:
        """No slice reported an engine and the state had none: it must stay
        none, which the next night loads, not an empty version it refuses."""
        failed = _record(0, 1, {}, stopped="lane")
        failed["engine"] = None
        state, _ = _stitch([failed], sw.empty_state("2026-10-16"), jobs=1)
        assert state["engine"] is None
        assert sw.load_state(sw.save_state(state, tmp_path), "x")["engine"] is None

    def test_a_slice_whose_lane_failed_is_no_engine_mismatch(self) -> None:
        good = _record(0, 2, {A.ident: _res(A, killed=4)})
        failed = _record(1, 2, {}, stopped="lane")
        failed["engine"] = None
        _, night = _stitch([good, failed])
        assert night["problems"] == ["slice 1: stopped by the lane"]

    def test_a_window_of_other_lines_than_the_sample_stops_the_night_short_and_the_rest_counts(self) -> None:
        """The sample is drawn from the state's lines, so a window of other
        lines or another size is a problem, not a recount: that result is
        left out, the rest fold in."""
        state = _state(f=4, g=5)
        _decide(state, A, killed=4)
        record = _record(0, 1, {A.ident: _res(A, killed=3), B.ident: _res(B, hash_="1" * 16, killed=2),
                                C.ident: _res(C, killed=4, survived=1, survivors=("1@1:survived",))},
                         counts={})
        state, night = _stitch([record], state, jobs=1)
        assert state["units"][A.ident]["window"] == _window(killed=4)
        assert night["problems"] == [
            f"slice 0 ran {A.ident} over lines 1, 2 and 3, 3 mutants, where the cycle's sample is lines "
            "1, 2, 3 and 4, 4 mutants",
            f"slice 0 ran {B.ident} at code the tree does not hold"]
        assert night["notes"] == [] and state["units"][C.ident]["window"]["survived"] == 1

    def test_a_new_engine_restarts_the_cycle_and_says_so(self) -> None:
        state = _state(f=4)
        _decide(state, A, killed=4)
        state["cycle_started"] = "2026-10-01"
        record = _record(0, 1, {A.ident: _res(A, killed=3, survived=1, survivors=("2@2:survived",))})
        record["engine"] = "3.9.0"
        state, night = _stitch([record], state, jobs=1)
        assert state["engine"] == "3.9.0" and state["cycle_started"] == "2026-10-17"
        assert state["units"][A.ident]["window"] == _window(killed=3, survived=1, survivors=("2@2:survived",))
        assert night["notes"] == ["mutmut 3.8.0 gave way to 3.9.0: every function starts afresh, "
                                  "and so does the cycle"]

    def test_a_slices_exit_is_two_only_for_an_engine_lane_or_unmapped_stop(self) -> None:
        decided = {A.ident: _res(A, survived=1, survivors=("1@1:survived",))}
        assert sw.slice_exit(_record(0, 1, decided)) == 0
        assert sw.slice_exit(_record(0, 1, decided, stopped="budget")) == 0
        assert sw.slice_exit(_record(0, 1, {}, planned=0)) == 0
        assert sw.slice_exit(_record(0, 1, {})) == 0
        assert sw.slice_exit(_record(0, 1, {}, stopped="budget")) == 0
        for stop in ("engine", "lane", "unmapped"):
            assert sw.slice_exit(_record(0, 1, decided, stopped=stop)) == 2

    def test_the_calibration_follows_what_the_mutants_cost(self) -> None:
        """Ten mutants estimated at 2.5 s of a job each took 20 s on one of
        the slice's two workers, 10 s of the job: the factor moves halfway
        from 1 to 4.  It moves past the old ceiling of 5.0, which it sat at
        from 4 to 10 November 2026 (#1838)."""
        result = _res(A, killed=10)
        result["durations"] = {str(n): 20.0 for n in range(1, 11)}
        record = {**_record(0, 1, {A.ident: result}), "workers": 2}
        state, _ = _stitch([record], jobs=1)
        assert state["calibration"] == 2.5
        result["durations"] = {str(n): 500.0 for n in range(1, 11)}
        state, _ = _stitch([record], jobs=1)
        assert state["calibration"] == 50.5


# ---------------------------------------------------------------------------
# Closing a cycle, and the committed summary
# ---------------------------------------------------------------------------


def _complete(state: dict[str, Any], counts: dict[Any, int]) -> None:
    """Count each unit's mutants, one a line, and decide its window killed."""
    for unit, n in counts.items():
        state["units"][unit.ident].update(mutants=n, lines=_lines(n))
        _decide(state, unit, killed=n)


class TestCycle:
    def test_an_incomplete_cycle_stays_open(self) -> None:
        state = _state(f=4, m=3, g=5)
        _decide(state, A, killed=4)
        assert sw.close_cycle(state, UNITS, head="h", today="e") is False
        assert state["cycle"] == 1 and state["last_complete"] is None

    def test_a_complete_cycle_closes_with_its_totals_and_opens_the_next(self) -> None:
        state = _state()
        _complete(state, {A: 4, B: 3, C: 5})
        _decide(state, B, killed=2, survived=1, survivors=("3@2:survived",))  # B's line 2 is the file's 21
        _decide(state, C, killed=3, survived=1, no_tests=1, survivors=("4@4:survived",))
        assert sw.close_cycle(state, UNITS, head="c" * 40, today="2026-11-30") is True
        assert state["cycle"] == 2 and state["cycle_started"] == "2026-11-30"
        assert all(r["window"] is None and r["mutants"] and r["lines"] for r in state["units"].values())
        last = state["last_complete"]
        assert last["cycle"] == 1 and last["finished"] == "2026-11-30" and last["head"] == "c" * 40
        assert last["modules"] == {
            "vera/a.py": {"killed": 6, "survived": 1, "timeout": 0, "no_tests": 0, "slow": 0, "other": 0,
                          "mutants": 7},
            "vera/b.py": {"killed": 3, "survived": 1, "timeout": 0, "no_tests": 1, "slow": 0, "other": 0,
                          "mutants": 5}}
        assert last["survivors"] == [f"vera.a.x{SEP}C{SEP}m__mutmut_3@21:survived", "vera.b.x_g__mutmut_4@4:survived"]
        assert (last["sampled"], last["population"], last["fraction"]) == (12, 12, 1.0)

    def test_the_cycle_closes_when_every_sampled_window_is_decided(self, monkeypatch: pytest.MonkeyPatch) -> None:
        """At a half sample each unit's window is its sampled lines' mutants;
        the cycle waits for every window, and closes on the sample alone."""
        monkeypatch.setattr(sw, "SAMPLE_FRACTION", 0.5)
        state = _state(f=40, m=40, g=40)
        sizes = {u: sum(sw.window_counts(state, u)[1]) for u in UNITS}
        assert all(5 <= n <= 35 for n in sizes.values()), sizes
        for u in (A, B):
            _decide(state, u, killed=sizes[u])
        assert sw.close_cycle(state, UNITS, head="h", today="e") is False
        last_line = sw.sampled_lines(state, C)[-1]
        _decide(state, C, killed=sizes[C] - 1, survived=1, survivors=(f"{sizes[C]}@{last_line}:survived",))
        assert sw.close_cycle(state, UNITS, head="h", today="e") is True
        last = state["last_complete"]
        assert (last["sampled"], last["population"], last["fraction"]) == (sum(sizes.values()), 120, 0.5)
        assert last["modules"]["vera/a.py"] == {"killed": sizes[A] + sizes[B], "survived": 0, "timeout": 0,
                                                "no_tests": 0, "slow": 0, "other": 0, "mutants": 80}
        assert last["survivors"] == [f"vera.b.x_g__mutmut_{sizes[C]}@{last_line}:survived"]

    def test_the_interval_is_wilsons(self) -> None:
        """The 95% Wilson interval of a proportion, the textbook values."""
        assert sw.wilson(5, 10) == (23.7, 76.3)
        assert sw.wilson(0, 10) == (0.0, 27.8)
        assert sw.wilson(10, 10) == (72.2, 100.0)
        assert sw.wilson(1600, 2000) == (78.2, 81.7)
        assert sw.wilson(0, 0) == (0.0, 0.0)

    def test_the_summary_is_the_committed_csv_badge_and_inventory(self, tmp_path: Path) -> None:
        """A module's total is its sampled mutants an in-process test reaches
        with a known outcome, so `no tests` and the cut-short statuses stay
        out of the score; its population and the score's 95% interval stand
        beside it, and the badge carries the interval's half-width."""
        state = _state()
        _complete(state, {A: 4, B: 3, C: 5})
        _decide(state, C, killed=3, survived=1, timeout=1, survivors=("4@4:survived", "5@5:timeout"))
        _decide(state, A, killed=3, no_tests=1)
        _decide(state, B, killed=1, other=1, slow=1)  # a segfault and a slow mutant: no outcome to score
        sw.close_cycle(state, UNITS, head="h", today="e")
        score = sw.write_summary(state, tmp_path)
        rows = (tmp_path / "mutation-summary.csv").read_text(encoding="utf-8").splitlines()
        assert rows == ["module,total,killed,survived,timeout,caught_pct,mutants,ci95_low,ci95_high",
                        "vera/b.py,5,3,1,1,80.0,5,37.6,96.4", "vera/a.py,4,4,0,0,100.0,7,51.0,100.0",
                        "TOTAL (vera),9,7,1,1,88.9,12,56.5,98.0"]
        assert score == 88.9
        badge = json.loads((tmp_path / "mutation.json").read_text(encoding="utf-8"))
        assert badge == {"schemaVersion": 1, "label": "mutation", "message": "88.9% ±20.8", "color": "green"}
        assert (tmp_path / "mutation-survivors.csv").read_text(encoding="utf-8").splitlines() == [
            "module,mutant,status", f"vera.a,x{SEP}C{SEP}m__mutmut_2@L21,slow", "vera.b,x_g__mutmut_4@L4,survived",
            "vera.b,x_g__mutmut_5@L5,timeout"]  # a slow mutant is listed, apart from the score

    def test_no_summary_is_written_before_a_cycle_has_closed(self, tmp_path: Path) -> None:
        with pytest.raises(sw.StateError):
            sw.write_summary(sw.empty_state("d"), tmp_path)

    def test_the_stitch_closes_a_complete_cycle_whatever_else_the_night_did(self) -> None:
        state = _state()
        _complete(state, {A: 4, B: 3})
        state["units"][C.ident].update(mutants=1, lines=_lines(1))
        done = {C.ident: _res(C, killed=1)}
        closed, night = _stitch([_record(0, 1, done)], json.loads(json.dumps(state)), jobs=1)
        assert night["closed"] and closed["cycle"] == 2
        kept, night = _stitch([_record(0, 2, done), _record(1, 2, {}, stopped="engine")],
                              json.loads(json.dumps(state)))
        assert night["problems"] == ["slice 1: stopped by the engine"]  # red, and the sample is decided:
        assert night["closed"] and kept["cycle"] == 2  # the cycle closes whatever else the night did
        # A slice with no record is noted, not a stop: the bins are disjoint,
        # so a state the other slices complete owed that slice nothing.
        closed, night = _stitch([_record(0, 2, done)], json.loads(json.dumps(state)))
        assert night["lost"] == [1] and night["problems"] == [] and night["closed"]


# ---------------------------------------------------------------------------
# The workflow's matrix, and the workflow read as data
# ---------------------------------------------------------------------------


class TestMatrix:
    def test_the_schedule_runs_the_nights_jobs_and_a_dispatch_one_by_default(self, capsys: pytest.CaptureFixture[str]) -> None:
        assert sw.main(["matrix", "--event", "schedule", "--requested", ""]) == 0
        assert capsys.readouterr().out.splitlines() == [
            f"jobs={sw.JOBS}", f"slices={json.dumps(list(range(sw.JOBS)))}"]
        assert sw.main(["matrix", "--event", "workflow_dispatch", "--requested", ""]) == 0
        assert capsys.readouterr().out.splitlines() == ["jobs=1", "slices=[0]"]

    def test_a_dispatch_outside_the_range_is_refused(self) -> None:
        assert sw.main(["matrix", "--event", "workflow_dispatch", "--requested", "0"]) == 2
        assert sw.main(["matrix", "--event", "workflow_dispatch", "--requested", str(sw.MAX_JOBS + 1)]) == 2


class TestWorkflow:
    def _wf(self) -> dict[Any, Any]:
        data = yaml.safe_load(WORKFLOW.read_text(encoding="utf-8"))
        assert isinstance(data, dict)
        return data

    def _steps(self, job: str) -> list[dict[str, Any]]:
        steps = self._wf()["jobs"][job]["steps"]
        assert isinstance(steps, list)
        return steps

    def test_it_runs_nightly_and_on_demand_with_one_job_by_default(self) -> None:
        on = self._wf()[True]
        assert set(on) == {"schedule", "workflow_dispatch"} and len(on["schedule"]) == 1
        assert on["workflow_dispatch"]["inputs"]["jobs"]["default"] == 1

    def test_only_the_issue_job_writes_and_it_writes_only_issues(self) -> None:
        import re

        wf = self._wf()
        assert wf["permissions"] == {"contents": "read"}
        jobs = wf["jobs"]
        for name in ("setup", "sweep", "stitch"):
            assert jobs[name]["permissions"] == {"contents": "read", "actions": "read"}, name
        assert jobs["issue"]["permissions"] == {"issues": "write"}
        assert not re.search(r"\$\{\{[^}]*\bsecrets\b", WORKFLOW.read_text(encoding="utf-8"))

    def test_every_context_value_reaches_a_shell_through_env(self) -> None:
        for job in self._wf()["jobs"].values():
            for step in job["steps"]:
                assert "${{" not in step.get("run", ""), step.get("name", step.get("id"))

    def test_every_action_is_pinned_as_the_other_workflows_pin_it(self) -> None:
        uses = {s["uses"] for j in self._wf()["jobs"].values() for s in j["steps"] if "uses" in s}
        assert uses == {"actions/checkout@v7", "actions/setup-python@v7", "actions/download-artifact@v8",
                        "actions/upload-artifact@v7", "actions/github-script@v9"}

    def test_a_night_never_cancels_another(self) -> None:
        assert self._wf()["concurrency"] == {"group": "mutation-nightly", "cancel-in-progress": False}

    def test_the_budget_fits_the_job_and_the_job_fits_the_cap(self) -> None:
        import re

        job = self._wf()["jobs"]["sweep"]
        (step,) = [s for s in job["steps"] if "scripts/mutate_sweep.py start" in s.get("run", "")]
        budget = int(re.search(r"--budget (\d+)", step["run"]).group(1))  # type: ignore[union-attr]
        assert budget == sw.DEFAULT_BUDGET_S
        assert budget + 30 * 60 <= job["timeout-minutes"] * 60 <= 6 * 3600

    def test_the_state_is_found_among_this_workflows_own_runs(self) -> None:
        (step,) = [s for s in self._steps("setup") if s.get("id") == "state"]
        assert "scripts/mutate_sweep.py find-state" in step["run"] and '--repo-id "$REPO_ID"' in step["run"]
        assert step["env"]["REPO_ID"] == "${{ github.repository_id }}"

    def test_a_setup_lookup_that_fails_fails_the_step(self) -> None:
        """bash with pipefail, and the command's output taken into a variable
        before it is written, so its exit status is never thrown away."""
        for step in self._steps("setup"):
            if "run" in step:
                assert step["shell"] == "bash", step.get("id")
                first = step["run"].splitlines()[0]
                assert first.split("=", 1)[1].startswith("$(python3 scripts/mutate_sweep.py "), first

    def test_the_engine_installed_is_uv_locks(self) -> None:
        """Both mutation lanes install uv.lock and nothing else, so a release
        of the engine or of anything it runs with reaches a lane only through
        a lock bump: a reviewed pull request, which the diff lane's self-tests
        run on.  ``--locked`` refuses a lock that ``pyproject.toml`` has moved
        past rather than resolving afresh.  No workflow names a mutmut
        version of its own: the engine is the lock's, and the version it
        reports is the one the sweep's state compares."""
        import re

        ci = yaml.safe_load((ROOT / ".github" / "workflows" / "ci.yml").read_text(encoding="utf-8"))
        (lock_check,) = [s for j in ci["jobs"].values() for s in j["steps"]
                         if s.get("name") == "Verify uv.lock is up to date"]
        assert lock_check["run"].splitlines()[0] == LOCKED_INSTALL[0]  # uv, as the lock check installs it
        for path, job in ((WORKFLOW, "sweep"), (DIFF_WORKFLOW, "mutate")):
            steps = yaml.safe_load(path.read_text(encoding="utf-8"))["jobs"][job]["steps"]
            (install,) = [s for s in steps if s.get("name") == "Install dependencies"]
            assert install["run"].splitlines() == LOCKED_INSTALL, path.name
            assert not [s for s in steps if s is not install
                        and re.search(r"\b(?:pip|uv)\b", s.get("run", ""))], path.name
        for path in sorted((ROOT / ".github" / "workflows").glob("*.yml")):
            assert "mutmut==" not in path.read_text(encoding="utf-8"), path.name

    def test_the_jobs_are_the_setups_matrix_and_one_failing_slice_stops_no_other(self) -> None:
        sweep = self._wf()["jobs"]["sweep"]
        assert sweep["strategy"] == {"fail-fast": False,
                                     "matrix": {"slice": "${{ fromJSON(needs.setup.outputs.slices) }}"}}
        # A lost runner fails the slice's job with nothing uploaded; the
        # stitch decides the night from the records it has, and the run's
        # colour follows the stitch (#1751).
        assert sweep["continue-on-error"] is True
        (step,) = [s for s in self._steps("setup") if s.get("id") == "jobs"]
        assert "scripts/mutate_sweep.py matrix" in step["run"]

    def test_the_stitch_runs_whatever_the_slices_did_and_keeps_the_state_whatever_it_did(self) -> None:
        stitch = self._wf()["jobs"]["stitch"]
        assert stitch["needs"] == ["setup", "sweep"]
        assert stitch["if"] == "always() && needs.setup.result == 'success'"
        (keep,) = [s for s in stitch["steps"] if str(s.get("uses", "")).startswith("actions/upload-artifact@")]
        assert keep["if"] == "always()"
        assert keep["with"]["name"] == "mutation-sweep-state" and keep["with"]["retention-days"] == 90
        (record,) = [s for s in self._steps("sweep") if s.get("name") == "Upload the slice's record"]
        assert record["if"] == "always()"
        assert record["with"]["name"] == "mutation-sweep-slice-${{ matrix.slice }}"

    def test_a_lane_that_fails_before_the_sweep_records_itself_while_the_runner_is_there(self) -> None:
        steps = self._steps("sweep")
        names = [s.get("name") for s in steps]
        i = names.index("Record a lane that failed before the sweep ran")
        assert names[i - 1] == "Mutate this slice of the night" and names[i + 1] == "Upload the slice's record"
        step = steps[i]
        assert step["if"] == "failure()" and "scripts/mutate_sweep.py lane-failed" in step["run"]
        assert '--slice "$SLICE" --of "$JOBS"' in step["run"] and '--out "$RUNNER_TEMP/slice"' in step["run"]
        assert step["env"] == {"SLICE": "${{ matrix.slice }}", "JOBS": "${{ needs.setup.outputs.jobs }}"}

    def test_the_tracking_issue_is_filed_only_for_a_scheduled_night_that_stopped_short(self) -> None:
        issue = self._wf()["jobs"]["issue"]
        assert issue["needs"] == ["setup", "sweep", "stitch"]
        assert issue["if"] == "always() && github.event_name == 'schedule' && needs.stitch.result != 'success'"
        (step,) = issue["steps"]
        assert 'const LABEL = "mutation-sweep";' in step["with"]["script"]
        # The issue says what the rules now are: no budget rule (#1838).
        assert "budget ran out" not in step["with"]["script"]
        assert "a second night in a row that decided no mutant" in step["with"]["script"]

    def test_a_slice_runs_two_workers_under_the_mutant_cap(self) -> None:
        """Two workers, not every CPU: four survivors at once took a runner
        into swap (#1838); and the cap on a mutant's run is the script's."""
        import re

        job = self._wf()["jobs"]["sweep"]
        (step,) = [s for s in job["steps"] if "scripts/mutate_sweep.py start" in s.get("run", "")]
        assert re.search(r"--max-children (\d+)", step["run"]).group(1) == str(sw.WORKERS) == "2"  # type: ignore[union-attr]
        assert re.search(r"--mutant-cap (\d+)", step["run"]).group(1) == str(sw.MUTANT_CAP_S) == "2400"  # type: ignore[union-attr]


# ---------------------------------------------------------------------------
# The heartbeat
# ---------------------------------------------------------------------------


MEMINFO = ("MemTotal:       16368832 kB\nMemFree:         1000000 kB\nMemAvailable:   11503616 kB\n"
           "SwapTotal:       4194300 kB\nSwapFree:        3145724 kB\n")
LOADAVG = "3.91 3.80 3.40 5/1234 99999\n"


class TestHeartbeat:
    """A line every few minutes with the time, the runner's memory and load,
    and the engine's last status, which the legs print into the job log;
    the record's heartbeat series holds the same figures, and a lost
    runner's last leg keeps them up to the leg (#1838)."""

    def test_the_watch_keeps_the_phases_the_engines_count_and_the_memory_figures(self) -> None:
        """The record carries what the proof night's table reads: when each
        of the engine's phases started and its first mutant was decided, its
        last count, and the runner's memory floor and swap peak (#1838)."""
        watch = sw.Watch()
        low = MEMINFO.replace("11503616", "1048576").replace("3145724", "2097148")
        for at, status, mem in ((60, "Generating mutants", MEMINFO), (120, "Running stats", MEMINFO),
                                (3000, "Running clean tests", low), (5000, "Running forced fail test", MEMINFO),
                                (5100, "Running mutation testing", MEMINFO), (5200, "0/48  🎉 0", MEMINFO),
                                (5500, "3/48  🎉 3 🫥 0", MEMINFO), (6000, "9/48  🎉 8 🙁 1", None)):
            watch.observe(at, status, mem)
        assert watch.fields() == {
            "phases": {"stats_s": 120, "clean_s": 3000, "forced_s": 5000, "mutants_s": 5100,
                       "first_mutant_s": 5500},
            "engine_status": "9/48  🎉 8 🙁 1", "engine_decided": 9, "mem_floor_mib": 1024, "swap_peak_mib": 2048}

    def test_the_nights_summary_states_its_rules(self) -> None:
        state, night = _stitch([_record(0, 1, {A.ident: _res(A, window=4, killed=1)}, stopped="budget")], jobs=1)
        text = sw.render_night(state, night, UNITS)
        assert sw.RULES in text and "| 0 | 1 | 1 | 0 | budget |" in text
        assert "budget ran out before its first mutant" not in text

    def test_a_line_carries_the_time_the_memory_the_load_and_the_engines_status(self) -> None:
        assert sw.HEARTBEAT_S == 300.0
        assert sw.heartbeat_line(3725.0, "Running mutants 12/345", MEMINFO, LOADAVG) == (
            "heartbeat +1:02 | mem avail 11,234 of 15,985 MiB | swap used 1,024 of 4,096 MiB"
            " | load 3.91 3.80 3.40 | engine: Running mutants 12/345")

    def test_what_the_platform_cannot_say_is_left_out(self) -> None:
        assert sw.heartbeat_line(59.0, None, None, None) == "heartbeat +0:00"
        assert sw.heartbeat_line(36000.0, "x", None, "1.00 2.00 3.00 1/2 3") == (
            "heartbeat +10:00 | load 1.00 2.00 3.00 | engine: x")
        assert sw.heartbeat_line(0.0, None, "MemTotal: 10 kB\n", None) == "heartbeat +0:00"

    def test_the_engines_status_is_the_newest_logs_last_row_without_the_spinner(self, tmp_path: Path) -> None:
        assert sw.engine_status(tmp_path) is None
        (tmp_path / "mutmut-run-1.log").write_text("the first attempt\n", encoding="utf-8")
        (tmp_path / "mutmut-run-2.log").write_text(
            "Running stats\n\u280b Running mutants 1/5\r\u2819 Running mutants 2/5\r", encoding="utf-8")
        assert sw.engine_status(tmp_path) == "Running mutants 2/5"
        (tmp_path / "mutmut-run-10.log").write_text("x" * 500, encoding="utf-8")
        assert sw.engine_status(tmp_path) == "x" * sw.STATUS_WIDTH


# ---------------------------------------------------------------------------
# A night end to end
# ---------------------------------------------------------------------------


FAKE_ENGINE = '''
import json, os, sys
from pathlib import Path
state = Path(os.environ["FAKE_STATE"])
args = sys.argv[1:]
with (state / "calls.jsonl").open("a", encoding="utf-8") as fh:
    fh.write(json.dumps({"cwd": os.getcwd(), "args": args, "columns": os.environ.get("COLUMNS"),
                         "bytecode_off": os.environ.get("PYTHONDONTWRITEBYTECODE")}) + "\\n")
if args[0] == "--version":
    print("mutmut, version 3.8.0")
    sys.exit(0)
def unit_starts(text):
    # Each unit's def line, keyed as mutmut mangles it.
    import ast
    starts = {}
    for node in ast.parse(text).body:
        if isinstance(node, ast.FunctionDef):
            starts["x_" + node.name] = node.lineno
        elif isinstance(node, ast.ClassDef):
            for member in node.body:
                if isinstance(member, ast.FunctionDef):
                    starts["xǁ" + node.name + "ǁ" + member.name] = member.lineno
    return starts
if args[0] == "count":
    data = json.load(sys.stdin)
    n = int(os.environ.get("FAKE_COUNT", "2"))
    out = {}
    for path, keys in data["units"].items():
        starts = unit_starts(data["sources"][path])
        out[path] = {key: {"mutants": n, "lines": {str(starts[key] + i): 1 for i in range(n)}} for key in keys}
    print(json.dumps(out))
    sys.exit(0)
if args[0] == "run" and os.environ.get("MUTATE_DIFF_WINDOW"):
    # As the engine launcher does before mutmut generates: each unit's
    # mutants on every line and in the window, a kept unit's mutants being
    # the count's, one a line, and a unit under the narrowing pragma none.
    import ast
    spec = json.loads(Path(os.environ["MUTATE_DIFF_WINDOW"]).read_text(encoding="utf-8"))
    n = int(os.environ.get("FAKE_COUNT", "2"))
    files = {}
    for path, lines in spec["lines"].items():
        text = Path(path).read_text(encoding="utf-8")
        rows = text.splitlines()
        units = {}
        for node in ast.parse(text).body:
            if isinstance(node, ast.FunctionDef):
                units["x_" + node.name] = node
            elif isinstance(node, ast.ClassDef):
                for member in node.body:
                    if isinstance(member, ast.FunctionDef):
                        units["xǁ" + node.name + "ǁ" + member.name] = member
        files[path] = {}
        for key, node in units.items():
            kept = "pragma: no mutate block" not in rows[node.lineno - 1]
            inside = len([l for l in lines if node.lineno <= l < node.lineno + n])  # its mutants, one a line
            files[path][key] = {"held": n, "window": inside if kept else 0}
    Path(spec["record"]).write_text(json.dumps({"files": files}), encoding="utf-8")
if args[0] == "run" and os.environ.get("FAKE_RUN_LOG"):
    # A log the engine printed, as it printed it (its stats pass stopping).
    print(Path(os.environ["FAKE_RUN_LOG"]).read_text(encoding="utf-8"), end="")
    sys.exit(1)
if args[0] == "run":
    import time
    if os.environ.get("FAKE_RUN_TRAP_INT"):
        # The budget's stop: the engine takes its interrupt, marks that it
        # is stopping (the listing then shows what the stop leaves), winds
        # down for a while, and exits.
        import signal
        def _stopping(*_):
            (state / "stopping").write_text("1", encoding="utf-8")
            time.sleep(float(os.environ["FAKE_RUN_TRAP_INT"]))
            if os.environ.get("FAKE_SNAPSHOT"):
                # What the slice had written of its record as the engine exits.
                source, target = os.environ["FAKE_SNAPSHOT"].split(os.pathsep)
                if Path(source).exists():
                    Path(target).write_bytes(Path(source).read_bytes())
            (state / "exited").write_text("1", encoding="utf-8")
            sys.exit(0)
        signal.signal(signal.SIGINT, _stopping)
    if os.environ.get("FAKE_INFLIGHT") and os.environ.get("MUTATION_ORACLE_INFLIGHT"):
        # As the oracle plugin writes it for each mutant's run (this
        # process standing in for the worker).
        with open(os.environ["MUTATION_ORACLE_INFLIGHT"], "a", encoding="utf-8") as fh:
            for name in os.environ["FAKE_INFLIGHT"].split(","):
                fh.write(f"{name}\\t{os.getpid()}\\t{time.time():.3f}\\t0\\n")
    time.sleep(float(os.environ.get("FAKE_RUN_SLEEP", "0")))
    if os.environ.get("FAKE_META"):
        # mutmut's meta file for a source file: each mutant's exit code.
        path, codes = os.environ["FAKE_META"].split("=", 1)
        meta = Path("mutants") / (path + ".meta")
        meta.parent.mkdir(parents=True, exist_ok=True)
        meta.write_text(json.dumps({"exit_code_by_key": json.loads(codes)}), encoding="utf-8")
    if os.environ.get("FAKE_SNAPSHOT"):
        # What the slice had written of its record while this run went on.
        source, target = os.environ["FAKE_SNAPSHOT"].split(os.pathsep)
        if Path(source).exists():
            Path(target).write_bytes(Path(source).read_bytes())
    failing = os.environ.get("FAKE_COPY_FAILURE", "")
    config = Path("pyproject.toml").read_text(encoding="utf-8")
    if failing and f"--deselect={failing}" not in config:
        print("Running stats")
        if os.environ.get("FAKE_COPY_FAILURE_SILENT"):
            # The fork server: the pass's pytest output never reaches the
            # log; the plugin wrote the failing test's id to the lane's file.
            with open(os.environ["MUTATION_ORACLE_FAILURES"], "a", encoding="utf-8") as fh:
                fh.write(failing + "\\n")
        else:
            print(f"FAILED {failing} - FileNotFoundError: x")
        print("failed to collect stats. runner returned 1")
        sys.exit(1)
    for fake, env in (("FAKE_ORACLE_SKIPS", "MUTATION_ORACLE_SKIPS"),
                      ("FAKE_ORACLE_SOURCE_SKIPS", "MUTATION_ORACLE_SOURCE_SKIPS")):
        skipped = os.environ.get(fake, "")
        if skipped and os.environ.get(env):
            with open(os.environ[env], "a", encoding="utf-8") as fh:
                fh.write("".join(f"{nodeid}\\n" for nodeid in skipped.split(",")))
    sys.exit(int(os.environ.get("FAKE_RUN_EXIT", "0")))
if args[0] == "results":
    import time
    stopping = (state / "stopping").exists()
    time.sleep(float(os.environ.get("FAKE_RESULTS_SLEEP_STOPPING" if stopping else "FAKE_RESULTS_SLEEP", "0")))
    calls = state / "results_calls"
    n = int(calls.read_text(encoding="utf-8")) + 1 if calls.exists() else 1
    calls.write_text(str(n), encoding="utf-8")
    if n >= int(os.environ.get("FAKE_RESULTS_FAIL_FROM", "") or 10**9):
        # A listing that meets a meta file mid-write, from this call on.
        print("Traceback (most recent call last):\\njson.decoder.JSONDecodeError: Expecting value")
        sys.exit(1)
    if os.environ.get("FAKE_RESULTS_FAIL_AFTER_EXIT") and (state / "exited").exists():
        print("Traceback (most recent call last):\\njson.decoder.JSONDecodeError: Expecting value")
        sys.exit(1)
    listing = (state / "results.txt").read_text(encoding="utf-8")
    if (state / "stopping").exists():
        listing = listing.replace(": not checked", ": segfault")  # what the stop leaves
    sys.stdout.write(listing)
    sys.exit(int(os.environ.get("FAKE_RESULTS_EXIT", "0")))
sys.exit(9)
'''

MODULE = "def f(x):\n    return x + 1\n\n\ndef g(x):\n    return x * 2\n"


def _git(repo: Path, *args: str) -> str:
    env = {k: v for k, v in os.environ.items() if k not in ("GIT_DIR", "GIT_WORK_TREE", "GIT_INDEX_FILE")}
    return subprocess.run(["git", "-C", str(repo), "-c", "user.name=t", "-c", "user.email=t@t.invalid",
                           "-c", "commit.gpgsign=false", *args], capture_output=True, text=True,
                          encoding="utf-8", env=env, check=True).stdout


@pytest.fixture
def repo(tmp_path: Path) -> Path:
    root = tmp_path / "repo"
    (root / "vera").mkdir(parents=True)
    (root / "tests").mkdir()
    (root / "vera" / "__init__.py").write_text("", encoding="utf-8")
    (root / "vera" / "m.py").write_text(MODULE, encoding="utf-8")
    (root / "tests" / "__init__.py").write_text("", encoding="utf-8")
    (root / "tests" / "test_m.py").write_text(
        "from vera.m import f, g\n\n\ndef test_f():\n    assert f(1) == 2\n\n\n"
        "def test_g():\n    assert g(3) == 6\n", encoding="utf-8")
    (root / "pyproject.toml").write_text(
        '[tool.mutmut]\nsource_paths = ["vera/"]\nuse_setproctitle = false\n'
        'process_isolation = "forkserver"\n'
        'pytest_add_cli_args = ["-p", "no:cacheprovider"]\npytest_add_cli_args_test_selection = []\n',
        encoding="utf-8")
    _git(root, "init", "-q")
    _git(root, "add", "-A")
    _git(root, "commit", "-q", "-m", "base")
    return root


#: The engine fixture's module: mutants on several lines of two functions.
HELD_MODULE = ("def f(x):\n    if x > 0:\n        return x + 1\n    return x - 2\n\n\n"
               "def g(x):\n    return x * 2\n")

#: Its tests: each sleeps while the mutant under test is one that
#: ``SWEEP_FIXTURE_HOLD`` names, for ``SWEEP_FIXTURE_HOLD_S`` seconds.  An
#: empty name is none: the clean run's ``MUTANT_UNDER_TEST`` is empty, and a
#: hold read as ``[""]`` once held the clean run for its whole hour.
HELD_TESTS = (
    "import os\nimport time\n\nfrom vera.m import f, g\n\n\n"
    "def _hold():\n"
    "    held = [n for n in os.environ.get('SWEEP_FIXTURE_HOLD', '').split(',') if n]\n"
    "    if os.environ.get('MUTANT_UNDER_TEST', '') in held:\n"
    "        time.sleep(float(os.environ.get('SWEEP_FIXTURE_HOLD_S', '0')))\n\n\n"
    "def test_f():\n    _hold()\n    assert (f(1), f(-1), f(0)) == (2, -3, -2)\n\n\n"
    "def test_g():\n    _hold()\n    assert g(3) == 6\n")


@pytest.fixture
def held_repo(tmp_path: Path) -> Path:
    """A repository for the engine's own runs: the oracle plugin loaded, as
    ``[tool.mutmut]`` loads it, and mutmut's wall bound (half its CPU limit,
    ``(est + 1) × timeout_multiplier``) far past any hold, so only the
    budget or the plugin's cap ends a held mutant."""
    root = tmp_path / "repo"
    (root / "vera").mkdir(parents=True)
    (root / "tests").mkdir()
    (root / "vera" / "__init__.py").write_text("", encoding="utf-8")
    (root / "vera" / "m.py").write_text(HELD_MODULE, encoding="utf-8")
    (root / "tests" / "__init__.py").write_text("", encoding="utf-8")
    (root / "tests" / "test_m.py").write_text(HELD_TESTS, encoding="utf-8")
    (root / "tests" / "mutation_oracle.py").write_text(
        (ROOT / "tests" / "mutation_oracle.py").read_text(encoding="utf-8"), encoding="utf-8")
    (root / "pyproject.toml").write_text(
        '[tool.mutmut]\nsource_paths = ["vera/"]\nuse_setproctitle = false\n'
        'process_isolation = "forkserver"\ntimeout_multiplier = 1000.0\n'
        'pytest_add_cli_args = ["-p", "tests.mutation_oracle", "-p", "no:cacheprovider"]\n'
        'pytest_add_cli_args_test_selection = []\n', encoding="utf-8")
    _git(root, "init", "-q")
    _git(root, "add", "-A")
    _git(root, "commit", "-q", "-m", "base")
    return root


@pytest.fixture
def no_git_locators(monkeypatch: pytest.MonkeyPatch) -> None:
    for name in ("GIT_DIR", "GIT_WORK_TREE", "GIT_INDEX_FILE", "GIT_COMMON_DIR"):
        monkeypatch.delenv(name, raising=False)


def _night(repo: Path, tmp_path: Path, n: int, results: str, *, state: Path | None = None,
           engine: list[str] | None = None, budget: float | None = None,
           extra: list[str] | None = None, real: bool = False,
           ) -> tuple[int, dict[str, Any], list[dict[str, Any]]]:
    """One night of one slice, against the stand-in engine (``engine``, the
    fake by default) or, with ``real``, the sweep's own default engine, the
    diff lane's launcher over mutmut, as the workflow runs it."""
    fake = tmp_path / f"fake{n}"
    fake.mkdir()
    (fake / "results.txt").write_text(results, encoding="utf-8")
    (tmp_path / "fake_mutmut.py").write_text(FAKE_ENGINE, encoding="utf-8")
    os.environ["FAKE_STATE"] = str(fake)
    out = tmp_path / f"slice{n}"
    try:
        code = sw.main(["night", "--slice", "0", "--of", "1", "--repo", str(repo), "--out", str(out),
                        "--workdir", str(tmp_path / f"work{n}"), "--max-children", "2",
                        *(["--state", str(state)] if state else []),
                        *(["--budget", str(budget)] if budget else []), *(extra or []),
                        *([] if real else
                          ["--engine", *(engine or [sys.executable, str(tmp_path / "fake_mutmut.py")])])])
    finally:
        del os.environ["FAKE_STATE"]
    calls = [json.loads(line) for line in (fake / "calls.jsonl").read_text(encoding="utf-8").splitlines()] if (
        fake / "calls.jsonl").exists() else []
    return code, json.loads((out / "slice-0.json").read_text(encoding="utf-8")), calls


def _stitch_cli(repo: Path, tmp_path: Path, n: int, state: Path | None) -> tuple[int, dict[str, Any]]:
    out = tmp_path / f"state{n}"
    code = sw.main(["stitch", "--of", "1", "--repo", str(repo), "--slices", str(tmp_path / f"slice{n}"),
                    "--out", str(out), *(["--state", str(state)] if state else [])])
    return code, json.loads((out / sw.STATE_FILE).read_text(encoding="utf-8"))


def _engine_said(tmp_path: Path, n: int, record: dict[str, Any] | None = None) -> str:
    """What a real night's engine printed (its logs' last rows, spinner
    frames dropped) and its record's stop and phases: a failure's message,
    so the job log says where the engine stopped."""
    rows: list[str] = []
    for log in sorted((tmp_path / f"work{n}").glob("mutmut-run-*.log")):
        text = log.read_text(encoding="utf-8", errors="replace").replace("\r", "\n")
        rows += [f"{log.name}: {r.strip()}" for r in text.splitlines() if r.strip()][-25:]
    if record is not None:
        rows.append(json.dumps({k: record.get(k) for k in (
            "stopped", "engine_exit", "engine_error", "engine_tail", "phases", "engine_status", "slow")}))
    return "\n".join(rows)


_REAL_RUN_ENGINE = sw.md.run_engine


def _quick_stop(*args: Any, **kwargs: Any) -> Any:
    """``run_engine`` with a one-second grace, so a budget stop is quick."""
    return _REAL_RUN_ENGINE(*args, **{**kwargs, "grace_s": (1.0, 1.0)})


@pytest.mark.usefixtures("no_git_locators")
class TestEndToEnd:
    def test_two_nights_carry_the_state_and_close_the_cycle(self, repo: Path, tmp_path: Path) -> None:
        code, record, calls = _night(repo, tmp_path, 1, (
            "    vera.m.x_f__mutmut_1: killed\n    vera.m.x_f__mutmut_2: survived\n"
            "    vera.m.x_g__mutmut_1: killed\n    vera.m.x_g__mutmut_2: not checked\n"))
        assert code == 0 and record["stopped"] is None
        assert [(p["lines"], p["mutants"]) for p in record["planned"]] == [([1, 2], 2), ([1, 2], 2)]
        lines = {"1": 1, "2": 1}
        assert record["counts"] == {"vera/m.py::x_f": {"mutants": 2, "lines": lines},
                                    "vera/m.py::x_g": {"mutants": 2, "lines": lines}}  # the engine's count
        (run,) = [c for c in calls if c["args"][0] == "run"]
        assert run["args"][-4:] == ["vera.m.x_f__mutmut_1", "vera.m.x_f__mutmut_2", "vera.m.x_g__mutmut_1",
                                    "vera.m.x_g__mutmut_2"]
        assert run["args"][run["args"].index("--max-children") + 1] == "2"
        window = json.loads((tmp_path / "work1" / "window.json").read_text(encoding="utf-8"))
        assert window["exact"] is True and window["lines"] == {"vera/m.py": [1, 2, 5, 6]}  # f at 1, g at 5
        code, state = _stitch_cli(repo, tmp_path, 1, None)
        assert code == 0 and state["cycle"] == 1
        assert state["units"]["vera/m.py::x_g"] == {"hash": state["units"]["vera/m.py::x_g"]["hash"],
                                                    "mutants": 2, "lines": lines, "window": None,
                                                    "partial": {"decided": {"1": "killed"}, "survivors": []}}
        assert state["units"]["vera/m.py::x_f"]["window"] == {
            "killed": 1, "survived": 1, "timeout": 0, "no_tests": 0, "slow": 0, "other": 0, "mutants": 2,
            "survivors": [{"n": 2, "line": 2, "text_sha": sw.line_hash("    return x + 1"), "status": "survived",
                           "files": []}]}

        code, record, calls = _night(repo, tmp_path, 2, (
            "    vera.m.x_g__mutmut_1: killed\n    vera.m.x_g__mutmut_2: killed\n"),
            state=tmp_path / "state1")
        assert code == 0 and record["state_in"] == sw.state_digest(tmp_path / "state1" / sw.STATE_FILE)
        assert record["counts"] == {}  # the state carried the counts
        (run,) = [c for c in calls if c["args"][0] == "run"]
        assert run["args"][-1:] == ["vera.m.x_g__mutmut_2"]  # the one mutant the first night left
        assert record["planned"] == [{"unit": "vera/m.py::x_g", "hash": record["planned"][0]["hash"],
                                      "lines": [1, 2], "mutants": 2, "todo": [2]}]
        assert record["results"]["vera/m.py::x_g"]["decided"] == {"2": "killed"}
        code, state = _stitch_cli(repo, tmp_path, 2, tmp_path / "state1")
        assert code == 0 and state["cycle"] == 2
        assert state["last_complete"]["modules"]["vera/m.py"]["survived"] == 1
        assert (tmp_path / "state2" / "mutation-summary.csv").read_text(encoding="utf-8").splitlines()[-1] == (
            "TOTAL (vera),4,3,1,0,75.0,4,30.1,95.4")

    def test_the_copy_holds_the_whole_tree_and_the_oracle_every_admitted_test(
        self, repo: Path, tmp_path: Path,
    ) -> None:
        (repo / "README.md").write_text("read by a test\n", encoding="utf-8")
        _git(repo, "add", "-A")
        _git(repo, "commit", "-q", "-m", "readme")
        _night(repo, tmp_path, 1, "    vera.m.x_f__mutmut_1: killed\n    vera.m.x_f__mutmut_2: killed\n    vera.m.x_g__mutmut_1: killed\n    vera.m.x_g__mutmut_2: killed\n")
        import tomllib

        cfg = tomllib.loads((tmp_path / "work1" / "tree" / "pyproject.toml").read_text(encoding="utf-8"))
        assert cfg["tool"]["mutmut"]["also_copy"] == ["README.md", "pyproject.toml", "tests"]
        assert cfg["tool"]["mutmut"]["pytest_add_cli_args_test_selection"] == ["tests/test_m.py"]
        assert cfg["tool"]["mutmut"]["only_mutate"] == ["vera/m.py"]

    def test_a_test_that_fails_in_the_copy_is_dropped_and_reported(
        self, repo: Path, tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        monkeypatch.setenv("FAKE_COPY_FAILURE", "tests/test_m.py::test_f")
        code, record, calls = _night(repo, tmp_path, 1, (
            "    vera.m.x_f__mutmut_1: killed\n    vera.m.x_f__mutmut_2: killed\n    vera.m.x_g__mutmut_1: killed\n    vera.m.x_g__mutmut_2: killed\n"))
        assert code == 0 and record["dropped_tests"] == ["tests/test_m.py::test_f"]
        assert len([c for c in calls if c["args"][0] == "run"]) == 2

    def test_a_copy_failure_the_log_does_not_name_is_read_from_the_plugins_file(
        self, repo: Path, tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        """Under the fork server the stats pass's pytest output dies with
        its child, so the log holds no `FAILED` line (the three engine stops
        of 3 and 4 November 2026, #1829): the plugin's file names the test,
        and the slice drops it as before."""
        monkeypatch.setenv("FAKE_COPY_FAILURE", "tests/test_m.py::test_f")
        monkeypatch.setenv("FAKE_COPY_FAILURE_SILENT", "1")
        code, record, calls = _night(repo, tmp_path, 1, (
            "    vera.m.x_f__mutmut_1: killed\n    vera.m.x_f__mutmut_2: killed\n    vera.m.x_g__mutmut_1: killed\n    vera.m.x_g__mutmut_2: killed\n"))
        assert code == 0 and record["stopped"] is None
        assert record["dropped_tests"] == ["tests/test_m.py::test_f"]
        assert len([c for c in calls if c["args"][0] == "run"]) == 2

    def test_the_copy_caches_bytecode(self, repo: Path, tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
        """A mutated module compiles in tens of seconds and loads from its
        .pyc in a fifth of a second; under the fork server every pass and
        every mutant's worker is a fresh process (#1829)."""
        monkeypatch.setenv("PYTHONDONTWRITEBYTECODE", "1")  # the night's own shell may set it
        code, _, calls = _night(repo, tmp_path, 1, "    vera.m.x_f__mutmut_1: killed\n    vera.m.x_f__mutmut_2: killed\n    vera.m.x_g__mutmut_1: killed\n    vera.m.x_g__mutmut_2: killed\n")
        assert code == 0
        (run,) = [c for c in calls if c["args"][0] == "run"]
        assert run["bytecode_off"] is None

    def test_a_test_dropped_on_an_earlier_night_is_deselected_from_the_start(
        self, repo: Path, tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        """A drop costs a stats pass on every night that makes it again
        (#1827): the next night deselects the test before its first run and
        says so, and forgets a drop whose test file the tree no longer holds."""
        failing = "tests/test_m.py::test_f"
        monkeypatch.setenv("FAKE_COPY_FAILURE", failing)
        _night(repo, tmp_path, 1, ("    vera.m.x_f__mutmut_1: killed\n    vera.m.x_f__mutmut_2: killed\n"
                                   "    vera.m.x_g__mutmut_1: killed\n    vera.m.x_g__mutmut_2: not checked\n"))
        _stitch_cli(repo, tmp_path, 1, None)
        code, record, calls = _night(repo, tmp_path, 2, (
            "    vera.m.x_g__mutmut_1: killed\n    vera.m.x_g__mutmut_2: killed\n"), state=tmp_path / "state1")
        assert code == 0 and record["deselected_tests"] == [failing] and record["dropped_tests"] == []
        assert len([c for c in calls if c["args"][0] == "run"]) == 1
        assert f"Deselected from the oracle from the start, each dropped on an earlier night:\n- `{failing}`" in (
            sw.render_slice(record))
        _stitch_cli(repo, tmp_path, 2, tmp_path / "state1")
        _git(repo, "mv", "tests/test_m.py", "tests/test_n.py")
        _git(repo, "commit", "-q", "-m", "moved")
        code, record, calls = _night(repo, tmp_path, 3, (
            "    vera.m.x_f__mutmut_1: killed\n    vera.m.x_f__mutmut_2: killed\n"
            "    vera.m.x_g__mutmut_1: killed\n    vera.m.x_g__mutmut_2: killed\n"), state=tmp_path / "state2")
        assert code == 0 and record["deselected_tests"] == [] and record["dropped_tests"] == [failing]
        assert len([c for c in calls if c["args"][0] == "run"]) == 2

    def test_a_test_that_reads_the_source_is_kept_out_and_reported(
        self, repo: Path, tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        reader = "tests/test_scan.py::test_every_site_names_a_code"
        monkeypatch.setenv("FAKE_ORACLE_SOURCE_SKIPS", f"{reader},{reader}")
        monkeypatch.setenv("FAKE_ORACLE_SKIPS", "tests/test_cli_like.py::test_runs")
        code, record, _ = _night(repo, tmp_path, 1, "    vera.m.x_f__mutmut_1: killed\n    vera.m.x_f__mutmut_2: killed\n    vera.m.x_g__mutmut_1: killed\n    vera.m.x_g__mutmut_2: killed\n")
        assert code == 0 and record["source_tests"] == [reader]
        assert record["subprocess_tests"] == ["tests/test_cli_like.py::test_runs"]
        report = sw.render_slice(record)
        assert "1 test(s) read the compiler's source" in report and "1 test(s) started a Python" in report
        _, state = _stitch_cli(repo, tmp_path, 1, None)
        assert state["nights"][-1]["slices"][0]["source_tests"] == 1

    def test_the_engine_is_handed_eighty_columns_whatever_the_nights_terminal(
        self, repo: Path, tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        """pytest draws its rules the terminal's width, and the slice's
        engine_failure knows a rule by that width."""
        monkeypatch.setenv("COLUMNS", "60")
        code, record, calls = _night(repo, tmp_path, 1, (
            "    vera.m.x_f__mutmut_1: killed\n    vera.m.x_f__mutmut_2: killed\n    vera.m.x_g__mutmut_1: killed\n    vera.m.x_g__mutmut_2: killed\n"))
        assert code == 0
        (run,) = [c for c in calls if c["args"][0] == "run"]
        assert run["columns"] == "80"

    def test_the_engines_own_failure_stops_the_slice_names_it_and_drops_no_test(
        self, repo: Path, tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        """The night of 28 October 2026: every test of the stats pass errored
        at teardown in mutmut's own hook, and the slice dropped each one as a
        test failing in the copy until none was left.  The slice stops at its
        first attempt, and its record and the night's problems name the
        exception and the engine's frame."""
        log = tmp_path / "night.log"
        log.write_text(ENGINE_FAILURE_LOG, encoding="utf-8")
        monkeypatch.setenv("FAKE_RUN_LOG", str(log))
        monkeypatch.setenv("FAKE_COUNT", "1")  # the listing below is of one mutant
        code, record, calls = _night(repo, tmp_path, 1, "    vera.m.x_f__mutmut_1: not checked\n")
        assert (record["dropped_tests"], len([c for c in calls if c["args"][0] == "run"])) == ([], 1)
        assert code == 2 and record["stopped"] == "engine" and record["engine_error"] == ENGINE_ERROR
        sw.check_record(record)
        code, state = _stitch_cli(repo, tmp_path, 1, None)
        assert code == 2 and state["nights"][-1]["problems"] == [f"slice 0: stopped by the engine: {ENGINE_ERROR}"]

    def test_a_failed_listing_decides_nothing_and_the_counts_stay(
        self, repo: Path, tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        """Without mutmut's listing there is no evidence of any outcome; the
        counts are the visitor's, asked before the run, and stay."""
        monkeypatch.setenv("FAKE_RESULTS_EXIT", "1")
        code, record, _ = _night(repo, tmp_path, 1, "")
        assert code == 2 and record["stopped"] == "engine" and record["results"] == {}
        _, state = _stitch_cli(repo, tmp_path, 1, None)
        assert {r["mutants"] for r in state["units"].values()} == {2}
        assert all(r["window"] is None and r["lines"] == {"1": 1, "2": 1} for r in state["units"].values())

    def test_a_budget_stop_before_the_first_mutant_is_a_normal_stop(
        self, repo: Path, tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        """A run the budget stopped before any mutant was decided lists at
        most what mutmut generated and decides nothing: the slice exits 0,
        and the night notes the stop; only a second such night is red
        (#1838)."""
        monkeypatch.setenv("FAKE_RUN_SLEEP", "30")
        monkeypatch.setenv("FAKE_COUNT", "1")
        monkeypatch.setattr(sw.md, "run_engine", lambda *a, **k: _quick_stop(*a, **k))
        monkeypatch.setattr(sw, "FIXED_S", 0)
        monkeypatch.setattr(sw, "OTHER_RATE_S", 0.01)  # both functions fit the two-second budget
        code, record, _ = _night(repo, tmp_path, 1, "    vera.m.x_f__mutmut_1: not checked\n", budget=2)
        assert [p["unit"] for p in record["planned"]] == ["vera/m.py::x_f", "vera/m.py::x_g"]
        assert record["stopped"] == "budget" and code == 0
        assert record["results"] == {}  # x_f's window undecided, x_g's not listed: both wait
        code, state = _stitch_cli(repo, tmp_path, 1, None)
        assert code == 0 and state["nights"][-1]["problems"] == []
        assert state["nights"][-1]["notes"] == ["slice 0: stopped by the budget with 0 mutant(s) decided; the rest "
                                                "of its bin waits for the next night"]

    def test_a_listing_that_maps_to_no_planned_window_is_red_after_a_budget_stop_too(
        self, repo: Path, tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        """A mutant of a function the night did not plan means the narrowing
        or the window went wrong: that outranks the budget, which leaves a
        slice only incomplete, as the diff lane's ``failed`` has it."""
        monkeypatch.setenv("FAKE_RUN_SLEEP", "30")
        monkeypatch.setattr(sw.md, "run_engine", lambda *a, **k: _quick_stop(*a, **k))
        code, record, _ = _night(repo, tmp_path, 1, "    vera.m.x_h__mutmut_1: killed\n", budget=2)
        assert record["stopped"] == "unmapped" and code == 2
        assert "did not plan" in record["engine_tail"][0]

    def test_an_engine_that_failed_before_generating_decides_nothing(
        self, repo: Path, tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        """R86's first repro: the run exits 2 before generating and the
        listing fails.  The night is red, the counts (the visitor's, asked
        before the run) stay, and the next night plans both functions
        again."""
        monkeypatch.setenv("FAKE_RUN_EXIT", "2")
        monkeypatch.setenv("FAKE_RESULTS_EXIT", "1")
        code, record, _ = _night(repo, tmp_path, 1, "")
        assert code == 2 and record["stopped"] == "engine" and record["results"] == {}
        code, state = _stitch_cli(repo, tmp_path, 1, None)
        assert code == 2 and {r["mutants"] for r in state["units"].values()} == {2}
        monkeypatch.delenv("FAKE_RUN_EXIT")
        monkeypatch.delenv("FAKE_RESULTS_EXIT")
        _, record, _ = _night(repo, tmp_path, 2, "    vera.m.x_f__mutmut_1: killed\n    vera.m.x_f__mutmut_2: killed\n    vera.m.x_g__mutmut_1: killed\n    vera.m.x_g__mutmut_2: killed\n",
                              state=tmp_path / "state1")
        assert [p["unit"] for p in record["planned"]] == ["vera/m.py::x_f", "vera/m.py::x_g"]

    def test_a_failed_listing_after_a_budget_stop_is_the_engines_failure(
        self, repo: Path, tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        """R86's second repro: the run overruns its budget and the listing
        fails.  That is not a budget stop: the night is red."""
        monkeypatch.setenv("FAKE_RUN_SLEEP", "30")
        monkeypatch.setenv("FAKE_RESULTS_EXIT", "1")
        monkeypatch.setattr(sw.md, "run_engine", lambda *a, **k: _quick_stop(*a, **k))
        code, record, _ = _night(repo, tmp_path, 1, "", budget=3)
        assert code == 2 and record["stopped"] == "engine" and record["results"] == {}
        code, state = _stitch_cli(repo, tmp_path, 1, None)
        assert code == 2 and all(r["window"] is None for r in state["units"].values())

    def test_a_status_a_budget_stop_left_stays_undecided(
        self, repo: Path, tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        """The night hands its budget stop to the reading of the listing: a
        `segfault` a stop can leave is not taken from a stopped run."""
        monkeypatch.setenv("FAKE_RUN_SLEEP", "30")
        monkeypatch.setattr(sw.md, "run_engine", lambda *a, **k: _quick_stop(*a, **k))
        monkeypatch.setattr(sw, "FIXED_S", 0)
        monkeypatch.setattr(sw, "OTHER_RATE_S", 0.01)
        _, record, _ = _night(repo, tmp_path, 1, (
            "    vera.m.x_f__mutmut_1: segfault\n    vera.m.x_f__mutmut_2: killed\n"), budget=2)
        assert record["stopped"] == "budget"
        assert record["results"]["vera/m.py::x_f"]["decided"] == {"2": "killed"}  # the segfault is the stop's

    def test_the_slice_prints_a_heartbeat_while_the_engine_runs(
        self, repo: Path, tmp_path: Path, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str],
    ) -> None:
        import threading

        monkeypatch.setenv("FAKE_RUN_SLEEP", "0.9")
        threads = threading.active_count()
        code, record, _ = _night(repo, tmp_path, 1, (
            "    vera.m.x_f__mutmut_1: killed\n    vera.m.x_f__mutmut_2: killed\n"
            "    vera.m.x_g__mutmut_1: killed\n    vera.m.x_g__mutmut_2: killed\n"),
            extra=["--heartbeat", "0.2"])
        assert code == 0 and record["stopped"] is None
        beats = [line for line in capsys.readouterr().out.splitlines() if line.startswith("heartbeat +0:00")]
        assert len(beats) >= 2, beats
        assert threading.active_count() == threads  # it stopped with the engine
        if sys.platform == "linux":  # the runners' platform: /proc is read
            assert all("mem avail" in b and "swap used" in b and "load" in b for b in beats), beats

    def test_a_lane_that_fails_before_the_sweep_leaves_a_record_the_stitch_reports(
        self, repo: Path, tmp_path: Path,
    ) -> None:
        out = tmp_path / "slice"
        state_dir = tmp_path / "state-in"
        sw.save_state(sw.empty_state("2026-10-16"), state_dir)
        args = ["lane-failed", "--slice", "1", "--of", "2", "--repo", str(repo), "--out", str(out),
                "--state", str(state_dir), "--why", "a step before the sweep failed"]
        assert sw.main(args) == 0
        record = json.loads((out / "slice-1.json").read_text(encoding="utf-8"))
        sw.check_record(record)
        assert record["stopped"] == "lane" and record["engine_tail"] == ["a step before the sweep failed"]
        assert record["head"] == _git(repo, "rev-parse", "HEAD").strip()
        assert record["state_in"] == sw.state_digest(state_dir / sw.STATE_FILE) and record["planned"] == []
        code = sw.main(["stitch", "--of", "2", "--repo", str(repo), "--slices", str(out),
                        "--state", str(state_dir), "--out", str(tmp_path / "state-out")])
        night = json.loads((tmp_path / "state-out" / sw.STATE_FILE).read_text(encoding="utf-8"))["nights"][-1]
        assert code == 2 and night["lost"] == [0]
        assert night["problems"] == ["slice 1: stopped by the lane: a step before the sweep failed"]
        # A record the sweep wrote itself is left alone.
        (out / "slice-1.json").write_text('{"kept": true}', encoding="utf-8")
        assert sw.main(args) == 0
        assert json.loads((out / "slice-1.json").read_text(encoding="utf-8")) == {"kept": True}

    def test_a_failure_of_the_lane_is_a_record_with_exit_two(self, repo: Path, tmp_path: Path) -> None:
        broken = tmp_path / "broken_engine.py"
        broken.write_text("raise SystemExit(3)\n", encoding="utf-8")
        code, record, _ = _night(repo, tmp_path, 1, "", engine=[sys.executable, str(broken)])
        assert code == 2 and record["stopped"] == "lane"
        assert "version" in record["engine_tail"][0]

    @starts_the_engine(900)
    def test_mutmut_itself_keeps_a_stopped_nights_mutants_and_runs_only_the_rest_the_next(
        self, held_repo: Path, tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        """Against the engine (#1838): a night the budget stops inside a
        window keeps each mutant it decided, the next night hands the engine
        the undecided remainder alone, the two nights' decisions are the
        whole window, and no mutant is decided twice."""
        pytest.importorskip("mutmut")
        monkeypatch.setenv("SWEEP_FIXTURE_HOLD", "vera.m.x_g__mutmut_1")
        monkeypatch.setenv("SWEEP_FIXTURE_HOLD_S", "900")
        monkeypatch.setattr(sw.md, "run_engine", lambda *a, **k: _quick_stop(*a, **k))
        monkeypatch.setattr(sw, "FIXED_S", 0)
        monkeypatch.setattr(sw, "OTHER_RATE_S", 0.01)  # both functions fit the 45 s budget's one job
        code, first, _ = _night(held_repo, tmp_path, 1, "", real=True, budget=45)
        assert code == 0 and first["stopped"] == "budget", _engine_said(tmp_path, 1, first)
        window = {p["unit"]: p["mutants"] for p in first["planned"]}
        assert set(window) == {"vera/m.py::x_f", "vera/m.py::x_g"}
        decided = {ident: set(r["decided"]) for ident, r in first["results"].items()}
        assert "1" not in decided.get("vera/m.py::x_g", set())  # held past the budget: undecided
        assert sum(map(len, decided.values())) == sum(window.values()) - 1, (window, decided,
                                                                              _engine_said(tmp_path, 1, first))
        code, state = _stitch_cli(held_repo, tmp_path, 1, None)
        assert code == 0 and state["units"]["vera/m.py::x_g"]["window"] is None
        monkeypatch.delenv("SWEEP_FIXTURE_HOLD")
        code, second, calls = _night(held_repo, tmp_path, 2, "", real=True, state=tmp_path / "state1", budget=300)
        assert code == 0 and second["stopped"] is None, _engine_said(tmp_path, 2, second)
        assert [(p["unit"], p["todo"]) for p in second["planned"]] == [("vera/m.py::x_g", [1])]
        assert {i: set(r["decided"]) for i, r in second["results"].items()} == {"vera/m.py::x_g": {"1"}}
        code, state = _stitch_cli(held_repo, tmp_path, 2, tmp_path / "state1")
        assert code == 0 and state["cycle"] == 2  # the union is the whole sample
        assert state["last_complete"]["sampled"] == sum(window.values())
        assert state["nights"][-1]["moved"] == 1

    @starts_the_engine(600)
    def test_mutmut_itself_ends_a_mutant_at_the_cap_as_slow_and_goes_on(
        self, held_repo: Path, tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        """Against the engine: a mutant whose covering test sleeps past a
        2 s cap is ended by the oracle plugin, recorded `slow`, and the run
        goes on to decide every other mutant; the stitch counts it apart."""
        pytest.importorskip("mutmut")
        monkeypatch.setenv("SWEEP_FIXTURE_HOLD", "vera.m.x_g__mutmut_1")
        monkeypatch.setenv("SWEEP_FIXTURE_HOLD_S", "60")
        code, record, _ = _night(held_repo, tmp_path, 1, "", real=True, extra=["--mutant-cap", "2"], budget=300)
        assert code == 0 and record["stopped"] is None, _engine_said(tmp_path, 1, record)
        assert record["slow"] == ["vera.m.x_g__mutmut_1"], _engine_said(tmp_path, 1, record)
        assert record["results"]["vera/m.py::x_g"]["decided"]["1"] == "slow"
        window = {p["unit"]: p["mutants"] for p in record["planned"]}
        assert {i: len(r["decided"]) for i, r in record["results"].items()} == window  # it went on
        assert "1" not in record["results"]["vera/m.py::x_g"]["durations"]  # the cap's exit wrote no end
        # Each run's start and end are the plugin's lines, so every mutant
        # whose run ended of its own accord has a measured duration, where
        # the fork server reports zero; the slow one, which the cap's exit
        # ended, has none.
        for result in record["results"].values():
            ended = {n for n, s in result["decided"].items() if s != sw.SLOW}
            assert set(result["durations"]) == ended and all(
                d > 0 for d in result["durations"].values()), result
        code, state = _stitch_cli(held_repo, tmp_path, 1, None)
        assert code == 0 and state["last_complete"]["modules"]["vera/m.py"]["slow"] == 1
        assert any(s.endswith(":slow") for s in state["last_complete"]["survivors"])

    @starts_the_engine(600)
    def test_mutmut_itself_generates_exactly_the_names_a_windowed_night_hands_it(
        self, held_repo: Path, tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        """Against the engine: in a run over a window of some lines, the
        names the night hands mutmut are the names it generates, numbered
        from one in the order of the window's lines."""
        pytest.importorskip("mutmut")
        monkeypatch.setattr(sw, "in_sample", lambda cycle, ident, line: line != 3)  # f's `return x + 1` out
        assert HELD_MODULE.splitlines()[2].strip() == "return x + 1"
        code, record, _ = _night(held_repo, tmp_path, 1, "", real=True, budget=300)
        assert code == 0 and record["stopped"] is None, _engine_said(tmp_path, 1, record)
        assert {p["unit"]: p["todo"] for p in record["planned"]} == {
            u: list(range(1, n + 1)) for u, n in {p["unit"]: p["mutants"] for p in record["planned"]}.items()}
        generated = {f"vera.m.{p['unit'].split('::')[1]}__mutmut_{n}" for p in record["planned"] for n in p["todo"]}
        listed = sw.md._engine_call(sw.md._default_engine(), ["results", "--all", "true"],
                                    cwd=tmp_path / "work1" / "tree", env=sw.md._git_env())
        assert listed is not None and listed.returncode == 0, listed
        assert set(sw.md.parse_results(listed.stdout)) == generated  # the window, numbered from one
        assert all(len(r["decided"]) == r["window"] for r in record["results"].values()), (
            record["results"], _engine_said(tmp_path, 1, record))  # every name handed was one generated

    @starts_the_engine(600)
    def test_mutmut_itself_decides_a_night(self, repo: Path, tmp_path: Path) -> None:
        """Against the engine, under the fork server: its ``count`` is what
        mutmut generates for each function, mutmut runs the planned mutants
        by name in the narrowed tree, and the stitch closes the cycle."""
        pytest.importorskip("mutmut")
        code, record, _ = _night(repo, tmp_path, 1, "", real=True, budget=300)
        assert code == 0 and record["stopped"] is None, _engine_said(tmp_path, 1, record)
        results = record["results"]
        assert set(results) == {"vera/m.py::x_f", "vera/m.py::x_g"}
        for ident, r in results.items():
            counted = record["counts"][ident]
            assert r["window"] == counted["mutants"] == sum(counted["lines"].values()) >= 1
            assert r["lines"] == sorted(int(line) for line in counted["lines"])  # every line sampled
            assert set(r["decided"].values()) == {"killed"} and len(r["decided"]) == r["window"]
            # No oracle plugin here, so no run's start is recorded, and the
            # fork server reports every duration as zero: none is a measure.
            assert r["survivors"] == [] and r["durations"] == {}
        code, state = _stitch_cli(repo, tmp_path, 1, None)
        assert code == 0 and state["cycle"] == 2 and state["last_complete"]["modules"]["vera/m.py"]["survived"] == 0
        assert state["last_complete"]["sampled"] == state["last_complete"]["population"] == sum(
            c["mutants"] for c in record["counts"].values())


# ---------------------------------------------------------------------------
# A slice that survives its runner: legs, the memory bound, `memory`, `lost`
# ---------------------------------------------------------------------------


def _planned(unit: Any, n: int, todo: list[int] | None = None) -> dict[str, Any]:
    """A slice's plan for a unit's whole window of ``n`` mutants, one a line."""
    return {"unit": unit.ident, "hash": H, "lines": list(range(1, n + 1)), "mutants": n,
            "todo": list(range(1, n + 1)) if todo is None else todo}


def _leg(slice_: int, of: int, results: dict[str, Any], *, leg: int = 3, running: bool = True,
         in_flight: list[str] | None = None, planned: list[dict[str, Any]] | None = None,
         age: float = sw.HEARTBEAT_S) -> dict[str, Any]:
    """A leg of a slice: its partial record as the workflow uploaded it,
    each mutant in flight having run ``age`` seconds when it was written."""
    record = _record(slice_, of, results, counts={})
    record.update(leg=leg, engine_running=running, in_flight=in_flight or [], elapsed_s=leg * sw.LEG_S,
                  in_flight_s={n: age for n in in_flight or []})
    if planned is not None:
        record["planned"] = planned
    return record


def _legs(records: list[dict[str, Any]], legs: list[dict[str, Any]], state: dict[str, Any] | None = None, *,
          jobs: int = 2) -> tuple[dict[str, Any], dict[str, Any]]:
    return sw.stitch(state or _state(f=4), "none", records, jobs=jobs, head=HEAD, units=UNITS,
                     today="2026-11-12", legs=legs)


def _round_trip(state: dict[str, Any], tmp_path: Path) -> dict[str, Any]:
    loaded = sw.load_state(sw.save_state(state, tmp_path), "x")
    assert loaded == state
    return json.loads(json.dumps(loaded))


F3 = "vera.a.x_f__mutmut_3"  # A's window mutant 3


class TestLegs:
    """A lost runner uploads nothing after the loss and its job log is gone
    with it (run 43087350670, slice 0, 11 November 2026), so a slice's
    record goes up in legs as it runs, and the stitch keeps the last leg of a
    slice whose final record never came."""

    def test_a_leg_merges_like_a_final_record_and_the_slice_counts_lost(self) -> None:
        leg = _leg(1, 2, {A.ident: _res(A, window=4, killed=2)})
        state, night = _legs([_record(0, 2, {C.ident: _res(C, killed=2)})], [leg],
                             _state(f=4, g=2))
        assert night["lost"] == [1] and night["problems"] == [] and night["moved"] == 4
        assert state["units"][A.ident]["partial"]["decided"] == {"1": "killed", "2": "killed"}
        assert night["notes"] == ["slice 1: no record; its legs keep 2 mutant(s) decided (the last, leg 3, "
                                  "written 90 minutes in), and the rest of its work waits for the next night"]

    def test_a_final_record_beats_every_leg_of_its_slice(self) -> None:
        final = _record(1, 2, {A.ident: _res(A, window=4, killed=1)}, counts={})
        leg = _leg(1, 2, {A.ident: _res(A, window=4, killed=3)}, leg=9)
        state, night = _legs([_record(0, 2, {}), final], [leg])
        assert night["lost"] == [] and night["moved"] == 1
        assert state["units"][A.ident]["partial"]["decided"] == {"1": "killed"}

    def test_the_last_leg_of_a_lost_slice_is_the_one_taken(self) -> None:
        early = _leg(1, 2, {A.ident: _res(A, window=4, killed=1)}, leg=1)
        late = _leg(1, 2, {A.ident: _res(A, window=4, killed=3)}, leg=4)
        for legs in ([early, late], [late, early]):
            state, night = _legs([_record(0, 2, {})], legs)
            assert night["moved"] == 3 and state["units"][A.ident]["partial"]["decided"] == {
                "1": "killed", "2": "killed", "3": "killed"}

    def test_a_leg_of_another_head_or_state_stops_the_night_short(self) -> None:
        leg = _leg(1, 2, {A.ident: _res(A, window=4, killed=2)})
        _, night = _legs([_record(0, 2, {})], [{**leg, "head": "e" * 40}])
        assert night["problems"] == [f"slice 1: a leg the night cannot take: ran {'e' * 40}, not {HEAD}"]
        assert night["moved"] == 0 and night["lost"] == [1]

    def test_the_stitch_reads_finals_and_legs_apart(self, repo: Path, tmp_path: Path) -> None:
        """The final record's name is unchanged (`slice-<n>.json`); a leg is
        `slice-<n>-leg-<k>.json`, read only for a slice with no final."""
        slices = tmp_path / "slices"
        slices.mkdir()
        head = _git(repo, "rev-parse", "HEAD").strip()
        unit = "vera/m.py::x_f"
        result = {"hash": sw.inventory(sw.vera_sources(repo, head))[0].hash, "window": 2, "lines": [1, 2],
                  "decided": {"1": "killed"}, "survivors": [], "durations": {}, "estimates": {}}
        for name, record in (("slice-0.json", {**_record(0, 2, {}, head=head, counts={})}),
                             ("slice-1-leg-2.json", {**_record(1, 2, {unit: result}, head=head,
                                                               counts={unit: {"mutants": 2, "lines": {"1": 1, "2": 1}}}),
                                                     "leg": 2})):
            (slices / name).write_text(json.dumps(record), encoding="utf-8")
        assert sw.main(["stitch", "--of", "2", "--repo", str(repo), "--slices", str(slices),
                        "--out", str(tmp_path / "out")]) == 0
        state = json.loads((tmp_path / "out" / sw.STATE_FILE).read_text(encoding="utf-8"))
        assert state["nights"][-1]["lost"] == [1] and state["nights"][-1]["moved"] == 1
        assert state["units"][unit]["partial"]["decided"] == {"1": "killed"}


class TestLossRule:
    """A mutant in flight when its slice ended with neither the engine
    finishing nor the budget stopping it takes a loss; at two recorded
    losses it is decided `lost`: counted apart, listed, never caught and
    never survived."""

    def test_two_losses_decide_lost_and_one_does_not(self, tmp_path: Path) -> None:
        planned = [_planned(A, 4)]
        first, night = _legs([], [_leg(0, 1, {}, in_flight=[F3], planned=planned)], jobs=1)
        assert night["moved"] == 0 and first["units"][A.ident]["losses"] == {"3": 1}
        assert first["units"][A.ident]["partial"] is None
        first = _round_trip(first, tmp_path / "one")
        second, night = _legs([], [_leg(0, 1, {}, in_flight=[F3], planned=planned)], first, jobs=1)
        rec = second["units"][A.ident]
        assert night["moved"] == 1 and "losses" not in rec
        assert rec["partial"] == {"decided": {"3": "lost"}, "survivors": [_survivor(3, 3, "lost")]}
        _round_trip(second, tmp_path / "two")

    def test_a_lost_window_counts_lost_apart_and_scores_nothing(self, tmp_path: Path) -> None:
        state = _state(f=4)
        state["units"][A.ident]["partial"] = {"decided": {"1": "killed", "2": "killed", "4": "survived"},
                                              "survivors": [_survivor(4, 4, "survived")]}
        state["units"][A.ident]["losses"] = {"3": 1}
        state, _ = _legs([], [_leg(0, 1, {}, in_flight=[F3], planned=[_planned(A, 4)])], state, jobs=1)
        window = state["units"][A.ident]["window"]
        assert window["lost"] == 1 and window["killed"] == 2 and window["survived"] == 1
        assert "memory" not in window and "losses" not in state["units"][A.ident]
        _round_trip(state, tmp_path)
        assert sw.tally(state, [A])["vera/a.py"]["lost"] == 1

    def test_no_loss_for_a_finished_or_budget_stopped_slice_or_a_leg_whose_engine_had_stopped(self) -> None:
        planned = [_planned(A, 4)]
        for record in (_record(0, 1, {}, stopped=None, counts={}), _record(0, 1, {}, stopped="budget", counts={})):
            record.update(in_flight=[F3], in_flight_s={F3: sw.HEARTBEAT_S}, planned=planned)
            state, _ = _legs([record], [], jobs=1)
            assert "losses" not in state["units"][A.ident]
        state, _ = _legs([], [_leg(0, 1, {}, in_flight=[F3], planned=planned, running=False)], jobs=1)
        assert "losses" not in state["units"][A.ident]

    def test_an_engine_stop_with_a_mutant_in_flight_is_a_loss(self) -> None:
        record = _record(0, 1, {}, stopped="engine", counts={})
        record.update(in_flight=[F3], in_flight_s={F3: sw.HEARTBEAT_S}, planned=[_planned(A, 4)])
        state, night = _legs([record], [], jobs=1)
        assert state["units"][A.ident]["losses"] == {"3": 1}
        assert night["problems"] == ["slice 0: stopped by the engine"]

    def test_a_loss_needs_the_cycles_own_window_and_an_undecided_mutant(self) -> None:
        other = [{**_planned(A, 4), "lines": [1, 2, 3]}]
        state, _ = _legs([], [_leg(0, 1, {}, in_flight=[F3], planned=other)], jobs=1)
        assert "losses" not in state["units"][A.ident]
        state = _state(f=4)
        state["units"][A.ident]["partial"] = {"decided": {"3": "killed"}, "survivors": []}
        state, _ = _legs([], [_leg(0, 1, {}, in_flight=[F3], planned=[_planned(A, 4)])], state, jobs=1)
        assert "losses" not in state["units"][A.ident]

    def test_a_decision_clears_the_mutants_loss(self) -> None:
        state = _state(f=4)
        state["units"][A.ident]["losses"] = {"3": 1}
        state, _ = _legs([_record(0, 1, {A.ident: _res(A, window=4, killed=3)}, counts={})], [], state, jobs=1)
        assert "losses" not in state["units"][A.ident]

    def test_a_cycle_that_closes_forgets_its_losses(self) -> None:
        state = _state(f=4, m=0, g=0)
        state["units"][A.ident]["partial"] = {"decided": {"1": "killed", "2": "killed", "4": "killed"},
                                              "survivors": []}
        state["units"][A.ident]["losses"] = {"3": 1}
        state, night = _legs([], [_leg(0, 1, {}, in_flight=[F3], planned=[_planned(A, 4)])], state, jobs=1)
        assert night["closed"] and all("losses" not in r for r in state["units"].values())
        assert state["last_complete"]["modules"]["vera/a.py"]["lost"] == 1
        assert any(s.endswith(":lost") for s in state["last_complete"]["survivors"])

    def test_a_slice_lost_twice_on_one_plan_deciding_nothing_is_a_problem(self, tmp_path: Path) -> None:
        """Lost before any mutant was in flight (in the stats pass, say), a
        slice decides nothing, not even a loss's second strike; the second
        night it happens on the same plan is red, never silence."""
        planned = [_planned(A, 4)]
        first, night = _legs([], [_leg(0, 1, {}, running=False, planned=planned)], jobs=1)
        assert night["problems"] == [] and set(night["lost_plans"]) == {"0"}
        first = _round_trip(first, tmp_path)
        _, night = _legs([], [_leg(0, 1, {}, running=False, planned=planned)], json.loads(json.dumps(first)),
                         jobs=1)
        assert (f"slice 0 lost its runner on the plan a slice lost the night before ({A.ident}), and neither "
                "night decided a mutant of it") in night["problems"]
        other = [_planned(A, 4, todo=[1, 2])]
        _, night = _legs([], [_leg(0, 1, {}, running=False, planned=other)], json.loads(json.dumps(first)),
                         jobs=1)
        assert not any("lost its runner" in p for p in night["problems"])
        _, night = _legs([], [_leg(0, 1, {A.ident: _res(A, window=4, killed=1)}, running=False, planned=planned)],
                         json.loads(json.dumps(first)), jobs=1)
        assert night["problems"] == [] and "lost_plans" not in night

    def test_a_state_with_no_new_fact_is_shaped_as_before(self) -> None:
        """Schema 3 stays: each new field is written only when it holds a
        fact, so a state without one is what the reader before them reads,
        and one with a fact is one it refuses rather than misreads."""
        state = _written_state()
        for rec in state["units"].values():
            assert set(rec) == {"hash", "mutants", "lines", "window", "partial"}
            assert rec["window"] is None or not set(sw.OPTIONAL_COLUMNS) & set(rec["window"])
        assert all("lost_plans" not in n for n in state["nights"])


#: Window mutants 1 to 3 of PICK_A by name.
A1, A2, A3 = (f"vera.a.x_f__mutmut_{n}" for n in (1, 2, 3))


class TestMemoryAndTheStop:
    def test_a_segfault_the_kernel_ended_under_the_bound_is_memory(self) -> None:
        listing = {A1: "segfault", A2: "killed", A3: "segfault"}
        out = sw.slice_results([PICK_A], listing, GENERATED, cut_short=False, finished=True, memory={A1, A2})
        assert out[A.ident]["decided"] == {"1": "memory", "2": "killed", "3": "segfault"}
        assert out[A.ident]["survivors"] == [_survivor(3, 3, "memory")]

    def test_a_status_the_engine_recorded_before_the_stop_is_kept(self) -> None:
        listing = {A1: "segfault", A2: "suspicious", A3: "killed"}
        out = sw.slice_results([PICK_A], listing, GENERATED, cut_short=True, finished=False, kept={A1})
        assert out[A.ident]["decided"] == {"1": "segfault", "3": "killed"}  # 2 came after the stop

    def test_a_memory_mutant_is_counted_apart_and_never_scored(self, tmp_path: Path) -> None:
        state = _state(f=4, m=0, g=0)
        result = _res(A, killed=3)
        result["decided"]["4"] = "memory"
        result["window"] = 4
        result["lines"] = [1, 2, 3, 4]
        result["survivors"] = [_survivor(4, 4, "memory")]
        state, night = _legs([_record(0, 1, {A.ident: result}, counts={})], [], state, jobs=1)
        assert night["closed"] and state["last_complete"]["modules"]["vera/a.py"]["memory"] == 1
        sw.write_summary(state, tmp_path)
        assert (tmp_path / "mutation-summary.csv").read_text(encoding="utf-8").splitlines()[-1].startswith(
            "TOTAL (vera),3,3,0,0,100.0")


def _cgroup(tmp_path: Path, kills: int) -> Path:
    cgroup = tmp_path / "cg"
    cgroup.mkdir(exist_ok=True)
    (cgroup / "memory.events").write_text(f"low 0\nhigh 0\nmax 9\noom 1\noom_kill {kills}\n", encoding="utf-8")
    return cgroup


class TestTracker:
    """Attribution over a stand-in cgroup and stand-in processes: `memory`
    needs the bound's `oom_kill` count to have risen while the mutant's
    process disappeared, and its exit to be mutmut's -9.  Whether a process
    is there is the tracker's `alive`, a set of pids here, so the logic runs
    the same on every platform; `pid_alive` itself is tested on a real
    process below."""

    PIDS = (4101, 4102)

    def _tracker(self, tmp_path: Path, live: set[int], codes: dict[str, Any]) -> Any:
        path = tmp_path / "inflight.txt"
        path.write_text("".join(f"{name}\t{pid}\t1000.0\t1\n" for name, pid in zip((A1, A2), self.PIDS, strict=True))
                        + f"{A3}\t1\t", encoding="utf-8")  # a line not whole yet is left out
        return sw.Tracker(path, _cgroup(tmp_path, 0), lambda: dict(codes), alive=lambda pid: pid in live)

    def _end_line(self, tmp_path: Path, name: str, pid: int, end: float) -> None:
        with (tmp_path / "inflight.txt").open("r+", encoding="utf-8") as fh:
            text = fh.read()
            head, _, partial = text.rpartition("\n")
            fh.seek(0)
            fh.write(f"{head}\n{name}\t{pid}\t{end}\tend\n{partial}")

    def test_a_rise_with_the_runs_process_gone_is_memory(self, tmp_path: Path) -> None:
        live = set(self.PIDS)
        codes: dict[str, Any] = {A1: None, A2: None}
        tracker = self._tracker(tmp_path, live, codes)
        tracker.look(10.0)
        assert tracker.in_flight() == [A1, A2] and tracker.memory() == set()
        live.discard(self.PIDS[0])
        _cgroup(tmp_path, 1)
        codes[A1] = sw.KILLED
        tracker.look(20.0)
        assert tracker.memory() == {A1} and tracker.in_flight() == [A2]
        assert tracker.durations() == {}  # the kernel ended it: no end line, no duration
        assert tracker.events == [{"look": 2, "t": 20.0, "rise": 1, "gone": [A1]}]
        assert tracker.first_choice() == {"took": 2, "not": 0}

    def test_the_rise_may_come_at_the_look_after_the_process_went(self, tmp_path: Path) -> None:
        live = set(self.PIDS)
        codes: dict[str, Any] = {A1: None, A2: None}
        tracker = self._tracker(tmp_path, live, codes)
        tracker.look(10.0)
        live.discard(self.PIDS[0])
        codes[A1] = sw.KILLED
        tracker.look(20.0)
        assert tracker.memory() == set()
        _cgroup(tmp_path, 1)
        tracker.look(30.0)
        assert tracker.memory() == {A1}

    def test_no_rise_leaves_a_segfault_and_a_live_process_is_never_memory(self, tmp_path: Path) -> None:
        live = set(self.PIDS)
        codes: dict[str, Any] = {A1: None, A2: None}
        tracker = self._tracker(tmp_path, live, codes)
        tracker.look(10.0)
        live.discard(self.PIDS[0])
        codes[A1] = sw.KILLED  # RLIMIT_CPU's hard limit ends a run with -9 too
        tracker.look(20.0)
        tracker.look(30.0)
        assert tracker.memory() == set()
        _cgroup(tmp_path, 1)  # a rise with no run gone (the fork server, say)
        tracker.look(40.0)
        codes[A2] = sw.KILLED  # its process is still there
        tracker.look(50.0)
        assert tracker.memory() == set()

    def test_more_runs_gone_with_minus_nine_than_the_rise_decide_none(self, tmp_path: Path) -> None:
        live = set(self.PIDS)
        codes: dict[str, Any] = {A1: None, A2: None}
        tracker = self._tracker(tmp_path, live, codes)
        tracker.look(10.0)
        live.clear()
        codes.update({A1: sw.KILLED, A2: sw.KILLED})
        _cgroup(tmp_path, 1)
        tracker.look(20.0)
        assert tracker.memory() == set()

    def test_a_run_that_ended_with_a_verdict_is_never_memory(self, tmp_path: Path) -> None:
        live = set(self.PIDS)
        codes: dict[str, Any] = {A1: None, A2: None}
        tracker = self._tracker(tmp_path, live, codes)
        tracker.look(10.0)
        live.discard(self.PIDS[0])
        codes[A1] = 1  # killed by its tests as the kernel ended another process
        _cgroup(tmp_path, 1)
        tracker.look(20.0)
        assert tracker.memory() == set()

    def test_a_duration_is_the_runs_own_end_less_its_start(self, tmp_path: Path) -> None:
        """The plugin's end line, not the look that first saw the verdict:
        a look long after the run ended (a slow listing, `--heartbeat 0`'s
        one look at the slice's end) moves nothing (#1838, PR 1863's review)."""
        live = set(self.PIDS)
        codes: dict[str, Any] = {A1: None, A2: None}
        tracker = self._tracker(tmp_path, live, codes)
        tracker.look(10.0)
        self._end_line(tmp_path, A1, self.PIDS[0], 1000.25)
        live.discard(self.PIDS[0])
        codes.update({A1: 1, A2: sw.INTERRUPTED})  # A2: the cap ended it, so no end line
        live.discard(self.PIDS[1])
        tracker.look(4000.0)
        assert tracker.durations() == {A1: 0.25}
        assert sw.read_run_ends(tmp_path / "inflight.txt") == {(A1, self.PIDS[0]): 1000.25}
        assert [r[0] for r in sw.read_in_flight(tmp_path / "inflight.txt")] == [A1, A2]

    def test_a_run_in_flight_has_its_age_at_the_record(self, tmp_path: Path) -> None:
        tracker = self._tracker(tmp_path, set(self.PIDS), {A1: None, A2: 1})
        tracker.look(10.0)
        assert tracker.in_flight_ages(1450.0) == {A1: 450.0}

    def test_pid_alive_on_a_real_process(self) -> None:
        proc = subprocess.Popen([sys.executable, "-c", "import time; time.sleep(60)"])
        try:
            assert sw.pid_alive(proc.pid)
            assert proc.poll() is None  # asking does not end it (os.kill(pid, 0) would, on Windows)
        finally:
            proc.kill()
            proc.wait()
        assert not sw.pid_alive(proc.pid)

    def test_the_cgroup_and_its_bound_are_read_from_proc(self, tmp_path: Path) -> None:
        assert sw.own_cgroup("0::/system.slice/mutation-sweep-0.scope\n", tmp_path) == (
            tmp_path / "system.slice" / "mutation-sweep-0.scope")
        assert sw.own_cgroup("12:memory:/x\n", tmp_path) is None and sw.own_cgroup(None) is None
        cgroup = _cgroup(tmp_path, 3)
        (cgroup / "memory.max").write_text("13958643712\n", encoding="utf-8")
        (cgroup / "memory.swap.max").write_text("0\n", encoding="utf-8")
        bound = sw.read_bound(cgroup)
        assert bound == {"cgroup": str(cgroup), "memory_max": 13958643712, "swap_max": 0} and sw.bounded(bound)
        (cgroup / "memory.max").write_text("max\n", encoding="utf-8")
        assert not sw.bounded(sw.read_bound(cgroup)) and not sw.bounded(sw.read_bound(None))
        (cgroup / "memory.max").write_text("1\n", encoding="utf-8")
        (cgroup / "memory.swap.max").write_text("max\n", encoding="utf-8")
        assert not sw.bounded(sw.read_bound(cgroup)) and sw.oom_kills(cgroup) == 3


class TestScope:
    def test_the_bound_is_the_runners_memory_less_the_reserve(self) -> None:
        assert sw.memory_max_bytes(MEMINFO) == 16368832 * 1024 - sw.MEMORY_RESERVE_MIB * 2**20
        with pytest.raises(sw.md.LaneError, match="no MemTotal"):
            sw.memory_max_bytes("")
        with pytest.raises(sw.md.LaneError, match="leave nothing"):
            sw.memory_max_bytes("MemTotal: 1000 kB\n")

    def test_the_scope_command_bounds_memory_and_swap_and_keeps_the_user_and_the_environment(self) -> None:
        argv = sw.scope_command(["python", "x.py"], memory_max=1234, unit="u-1", uid=1001, gid=118,
                                env={"PATH": "/v/bin:/usr/bin", "HOME": "/home/runner"})
        assert argv == ["sudo", "-n", "--preserve-env", "systemd-run", "--scope", "--quiet", "--unit=u-1",
                        "--uid=1001", "--gid=118", "--property=MemoryMax=1234", "--property=MemorySwapMax=0",
                        "--property=OOMPolicy=continue", "--", "/usr/bin/env", "HOME=/home/runner",
                        "PATH=/v/bin:/usr/bin", "python", "x.py"]

    @pytest.mark.usefixtures("no_git_locators")
    def test_a_slice_that_requires_the_bound_and_lacks_it_is_a_lane_stop(
        self, repo: Path, tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        """The scheduled workflow keeps working only by failing loudly: a
        slice told to run under the bound that finds none never runs."""
        monkeypatch.setattr(sw, "own_cgroup", lambda text, root=None: None)
        code, record, calls = _night(repo, tmp_path, 1, "", extra=["--require-bound"])
        assert code == 2 and record["stopped"] == "lane" and not [c for c in calls if c["args"][0] == "run"]
        assert "the memory bound is not in place" in record["engine_tail"][0]

    def test_the_plugin_names_each_run_as_it_starts_and_makes_it_the_first_choice(self, tmp_path: Path) -> None:
        """In a process of its own: the choice cannot be taken back by an
        unprivileged process, and the test's own must not keep it."""
        import time

        import tests.mutation_oracle as plugin

        path = tmp_path / "inflight.txt"
        assert not plugin.mark_in_flight({"MUTANT_UNDER_TEST": "stats", plugin.INFLIGHT_ENV: str(path)})
        assert not plugin.mark_in_flight({"MUTANT_UNDER_TEST": A1})
        assert not path.exists()
        child = subprocess.run(
            [sys.executable, "-c",
             "import json, os, sys\n"
             f"sys.path.insert(0, {str(ROOT)!r})\n"
             "import tests.mutation_oracle as p\n"
             f"ok = p.mark_in_flight({{'MUTANT_UNDER_TEST': {A1!r}, p.INFLIGHT_ENV: {str(path)!r}}})\n"
             f"os.environ.update({{'MUTANT_UNDER_TEST': {A1!r}, p.INFLIGHT_ENV: {str(path)!r}}})\n"
             "p.pytest_sessionfinish(None, 0)  # the run's session ends: its end line\n"
             "adj = open('/proc/self/oom_score_adj').read().strip() if os.path.exists('/proc/self') else None\n"
             "print(json.dumps({'ok': ok, 'pid': os.getpid(), 'adj': adj}))\n"],
            capture_output=True, text=True, encoding="utf-8", check=True)
        seen = json.loads(child.stdout)
        ((name, pid, start, took),) = sw.read_in_flight(path)
        assert seen["ok"] and (name, pid) == (A1, seen["pid"]) and abs(start - time.time()) < 60
        assert list(sw.read_run_ends(path)) == [(A1, seen["pid"])] and sw.read_run_ends(path)[(A1, pid)] >= start
        assert not plugin.mark_end({"MUTANT_UNDER_TEST": "stats", plugin.INFLIGHT_ENV: str(path)})
        assert took is (sys.platform == "linux") and seen["adj"] == ("1000" if took else seen["adj"])


def _scope_prerequisites() -> str | None:
    """Why a real scope cannot be made here, or None."""
    if sys.platform != "linux":
        return "a systemd scope is Linux's"
    if not Path("/run/systemd/system").is_dir():
        return "systemd is not the init here"
    import shutil

    if shutil.which("sudo") is None or shutil.which("systemd-run") is None:
        return "no sudo or systemd-run"
    if subprocess.run(["sudo", "-n", "true"], capture_output=True, check=False).returncode != 0:
        return "sudo asks for a password here"
    return None


def _on_a_hosted_runner() -> bool:
    """A GitHub-hosted runner's own VM, outside any container: where the
    nightly sweep runs its slices, and where this test must run."""
    in_container = Path("/.dockerenv").exists() or Path("/run/.containerenv").exists()
    return (sys.platform == "linux" and os.environ.get("RUNNER_ENVIRONMENT") == "github-hosted"
            and not in_container)


#: Run under the scope: the night's own check of its bound
#: (`mutate_sweep.check_bound`, what `night --require-bound` runs before it
#: plans), then, with `hog`, a child that allocates until the kernel ends
#: it, and what the scope saw, as JSON.  Its own footprint is small, so the
#: kernel's choice is the child, which also makes itself the first choice
#: as a mutant's run does.
SCOPE_HARNESS = """
import json, os, subprocess, sys
sys.path.insert(0, sys.argv[1])
import mutate_sweep as sw
try:
    bound, refused = sw.check_bound(), None
except sw.md.LaneError as exc:
    bound, refused = None, str(exc)
cgroup = sw.own_cgroup(open("/proc/self/cgroup", encoding="utf-8").read())
before = sw.oom_kills(cgroup)
hog = None
if sys.argv[2] == "hog":
    hog = subprocess.run([sys.executable, "-c",
        "open('/proc/self/oom_score_adj', 'w').write('1000')\\n"
        "chunks = []\\n"
        "while True:\\n"
        "    chunks.append(bytearray(4 << 20))\\n"], check=False).returncode
print(json.dumps({"hog": hog, "before": before, "after": sw.oom_kills(cgroup), "bound": bound,
                  "refused": refused, "uid": os.getuid(), "gid": os.getgid(), "home": os.environ.get("HOME"),
                  "kept": os.environ.get("SWEEP_SCOPE_SENTINEL"), "path": os.environ.get("PATH")}))
"""


class TestARealScope:
    """The bound on a runner: the workflow's own builder (`scope_command`),
    a small MemoryMax, a child that allocates until the kernel ends it.  The
    night's own check of its bound accepts the scope, the parent under it
    lives, the scope's `oom_kill` count rises, the child ends by signal 9,
    and the user and the environment are the runner's; the same check
    refuses a scope with no bound on its swap.  It must run on a
    GitHub-hosted runner outside a container (it fails there when it
    cannot), and is skipped with its reason elsewhere."""

    def _run(self, tmp_path: Path, mode: str, *, drop: str | None = None) -> dict[str, Any]:
        harness = tmp_path / "harness.py"
        harness.write_text(SCOPE_HARNESS, encoding="utf-8")
        env = {k: os.environ[k] for k in sw.PINNED_ENV if k in os.environ}
        env["SWEEP_SCOPE_SENTINEL"] = "kept"
        argv = sw.scope_command([sys.executable, "-I", str(harness), str(ROOT / "scripts"), mode],
                                memory_max=self.LIMIT, unit=f"vera-sweep-scope-test-{mode}-{os.getpid()}",
                                uid=os.getuid(), gid=os.getgid(), env=env)
        argv = [a for a in argv if a != drop]
        done = subprocess.run(argv, capture_output=True, text=True, encoding="utf-8", timeout=300, check=False)
        assert done.returncode == 0, done.stderr
        seen: dict[str, Any] = json.loads(done.stdout.strip().splitlines()[-1])
        return seen

    LIMIT = 96 * 2**20

    def test_the_kernel_ends_the_child_and_the_parent_lives(self, tmp_path: Path) -> None:
        why = _scope_prerequisites()
        if why is not None:
            if _on_a_hosted_runner():
                pytest.fail(f"a hosted runner must be able to make the sweep's scope: {why}")
            pytest.skip(why)
        seen = self._run(tmp_path, "hog")
        assert seen["refused"] is None and sw.bounded(seen["bound"]), seen
        assert (seen["bound"]["memory_max"], seen["bound"]["swap_max"]) == (self.LIMIT, 0), seen
        assert seen["hog"] == -9, seen
        assert seen["after"] > seen["before"], seen
        assert (seen["uid"], seen["gid"]) == (os.getuid(), os.getgid()), seen
        assert seen["kept"] == "kept" and seen["home"] == os.environ.get("HOME"), seen
        assert seen["path"] == os.environ.get("PATH"), seen
        unbounded = self._run(tmp_path, "check", drop="--property=MemorySwapMax=0")
        assert unbounded["bound"] is None and "the memory bound is not in place" in unbounded["refused"], unbounded


def _alive(pid: int) -> bool:
    try:
        os.kill(pid, 0)
    except ProcessLookupError:
        return False
    except PermissionError:
        return True
    return True


class TestRunEngine:
    def test_any_interrupt_ends_the_engines_whole_process_group(
        self, tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        """The engine runs in a session of its own, so an exception that
        ends the wait (a keyboard interrupt, the slice's SIGTERM, a test's
        timeout) must end its group, its workers included (#1838, the
        review of #1846)."""
        if os.name != "posix":
            pytest.skip("process groups are POSIX's")
        import time

        pids = tmp_path / "pids"
        script = tmp_path / "engine.py"
        script.write_text(
            "import os, subprocess, sys, time\n"
            "child = subprocess.Popen([sys.executable, '-c', 'import time; time.sleep(120)'])\n"
            f"open({str(pids)!r}, 'w').write(f'{{os.getpid()}} {{child.pid}}')\n"
            "time.sleep(120)\n", encoding="utf-8")
        real = subprocess.Popen.wait
        calls = {"n": 0}

        def interrupted(self: Any, timeout: float | None = None) -> Any:
            calls["n"] += 1
            if calls["n"] == 1:
                deadline = time.monotonic() + 30
                while not pids.exists() and time.monotonic() < deadline:
                    time.sleep(0.05)
                raise KeyboardInterrupt
            return real(self, timeout=timeout)

        monkeypatch.setattr(subprocess.Popen, "wait", interrupted)
        with pytest.raises(KeyboardInterrupt):
            sw.md.run_engine([sys.executable, str(script)], cwd=tmp_path, budget_s=60,
                             log_path=tmp_path / "log", grace_s=(1.0, 1.0))
        monkeypatch.setattr(subprocess.Popen, "wait", real)
        engine, worker = (int(p) for p in pids.read_text(encoding="utf-8").split())
        deadline = time.monotonic() + 15
        while time.monotonic() < deadline and _alive(worker):
            time.sleep(0.1)
        alive = _alive(worker)
        for pid in (engine, worker):  # nothing outlives the test whatever it found
            try:
                os.kill(pid, 9)
            except OSError:
                pass
        assert not alive

    def test_the_budgets_stop_reads_the_run_before_any_signal(self, tmp_path: Path) -> None:
        seen: list[bool] = []
        log = tmp_path / "log"
        script = tmp_path / "engine.py"
        script.write_text("import time\nprint('ran', flush=True)\ntime.sleep(60)\n", encoding="utf-8")

        def before() -> None:
            seen.append("ran" in log.read_text(encoding="utf-8"))

        run = sw.md.run_engine([sys.executable, str(script)], cwd=tmp_path, budget_s=2.0, log_path=log,
                               grace_s=(1.0, 1.0), before_stop=before)
        assert run.stopped == "budget" and seen == [True]


class TestDurations:
    def test_a_night_of_zero_durations_leaves_the_calibration_where_it_was(self) -> None:
        """mutmut's fork server reports every mutant's duration as zero; a
        night of them moved the factor halfway to zero."""
        result = _res(A, killed=10)
        result["durations"] = {str(n): 0.0 for n in range(1, 11)}
        state = _state(f=10)
        state["calibration"] = 5.0
        record = {**_record(0, 1, {A.ident: result}), "workers": 2}
        state, _ = _stitch([record], state, jobs=1)
        assert state["calibration"] == 5.0
        result["durations"] = {str(n): 20.0 for n in range(1, 11)}
        state = _state(f=10)
        state["calibration"] = 5.0
        state, _ = _stitch([record], state, jobs=1)
        assert state["calibration"] == 4.5  # halfway from 5 to 4

    def test_a_zero_duration_is_not_recorded(self) -> None:
        out = sw.slice_results([PICK_A], {A1: "killed", A2: "killed", A3: "killed"}, GENERATED, cut_short=False,
                               finished=True, seconds={A1: (0.0, 1.0), A2: (3.5, 1.0)})
        assert out[A.ident]["durations"] == {"2": 3.5}


@pytest.mark.usefixtures("no_git_locators")
class TestTheSliceAcrossSteps:
    def test_the_partial_record_is_written_while_the_engine_runs(
        self, repo: Path, tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        """The stand-in engine copies the slice's partial record while it
        runs: the plan and the decisions listed so far are in it, the engine
        still running, the mutants it started in flight."""
        live = tmp_path / "live"
        snapshot = tmp_path / "snapshot.json"
        monkeypatch.setenv("FAKE_RUN_SLEEP", "2.5")
        monkeypatch.setenv("FAKE_INFLIGHT", "vera.m.x_g__mutmut_2")
        monkeypatch.setenv("FAKE_SNAPSHOT", os.pathsep.join([str(live / sw.PARTIAL_FILE), str(snapshot)]))
        code, record, _ = _night(repo, tmp_path, 1, (
            "    vera.m.x_f__mutmut_1: killed\n    vera.m.x_f__mutmut_2: killed\n"
            "    vera.m.x_g__mutmut_1: killed\n    vera.m.x_g__mutmut_2: not checked\n"),
            extra=["--heartbeat", "0.4", "--live", str(live)])
        assert code == 0
        partial = json.loads(snapshot.read_text(encoding="utf-8"))
        sw.check_record(partial)
        assert partial["engine_running"] is True and partial["in_flight"] == ["vera.m.x_g__mutmut_2"]
        assert {i: r["decided"] for i, r in partial["results"].items()} == {
            "vera/m.py::x_f": {"1": "killed", "2": "killed"}, "vera/m.py::x_g": {"1": "killed"}}
        assert partial["heartbeats"] and set(partial["heartbeats"][0]) == {
            "t", "mem_avail_mib", "swap_used_mib", "load1", "disk_free_mib", "procs", "bound_mib", "oom_kill"}
        assert json.loads((live / sw.EXIT_FILE).read_text(encoding="utf-8")) == {"code": 0}
        assert record["engine_running"] is False and record["in_flight"] == ["vera.m.x_g__mutmut_2"]

    def test_start_legs_and_finish_follow_a_slice_run_in_the_background(
        self, repo: Path, tmp_path: Path, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str],
    ) -> None:
        """The workflow's steps, on a slice started without the scope: the
        start returns once it runs, leg 0 keeps the plan, a later leg finds
        it finished and keeps nothing, and the finish gives its exit."""
        # The slice runs in a process of its own, at the committed sample
        # fraction: a one-function module whose lines the sample draws.
        monkeypatch.setattr(sw, "SAMPLE_FRACTION", 0.02)
        name, lines = next((f"f{i}", drawn) for i in range(5000) if (drawn := [
            line for line in (1, 2) if sw.in_sample(1, f"vera/m.py::x_f{i}", line)]))
        (repo / "vera" / "m.py").write_text(f"def {name}(x):\n    return x + 1\n", encoding="utf-8")
        (repo / "tests" / "test_m.py").write_text("def test_nothing():\n    pass\n", encoding="utf-8")
        _git(repo, "add", "-A")
        _git(repo, "commit", "-q", "-m", "one function")
        fake = tmp_path / "fake"
        fake.mkdir()
        (fake / "results.txt").write_text("".join(f"    vera.m.x_{name}__mutmut_{n}: killed\n"
                                                  for n in range(1, len(lines) + 1)), encoding="utf-8")
        (tmp_path / "fake_mutmut.py").write_text(FAKE_ENGINE, encoding="utf-8")
        monkeypatch.setenv("FAKE_STATE", str(fake))
        monkeypatch.setenv("FAKE_RUN_SLEEP", "3")
        live, out, legs = tmp_path / "live", tmp_path / "slice", tmp_path / "legs"
        assert sw.main(["start", "--slice", "0", "--live", str(live), "--no-bound", "--wait", "120", "--",
                        "--slice", "0", "--of", "1", "--repo", str(repo), "--out", str(out),
                        "--workdir", str(tmp_path / "work"), "--heartbeat", "0.3",
                        "--engine", sys.executable, str(tmp_path / "fake_mutmut.py")]) == 0
        assert sw.main(["leg", "--leg", "0", "--live", str(live), "--out", str(legs / "0"), "--poll", "0.2"]) == 0
        (zero,) = (legs / "0").glob("*.json")
        assert zero.name == "slice-0-leg-0.json"
        plan = json.loads(zero.read_text(encoding="utf-8"))
        assert plan["leg"] == 0 and [p["unit"] for p in plan["planned"]] == [f"vera/m.py::x_{name}"]
        sw.check_record(plan)
        summary = tmp_path / "summary.md"
        assert sw.main(["finish", "--live", str(live), "--summary", str(summary), "--poll", "0.2"]) == 0
        assert sw.main(["leg", "--leg", "1", "--live", str(live), "--out", str(legs / "1"), "--leg-s", "0"]) == 0
        assert not (legs / "1").exists()  # finished: the final record is the one uploaded
        assert json.loads((out / "slice-0.json").read_text(encoding="utf-8"))["stopped"] is None
        assert "## Mutation sweep: slice 0 of 1" in summary.read_text(encoding="utf-8")
        assert "heartbeat +0:00" in capsys.readouterr().out  # the slice's output reached this job's log

    def test_a_slice_whose_driver_ended_with_no_record_keeps_its_partial_decisions(
        self, repo: Path, tmp_path: Path,
    ) -> None:
        live, out = tmp_path / "live", tmp_path / "slice"
        head = _git(repo, "rev-parse", "HEAD").strip()
        partial = {**_record(0, 1, {}, head=head, counts={}), "in_flight": [], "engine_running": True}
        partial["results"] = {"vera/m.py::x_f": {"hash": "0" * 16, "window": 2, "lines": [1, 2],
                                                 "decided": {"1": "killed"}, "survivors": [], "durations": {},
                                                 "estimates": {}}}
        sw.write_atomically(live / sw.PARTIAL_FILE, partial)
        write_driver = {"pid": 2**22 + 12345}  # a process that is not there
        sw.write_atomically(live / sw.DRIVER_FILE, write_driver)
        assert sw.main(["finish", "--live", str(live), "--poll", "0.1"]) == 2
        assert sw.main(["lane-failed", "--slice", "0", "--of", "1", "--repo", str(repo), "--out", str(out),
                        "--live", str(live), "--why", "a step of the slice failed before it wrote its record"]) == 0
        record = json.loads((out / "slice-0.json").read_text(encoding="utf-8"))
        sw.check_record(record)
        assert record["stopped"] == "lane" and record["results"]["vera/m.py::x_f"]["decided"] == {"1": "killed"}
        assert record["engine_tail"] == ["a step of the slice failed before it wrote its record"]


class TestTheWorkflowsLegs:
    def _wf(self) -> dict[Any, Any]:
        data = yaml.safe_load(WORKFLOW.read_text(encoding="utf-8"))
        assert isinstance(data, dict)
        return data

    def test_every_leg_waits_then_uploads_whatever_happened_and_they_cover_the_budget(self) -> None:
        import re

        steps = self._wf()["jobs"]["sweep"]["steps"]
        names = [s.get("name", "") for s in steps]
        legs = [i for i, s in enumerate(steps) if "scripts/mutate_sweep.py leg" in s.get("run", "")]
        assert len(legs) == sw.LEGS + 1
        for k, i in enumerate(legs):
            assert re.search(rf"--leg {k}\b", steps[i]["run"]) and f'"$RUNNER_TEMP/legs/{k}"' in steps[i]["run"]
            upload = steps[i + 1]
            assert upload["uses"].startswith("actions/upload-artifact@") and upload["if"] == "always()"
            assert upload["with"] == {"name": f"mutation-sweep-slice-${{{{ matrix.slice }}}}-leg-{k}",
                                      "path": f"${{{{ runner.temp }}}}/legs/{k}/", "retention-days": 3,
                                      "if-no-files-found": "ignore"}
        assert names[legs[0] - 1] == "Start this slice under the memory bound"
        assert names[legs[-1] + 2] == "Mutate this slice of the night"
        # The last leg is within one leg of the budget's end, and the job's
        # timeout holds the budget, the grace and the steps around it.
        assert (sw.LEGS + 1) * sw.LEG_S >= sw.DEFAULT_BUDGET_S
        job = self._wf()["jobs"]["sweep"]
        assert sw.DEFAULT_BUDGET_S + 90 + 30 * 60 <= job["timeout-minutes"] * 60 <= 6 * 3600

    def test_the_final_record_keeps_its_name_and_the_stitch_reads_every_slice_artifact(self) -> None:
        steps = self._wf()["jobs"]["sweep"]["steps"]
        (final,) = [s for s in steps if s.get("name") == "Upload the slice's record"]
        assert final["with"] == {"name": "mutation-sweep-slice-${{ matrix.slice }}",
                                 "path": "${{ runner.temp }}/slice/", "retention-days": 7}
        (download,) = [s for s in self._wf()["jobs"]["stitch"]["steps"]
                       if s.get("name") == "Download the slices' records"]
        assert download["with"]["pattern"] == "mutation-sweep-slice-*" and download["with"]["merge-multiple"]

    def test_only_the_start_step_asks_for_sudo_and_it_runs_the_scope_builder(self) -> None:
        text = WORKFLOW.read_text(encoding="utf-8")
        assert "sudo" not in "\n".join(s.get("run", "") for j in self._wf()["jobs"].values() for s in j["steps"])
        assert "scripts/mutate_sweep.py start" in text and "--no-bound" not in text


# ---------------------------------------------------------------------------
# PR 1863's review: a leg never loses what an earlier one held; a failed leg
# never ends the slice; a cancelled run charges no loss; a loss needs a run
# that had lasted a heartbeat; the bound's check run where a night runs it
# ---------------------------------------------------------------------------


def _killed(*numbers: int) -> dict[str, Any]:
    """A's result with ``numbers`` killed, of its window of 4."""
    return {"hash": H, "window": 4, "lines": [1, 2, 3, 4], "decided": {str(n): "killed" for n in numbers},
            "survivors": [], "durations": {}, "estimates": {}}


class TestTheLegsUnion:
    """A lost slice's valid legs are taken together: a decision is final,
    so a mutant any of them decided is decided, and a later leg that holds
    less (its listing failed) takes nothing away."""

    def test_a_later_empty_leg_keeps_what_an_earlier_one_decided(self) -> None:
        """The review's probe: leg 4 holds mutants 1 to 3 killed, leg 5 is
        valid and empty."""
        legs = [_leg(1, 2, {A.ident: _killed(1, 2, 3)}, leg=4), _leg(1, 2, {}, leg=5)]
        for order in (legs, legs[::-1]):
            state, night = _legs([_record(0, 2, {})], order)
            assert night["moved"] == 3 and night["problems"] == []
            assert state["units"][A.ident]["partial"]["decided"] == {"1": "killed", "2": "killed", "3": "killed"}
            assert night["notes"][0].startswith("slice 1: no record; its legs keep 3 mutant(s) decided "
                                                "(the last, leg 5, written 150 minutes in)")

    def test_two_legs_that_disagree_leave_the_mutant_undecided_and_are_a_problem(self) -> None:
        early = _leg(1, 2, {A.ident: _killed(1, 2)}, leg=2)
        late = _res(A, window=4, killed=1, survived=1, survivors=("2@2:survived",))
        late["decided"] = {"1": "killed", "2": "survived", "3": "killed"}
        state, night = _legs([_record(0, 2, {})], [early, _leg(1, 2, {A.ident: late}, leg=3)])
        assert state["units"][A.ident]["partial"] == {"decided": {"1": "killed", "3": "killed"}, "survivors": []}
        assert night["problems"] == [f"slice 1: its legs disagree on mutant 2 of {A.ident} (leg 2: killed, "
                                     "leg 3: survived); it is left undecided"]

    def test_a_malformed_highest_leg_is_a_problem_and_the_valid_ones_are_taken(self) -> None:
        bad = {**_leg(1, 2, {A.ident: _killed(4)}, leg=6, in_flight=[F3]), "in_flight": ["not a mutant"]}
        legs = [_leg(1, 2, {A.ident: _killed(1)}, leg=2), _leg(1, 2, {A.ident: _killed(2)}, leg=4), bad]
        state, night = _legs([_record(0, 2, {})], legs)
        assert state["units"][A.ident]["partial"]["decided"] == {"1": "killed", "2": "killed"}
        assert len(night["problems"]) == 1 and night["problems"][0].startswith(
            "slice 1: a leg the night cannot take: a malformed record")
        assert "losses" not in state["units"][A.ident]  # in flight only in the leg refused

    def test_in_flight_is_the_highest_legs_and_a_later_decision_is_no_loss(self) -> None:
        """A mutant in flight at leg 2 and decided at leg 5 draws no loss:
        the union holds its decision; one in flight at the highest leg does."""
        legs = [_leg(1, 2, {}, leg=2, in_flight=[F3], planned=[_planned(A, 4)]),
                _leg(1, 2, {A.ident: _killed(3)}, leg=5, in_flight=["vera.a.x_f__mutmut_4"],
                     planned=[_planned(A, 4)])]
        state, _ = _legs([_record(0, 2, {})], legs)
        assert state["units"][A.ident]["partial"]["decided"] == {"3": "killed"}
        assert state["units"][A.ident]["losses"] == {"4": 1}


class TestTheLossNeedsARunThatHadLasted:
    """What a lost slice's last record says is all that is known of its
    end: a mutant whose run had just started there draws no loss."""

    def test_a_run_that_had_lasted_a_heartbeat_takes_a_loss_and_one_just_started_does_not(self) -> None:
        planned = [_planned(A, 4)]
        state, _ = _legs([], [_leg(0, 1, {}, in_flight=[F3], planned=planned, age=sw.HEARTBEAT_S)], jobs=1)
        assert state["units"][A.ident]["losses"] == {"3": 1}
        state, night = _legs([], [_leg(0, 1, {}, in_flight=[F3], planned=planned, age=sw.HEARTBEAT_S - 1)],
                             jobs=1)
        assert "losses" not in state["units"][A.ident] and set(night["lost_plans"]) == {"0"}
        record = _record(0, 1, {}, stopped="engine", counts={})
        record.update(in_flight=[F3], in_flight_s={F3: 3.0}, planned=planned)
        state, _ = _legs([record], [], jobs=1)
        assert "losses" not in state["units"][A.ident]
        record["in_flight_s"] = {}  # no age recorded: none is known
        state, _ = _legs([record], [], jobs=1)
        assert "losses" not in state["units"][A.ident]

    def test_a_record_holds_only_ages_of_its_mutants_in_flight(self) -> None:
        leg = _leg(0, 1, {}, in_flight=[F3])
        sw.check_record(leg)
        for bad in ({"vera.a.x_f__mutmut_4": 400.0}, {F3: -1.0}, [F3]):
            with pytest.raises(sw.StateError, match="time in flight"):
                sw.check_record({**leg, "in_flight_s": bad})


class TestACancelledRun:
    """A cancelled run's slices end with no final record, as a lost
    runner's do: the stitch is told the sweep job's result and charges no
    loss on a cancelled run."""

    def test_a_cancelled_run_charges_no_loss_and_keeps_the_decisions(self) -> None:
        planned = [_planned(A, 4)]
        leg = _leg(0, 1, {A.ident: _killed(1)}, in_flight=[F3], planned=planned)
        state, night = sw.stitch(_state(f=4), "none", [], jobs=1, head=HEAD, units=UNITS, today="2026-11-12",
                                 legs=[leg], cancelled=True)
        assert "losses" not in state["units"][A.ident] and night["moved"] == 1
        assert "the run was cancelled: no slice's end is a loss" in night["notes"]
        idle = _leg(0, 1, {}, running=False, planned=planned)
        _, night = sw.stitch(_state(f=4), "none", [], jobs=1, head=HEAD, units=UNITS, today="2026-11-12",
                             legs=[idle], cancelled=True)
        assert "lost_plans" not in night  # a cancel is no strike either
        engine = _record(0, 1, {}, stopped="engine", counts={})
        engine.update(in_flight=[F3], in_flight_s={F3: sw.HEARTBEAT_S}, planned=planned)
        state, _ = sw.stitch(_state(f=4), "none", [engine], jobs=1, head=HEAD, units=UNITS, today="2026-11-12",
                             cancelled=True)
        assert "losses" not in state["units"][A.ident]

    def test_a_lost_runner_still_takes_a_loss(self) -> None:
        leg = _leg(0, 1, {}, in_flight=[F3], planned=[_planned(A, 4)])
        state, _ = sw.stitch(_state(f=4), "none", [], jobs=1, head=HEAD, units=UNITS, today="2026-11-12",
                             legs=[leg], cancelled=False)
        assert state["units"][A.ident]["losses"] == {"3": 1}

    @pytest.mark.usefixtures("no_git_locators")
    def test_the_cli_reads_the_sweep_jobs_result(self, repo: Path, tmp_path: Path) -> None:
        head = _git(repo, "rev-parse", "HEAD").strip()
        unit = "vera/m.py::x_f"
        fn_hash = sw.inventory(sw.vera_sources(repo, head))[0].hash
        mutant = "vera.m.x_f__mutmut_2"
        leg = {**_record(0, 1, {}, head=head, counts={unit: {"mutants": 2, "lines": {"1": 1, "2": 1}}}),
               "leg": 3, "engine_running": True, "in_flight": [mutant], "in_flight_s": {mutant: sw.HEARTBEAT_S},
               "planned": [{"unit": unit, "hash": fn_hash, "lines": [1, 2], "mutants": 2, "todo": [1, 2]}]}
        for result, losses in (("cancelled", None), ("failure", {"2": 1})):
            slices = tmp_path / f"slices-{result}"
            slices.mkdir()
            (slices / "slice-0-leg-3.json").write_text(json.dumps(leg), encoding="utf-8")
            out = tmp_path / f"out-{result}"
            sw.main(["stitch", "--of", "1", "--repo", str(repo), "--slices", str(slices), "--out", str(out),
                     "--sweep-result", result])
            state = json.loads((out / sw.STATE_FILE).read_text(encoding="utf-8"))
            assert state["units"][unit].get("losses") == losses, result


@pytest.mark.usefixtures("no_git_locators")
class TestThePartialRecordIsMonotone:
    def test_a_listing_that_fails_keeps_the_last_results_read_whole(
        self, repo: Path, tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        """The first listing reads; every later one fails (a meta file met
        mid-write).  The partial record keeps the first's decisions and
        says when the listing failed; so does the final record, whose own
        listing failed too, under the engine's stop."""
        live = tmp_path / "live"
        snapshot = tmp_path / "snapshot.json"
        monkeypatch.setenv("FAKE_RUN_SLEEP", "2.5")
        monkeypatch.setenv("FAKE_RESULTS_FAIL_FROM", "2")
        monkeypatch.setenv("FAKE_SNAPSHOT", os.pathsep.join([str(live / sw.PARTIAL_FILE), str(snapshot)]))
        code, record, _ = _night(repo, tmp_path, 1, (
            "    vera.m.x_f__mutmut_1: killed\n    vera.m.x_f__mutmut_2: killed\n"
            "    vera.m.x_g__mutmut_1: killed\n    vera.m.x_g__mutmut_2: not checked\n"),
            extra=["--heartbeat", "0.4", "--live", str(live)])
        decided = {"vera/m.py::x_f": {"1": "killed", "2": "killed"}, "vera/m.py::x_g": {"1": "killed"}}
        partial = json.loads(snapshot.read_text(encoding="utf-8"))
        sw.check_record(partial)
        assert {i: r["decided"] for i, r in partial["results"].items()} == decided
        assert partial["results_at"] is not None and partial["listing_failed"]["why"] == "the listing exited 1"
        assert partial["listing_failed"]["at"] > partial["results_at"]
        assert code == 2 and record["stopped"] == "engine"
        sw.check_record(record)
        assert {i: r["decided"] for i, r in record["results"].items()} == decided


class TestAFailedLegNeverEndsTheSlice:
    def test_a_leg_that_raises_returns_zero_and_says_why(
        self, tmp_path: Path, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str],
    ) -> None:
        live = tmp_path / "live"
        sw.write_atomically(live / sw.STARTED_FILE, {"epoch": 0.0, "bound": None, "pid": 1})
        sw.write_atomically(live / sw.PARTIAL_FILE, _record(0, 1, {}))

        def full(path: Path, data: Any) -> None:
            raise OSError(28, "No space left on device")

        monkeypatch.setattr(sw, "write_atomically", full)
        assert sw.main(["leg", "--leg", "0", "--live", str(live), "--out", str(tmp_path / "legs"),
                        "--leg-s", "0.2", "--poll", "0.05"]) == 0
        assert "leg 0: failed, and the slice goes on: OSError" in capsys.readouterr().out

    def test_every_leg_and_upload_continues_on_error_and_the_finish_runs_whatever_they_did(self) -> None:
        steps = yaml.safe_load(WORKFLOW.read_text(encoding="utf-8"))["jobs"]["sweep"]["steps"]
        names = [s.get("name", "") for s in steps]
        start, finish = names.index("Start this slice under the memory bound"), names.index(
            "Mutate this slice of the night")
        between = steps[start + 1:finish]
        assert len(between) == 2 * (sw.LEGS + 1)
        for step in between:
            assert step.get("continue-on-error") is True, step["name"]
        # The finish runs when the steps up to the start succeeded, which no
        # leg can change, and never on a cancel; the final upload always.
        assert "if" not in steps[finish] and "continue-on-error" not in steps[finish]
        (upload,) = [s for s in steps if s.get("name") == "Upload the slice's record"]
        assert upload["if"] == "always()"

    def test_the_stitch_is_told_the_sweep_jobs_result(self) -> None:
        steps = yaml.safe_load(WORKFLOW.read_text(encoding="utf-8"))["jobs"]["stitch"]["steps"]
        (fold,) = [s for s in steps if s.get("name") == "Fold the night into the state"]
        assert fold["env"]["SWEEP_RESULT"] == "${{ needs.sweep.result }}"
        assert '--sweep-result "$SWEEP_RESULT"' in fold["run"]

    def test_the_jobs_timeout_holds_the_budget_the_grace_and_the_legs(self) -> None:
        """A job's own timeout reads to the stitch as a lost runner, so it
        must not arise: the last leg waits no longer than the budget from
        the slice's start, and the timeout holds the budget, the engine's
        grace (60 s and 30 s), its last listing, and the steps before the
        slice with room (the proof night's install and self-tests took 3 to
        4 minutes, run 43087350670)."""
        job = yaml.safe_load(WORKFLOW.read_text(encoding="utf-8"))["jobs"]["sweep"]
        assert sw.LEGS * sw.LEG_S <= sw.DEFAULT_BUDGET_S
        grace = 60 + 30
        assert sw.DEFAULT_BUDGET_S + grace + sw.md.ENGINE_CALL_TIMEOUT_S + 30 * 60 <= job["timeout-minutes"] * 60


class TestTheBoundsCheck:
    @pytest.mark.usefixtures("no_git_locators")
    def test_a_slice_whose_bound_holds_but_has_no_choom_is_a_lane_stop(
        self, repo: Path, tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        real = shutil.which
        monkeypatch.setattr(sw, "read_bound", lambda cgroup: {"cgroup": "/x", "memory_max": 1, "swap_max": 0})
        monkeypatch.setattr(sw.shutil, "which", lambda name, *a, **k: None if name == "choom" else real(name))
        code, record, calls = _night(repo, tmp_path, 1, "", extra=["--require-bound"])
        assert code == 2 and record["stopped"] == "lane" and not [c for c in calls if c["args"][0] == "run"]
        assert "choom is not on the path" in record["engine_tail"][0]


@pytest.mark.usefixtures("no_git_locators")
class TestNoDurationFromTheSlicesEnd:
    def test_with_no_heartbeat_the_one_look_at_the_end_measures_nothing(
        self, repo: Path, tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        """`--heartbeat 0` leaves one look, after the engine ends: a run
        whose start the plugin wrote and whose end it did not has no
        duration, where the slice's end less its start would be one."""
        monkeypatch.setenv("FAKE_RUN_SLEEP", "1.5")
        monkeypatch.setenv("FAKE_INFLIGHT", "vera.m.x_f__mutmut_1")
        monkeypatch.setenv("FAKE_META", 'vera/m.py={"vera.m.x_f__mutmut_1": 1}')
        code, record, _ = _night(repo, tmp_path, 1, (
            "    vera.m.x_f__mutmut_1: killed\n    vera.m.x_f__mutmut_2: killed\n"
            "    vera.m.x_g__mutmut_1: killed\n    vera.m.x_g__mutmut_2: killed\n"),
            extra=["--heartbeat", "0"])
        assert code == 0 and record["results"]["vera/m.py::x_f"]["decided"]["1"] == "killed"
        assert record["results"]["vera/m.py::x_f"]["durations"] == {}


# ---------------------------------------------------------------------------
# PR 1863's second review: what a stop leaves, a budget stop's failed
# listing, a driver that raised after the engine ran, one loss predicate
# ---------------------------------------------------------------------------


@pytest.mark.usefixtures("no_git_locators")
class TestAfterTheBudgetsStop:
    def _stopped_night(self, repo: Path, tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> Any:
        """A budget stop the engine takes 2 s to wind down from: the
        heartbeat lists it meanwhile, when `x_f`'s mutant 2 shows the
        `segfault` the stop leaves; the final listing then fails."""
        monkeypatch.setenv("FAKE_RUN_SLEEP", "60")
        monkeypatch.setenv("FAKE_RUN_TRAP_INT", "2")
        monkeypatch.setenv("FAKE_RESULTS_FAIL_AFTER_EXIT", "1")
        live = tmp_path / "live"
        code, record, _ = _night(repo, tmp_path, 1, (  # the budget plans x_f alone
            "    vera.m.x_f__mutmut_1: killed\n    vera.m.x_f__mutmut_2: not checked\n"),
            budget=1.5, extra=["--heartbeat", "0.3", "--live", str(live)])
        return code, record, live

    def test_a_status_the_stop_left_is_no_decision_in_any_record(
        self, repo: Path, tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        if os.name != "posix":
            pytest.skip("the stand-in engine winds down on SIGINT, the budget's stop on POSIX")
        code, record, live = self._stopped_night(repo, tmp_path, monkeypatch)
        assert code == 2 and record["stopped"] == "engine" and record["budget_stopped"] is True
        assert record["results"]["vera/m.py::x_f"]["decided"] == {"1": "killed"}, record["results"]
        partial = json.loads((live / sw.PARTIAL_FILE).read_text(encoding="utf-8"))
        assert partial["budget_stopped"] is True
        assert partial["results"]["vera/m.py::x_f"]["decided"] == {"1": "killed"}

    def test_a_budget_stop_whose_listing_failed_charges_no_loss(self) -> None:
        record = _record(0, 1, {}, stopped="engine", counts={})
        record.update(in_flight=[F3], in_flight_s={F3: sw.HEARTBEAT_S}, planned=[_planned(A, 4)],
                      budget_stopped=True)
        state, _ = _legs([record], [], jobs=1)
        assert "losses" not in state["units"][A.ident]
        assert "takes a loss" not in sw.render_slice(record)
        leg = {**_leg(0, 1, {}, in_flight=[F3], planned=[_planned(A, 4)]), "budget_stopped": True}
        state, _ = _legs([], [leg], jobs=1)  # a leg written in the stop's grace
        assert "losses" not in state["units"][A.ident]


@pytest.mark.usefixtures("no_git_locators")
class TestADriverThatRaisedAfterTheEngineRan:
    def test_its_record_keeps_the_last_partial_records_decisions(
        self, repo: Path, tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        def late(path: Path) -> list[str]:
            raise RuntimeError("after the engine")

        monkeypatch.setattr(sw.md, "skipped_tests", late)
        monkeypatch.setenv("FAKE_RUN_SLEEP", "1.5")
        live = tmp_path / "live"
        code, record, _ = _night(repo, tmp_path, 1, (
            "    vera.m.x_f__mutmut_1: killed\n    vera.m.x_f__mutmut_2: killed\n"
            "    vera.m.x_g__mutmut_1: killed\n    vera.m.x_g__mutmut_2: not checked\n"),
            extra=["--heartbeat", "0.3", "--live", str(live)])
        sw.check_record(record)
        assert code == 2 and record["stopped"] == "lane"
        assert record["engine_tail"] == ["RuntimeError: after the engine"]
        assert {i: r["decided"] for i, r in record["results"].items()} == {
            "vera/m.py::x_f": {"1": "killed", "2": "killed"}, "vera/m.py::x_g": {"1": "killed"}}


class TestOneLossPredicate:
    """The slice's report names a loss exactly where the stitch charges one."""

    def test_the_report_and_the_stitch_agree_on_every_stop(self) -> None:
        planned = [_planned(A, 4)]
        records: list[tuple[dict[str, Any], bool]] = []
        for stopped, budget, age, charged in (("engine", False, sw.HEARTBEAT_S, True),
                                              ("engine", False, 3.0, False),
                                              ("engine", True, sw.HEARTBEAT_S, False),
                                              ("lane", False, sw.HEARTBEAT_S, False),
                                              ("unmapped", False, sw.HEARTBEAT_S, False),
                                              ("budget", True, sw.HEARTBEAT_S, False)):
            record = _record(0, 1, {}, stopped=stopped, counts={})
            record.update(in_flight=[F3], in_flight_s={F3: age}, planned=planned, budget_stopped=budget)
            state, _ = _legs([record], [], jobs=1)
            assert ("losses" in state["units"][A.ident]) is charged, (stopped, budget, age)
            assert ("takes a loss" in sw.render_slice(record)) is charged, (stopped, budget, age)
            records.append((record, charged))
        for record, charged in records:
            assert sw.charged_in_flight(record) == ([F3] if charged else [])


# ---------------------------------------------------------------------------
# PR 1863's third review: what a listing showed before the stop is kept; a
# record says the stop was sent wherever it is written after it
# ---------------------------------------------------------------------------


@pytest.mark.usefixtures("no_git_locators")
class TestTheStopsEdges:
    def test_a_status_a_listing_showed_before_the_stop_is_kept_with_no_meta_file(
        self, repo: Path, tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        """mutmut's meta file can be mid-write when the stop is sent (it is
        written with a plain write), which hides its mutants' codes from
        ``before_stop``; here there is none at all.  The listing a heartbeat
        read before the stop showed the `segfault`, so it is the engine's own
        and the final record keeps it."""
        monkeypatch.setenv("FAKE_RUN_SLEEP", "60")
        code, record, _ = _night(repo, tmp_path, 1, (  # the budget plans x_f alone
            "    vera.m.x_f__mutmut_1: killed\n    vera.m.x_f__mutmut_2: segfault\n"),
            budget=1.5, extra=["--heartbeat", "0.3", "--live", str(tmp_path / "live")])
        assert record["stopped"] == "budget" and record["budget_stopped"] is True
        assert record["results"]["vera/m.py::x_f"]["decided"] == {"1": "killed", "2": "segfault"}

    def test_a_record_published_after_the_stop_says_so_though_its_listing_began_before(
        self, repo: Path, tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        """A heartbeat begins a 1 s listing before the stop and publishes
        after it: that record says the stop was sent, as does the record on
        disk as the engine exits, so a leg copying it charges no loss."""
        if os.name != "posix":
            pytest.skip("the stand-in engine winds down on SIGINT, the budget's stop on POSIX")
        live = tmp_path / "live"
        snapshot = tmp_path / "at-exit.json"
        monkeypatch.setenv("FAKE_RUN_SLEEP", "60")
        monkeypatch.setenv("FAKE_RUN_TRAP_INT", "2")
        monkeypatch.setenv("FAKE_RESULTS_SLEEP", "1")
        monkeypatch.setenv("FAKE_RESULTS_SLEEP_STOPPING", "5")
        monkeypatch.setenv("FAKE_SNAPSHOT", os.pathsep.join([str(live / sw.PARTIAL_FILE), str(snapshot)]))
        _night(repo, tmp_path, 1, "    vera.m.x_f__mutmut_1: killed\n    vera.m.x_f__mutmut_2: not checked\n",
               budget=1.0, extra=["--heartbeat", "0.3", "--live", str(live)])
        at_exit = json.loads(snapshot.read_text(encoding="utf-8"))
        assert at_exit["budget_stopped"] is True, at_exit.get("elapsed_s")
        assert sw.charged_in_flight({**at_exit, "leg": 4}) == []

    def test_the_report_says_a_cancelled_run_charges_no_loss(self) -> None:
        record = _record(0, 1, {}, stopped="engine", counts={})
        record.update(in_flight=[F3], in_flight_s={F3: sw.HEARTBEAT_S}, planned=[_planned(A, 4)])
        assert "each takes a loss unless the night's run was cancelled" in sw.render_slice(record)
