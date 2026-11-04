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
import subprocess
import sys
from pathlib import Path
from typing import Any

import pytest
import yaml

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


def _window(killed: int = 0, survived: int = 0, timeout: int = 0, no_tests: int = 0, other: int = 0,
            survivors: tuple[str, ...] = ()) -> dict[str, Any]:
    """A decided window: its columns, summing to its size, and its survivors."""
    return {"killed": killed, "survived": survived, "timeout": timeout, "no_tests": no_tests, "other": other,
            "mutants": killed + survived + timeout + no_tests + other, "survivors": list(survivors)}


def _decide(state: dict[str, Any], unit: Any, **window: Any) -> None:
    """Decide the unit's sampled window with the given columns."""
    state["units"][unit.ident]["window"] = _window(**window)


def _res(unit: Any, *, hash_: str = H, lines: list[int] | None = None, survivors: tuple[str, ...] = (),
         **columns: int) -> dict[str, Any]:
    """A slice's result for a unit's window: its columns summing to the
    window, over lines 1 to the window unless given."""
    statuses = {c: columns.get(c, 0) for c in sw.COLUMNS}
    window = sum(statuses.values())
    return {"hash": hash_, "window": window, "lines": list(range(1, window + 1)) if lines is None else lines,
            "statuses": statuses, "survivors": list(survivors)}


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
        assert state["units"][A.ident] == {"hash": "1" * 16, "mutants": None, "lines": None, "window": None}
        assert state["units"][B.ident] == {"hash": H, "mutants": 3, "lines": _lines(3), "window": _window(killed=3)}

    def test_a_new_engine_starts_every_function_afresh(self) -> None:
        """mutmut makes a function's mutants by its own rules, so a count,
        its lines and a decided window mean nothing under another version."""
        state = _state(f=4)
        _decide(state, A, killed=4)
        state = sw.reconcile(state, UNITS, "3.9.0")
        assert state["engine"] == "3.9.0"
        assert all(r == {"hash": H, "mutants": None, "lines": None, "window": None} for r in state["units"].values())

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
    "another schema": (_set("schema", 3), "not a schema 2 state"),
    "a field it does not have": (_set("extra", 1), "the state does not have exactly the fields"),
    "an engine that is not a version": (_set("engine", "3.8.0; touch /tmp/x"), "the engine version is malformed"),
    "a cycle of zero": (_set("cycle", 0), "the cycle is not a whole number"),
    "a cycle that is a flag": (_set("cycle", True), "the cycle is not a whole number"),
    "a start that is not a date": (_set("cycle_started", "yesterday"), "the cycle's start is malformed"),
    "a calibration out of range": (_set("calibration", 9.0), "the calibration is not a number from 0.2 to 5.0"),
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
    "a window's survivor that is not a mutant": (_set("units", A.ident, "window", "survivors", ["x; rm"]),
                                                 "survivor 'x; rm' is malformed"),
    "a decided window and no lines": (_set("units", A.ident, "lines", None), "has a decided window and no lines"),
    "a schema the state was not converted from": (_set("converted_from", 2), "the schema the state was converted from"),
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
        the stitch writes is a plain schema 2 state."""
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
        assert state["schema"] == 2 and state["converted_from"] == 1
        assert (state["cycle"], state["cycle_started"], state["engine"], state["calibration"]) == (
            2, "2026-11-05", "3.8.0", 1.5)
        assert state["units"][A.ident] == {"hash": H, "mutants": 4, "lines": None, "window": None}
        assert state["units"][C.ident] == {"hash": H, "mutants": None, "lines": None, "window": None}
        assert state["nights"] == old["nights"]
        written, night = sw.stitch(state, sw.state_digest(path), [_record(0, 1, {}, planned=0, digest=sw.state_digest(path))],
                                   jobs=1, head=HEAD, units=UNITS, today="2026-11-05")
        assert "converted_from" not in written and night["notes"] == [
            "the state was the sweep's that decided mutants by number: its nights carry over, and every "
            "function and the cycle start afresh with the sample drawn by line"]
        assert sw.load_state(sw.save_state(written, tmp_path / "out"), "x") == written
        bad = dict(old, units={A.ident: "not a record"})
        path.write_text(json.dumps(bad), encoding="utf-8")
        with pytest.raises(sw.StateError, match="not a schema 2 state"):
            sw.load_state(path, "2026-11-05")

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

    def test_a_window_goes_whole_into_one_job(self) -> None:
        """A unit's sampled window is decided whole: it goes into one job,
        the next one when it does not fit a job already holding work."""
        bins = _plan(_state(f=4, m=3, g=5), jobs=3, mutants=5)
        assert _bins(bins) == [[("x_f", (1, 2, 3, 4))], [(f"x{SEP}C{SEP}m", (1, 2, 3))], [("x_g", (1, 2, 3, 4, 5))]]

    def test_a_function_without_its_lines_stops_the_plan(self) -> None:
        """Every unit is counted before the plan, by mutmut's own visitor
        through the engine; one that is not cannot be sampled."""
        with pytest.raises(sw.StateError, match="has no mutants by line"):
            _plan(_state(f=4), jobs=2, mutants=6)  # m and g uncounted

    def test_a_jobs_first_piece_is_taken_whatever_it_costs(self) -> None:
        """A job with work open decides something, so a night cannot stall."""
        state = sw.reconcile(sw.empty_state("d"), [CORE_UNIT, C], "3.8.0")
        state["units"][CORE_UNIT.ident].update(mutants=3, lines=_lines(3))
        state["units"][C.ident].update(mutants=1, lines=_lines(1))
        bins = sw.plan(state, [CORE_UNIT, C], jobs=2, budget_s=1)
        assert _bins(bins) == [[("x_v", (1, 2, 3))], [("x_g", (1,))]]

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
        assert _bins(first) == _bins(second) == [[("x_f", (1, 2, 3, 4))], [(f"x{SEP}C{SEP}m", (1, 2, 3))],
                                                 [("x_g", (1, 2, 3, 4, 5))]]
        flat = [n for b in first for n in sw.engine_targets(b)]
        assert len(flat) == len(set(flat)) == 3

    def test_the_calibration_scales_a_jobs_share(self) -> None:
        state = _state(f=4, m=3, g=5)
        state["calibration"] = 2.0
        assert _bins(_plan(state, mutants=8)) == [[("x_f", (1, 2, 3, 4))]]

    def test_the_targets_are_the_picked_units_globs_and_the_window_their_lines(self) -> None:
        picks = [sw.Pick(unit=A, lines=(2, 7), counts=(1, 2), before=(1, 4)),
                 sw.Pick(unit=B, lines=(5,), counts=(3,), before=(0,)),
                 sw.Pick(unit=C, lines=(1,), counts=(1,), before=(0,))]
        assert sw.engine_targets(picks) == ["vera.a.x_f__mutmut_*", f"vera.a.x{SEP}C{SEP}m__mutmut_*",
                                            "vera.b.x_g__mutmut_*"]
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
        assert pick == sw.Pick(unit=A, lines=(5, 9), counts=(2, 4), before=(3, 5))
        assert [pick.line_of(n) for n in range(1, 7)] == [5, 5, 9, 9, 9, 9]
        assert [pick.full_number(n) for n in range(1, 7)] == [4, 5, 6, 7, 8, 9]
        with pytest.raises(sw.StateError, match="mutant 7 is past its window of 6"):
            pick.full_number(7)


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
        assert state["units"][C.ident] == {"hash": H, "mutants": 3, "lines": {"1": 2, "9": 1}, "window": None}
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


class TestSliceResults:
    def test_a_window_is_decided_whole_and_its_survivors_sit_on_their_lines(self) -> None:
        out = sw.slice_results([PICK_A, PICK_C], {
            "vera.a.x_f__mutmut_1": "killed", "vera.a.x_f__mutmut_2": "survived", "vera.a.x_f__mutmut_3": "timeout",
            "vera.b.x_g__mutmut_1": "no tests"}, GENERATED, cut_short=False, finished=True)
        assert out == {
            A.ident: {"hash": H, "window": 3, "lines": [3, 7], "survivors": ["4@7:survived", "5@7:timeout"],
                      "statuses": {"killed": 1, "survived": 1, "timeout": 1, "no_tests": 0, "other": 0}},
            C.ident: {"hash": H, "window": 1, "lines": [5], "survivors": [],
                      "statuses": {"killed": 0, "survived": 0, "timeout": 0, "no_tests": 1, "other": 0}}}

    def test_an_undecided_mutant_leaves_its_window_to_another_night(self) -> None:
        listing = {"vera.a.x_f__mutmut_1": "killed", "vera.a.x_f__mutmut_2": "not checked",
                   "vera.a.x_f__mutmut_3": "check was interrupted by user", "vera.b.x_g__mutmut_1": "killed"}
        out = sw.slice_results([PICK_A, PICK_C], listing, GENERATED, cut_short=True, finished=False)
        assert set(out) == {C.ident}

    def test_a_status_a_budget_stop_can_leave_waits_for_a_run_it_did_not_stop(self) -> None:
        listing = {"vera.a.x_f__mutmut_1": "segfault", "vera.a.x_f__mutmut_2": "suspicious",
                   "vera.a.x_f__mutmut_3": "timeout"}
        assert sw.slice_results([PICK_A], listing, GENERATED, cut_short=True, finished=False) == {}
        decided = sw.slice_results([PICK_A], listing, GENERATED, cut_short=False, finished=True)[A.ident]
        assert decided["statuses"] == {"killed": 0, "survived": 0, "timeout": 1, "no_tests": 0, "other": 2}
        assert decided["survivors"] == ["5@7:timeout"]  # the window's mutant 3, the fifth of the unit

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
        assert night["problems"] == [] and night["moved"] == 6  # the decided windows' mutants
        assert state["units"][A.ident] == {
            "hash": H, "mutants": 4, "lines": _lines(4),
            "window": _window(killed=2, survived=2, survivors=("3@3:survived", "4@4:survived"))}
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

    def test_a_night_that_decides_nothing_stops_short_and_survivors_never_do(self) -> None:
        state = _state(f=4)
        _, night = _stitch([_record(0, 1, {})], state, jobs=1)
        assert night["problems"] == ["the night decided no mutant"]
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

    def test_a_budget_stop_before_the_first_mutant_stops_the_night_short(self) -> None:
        """The four checker slices of 3 November 2026 spent their budget in
        five stats passes each and decided nothing, and the night would have
        been green but for a lost runner (#1827)."""
        good = _record(0, 2, {A.ident: _res(A, killed=4)})
        _, night = _stitch([good, _record(1, 2, {}, stopped="budget")])
        assert night["problems"] == ["slice 1: its budget ran out before its first mutant"]
        one = _record(1, 2, {C.ident: _res(C, killed=2)}, stopped="budget")
        _, night = _stitch([good, one])
        assert night["problems"] == []
        _, night = _stitch([good, _record(1, 2, {}, stopped="budget", planned=0)])
        assert night["problems"] == []  # nothing planned, nothing owed

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
        assert kept["units"][A.ident] == {"hash": H, "mutants": 4, "lines": _lines(4), "window": _window(killed=4)}

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

    def test_a_slices_exit_is_two_only_when_it_failed_or_decided_nothing_it_held(self) -> None:
        decided = {A.ident: _res(A, survived=1, survivors=("1@1:survived",))}
        assert sw.slice_exit(_record(0, 1, decided)) == 0
        assert sw.slice_exit(_record(0, 1, decided, stopped="budget")) == 0
        assert sw.slice_exit(_record(0, 1, {}, planned=0)) == 0
        assert sw.slice_exit(_record(0, 1, {})) == 2
        assert sw.slice_exit(_record(0, 1, {}, stopped="budget")) == 2  # the budget ran out before the first mutant
        assert sw.slice_exit(_record(0, 1, decided, stopped="engine")) == 2

    def test_the_calibration_follows_what_the_mutants_cost(self) -> None:
        """Ten mutants estimated at 2.5 s each took 100 s past the fixed passes:
        the factor moves halfway from 1 to 4."""
        record = _record(0, 1, {A.ident: _res(A, killed=10)})
        record["engine_s"] = sw.FIXED_S + 100.0
        state, _ = _stitch([record], jobs=1)
        assert state["calibration"] == 2.5


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
            "vera/a.py": {"killed": 6, "survived": 1, "timeout": 0, "no_tests": 0, "other": 0, "mutants": 7},
            "vera/b.py": {"killed": 3, "survived": 1, "timeout": 0, "no_tests": 1, "other": 0, "mutants": 5}}
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
                                                "no_tests": 0, "other": 0, "mutants": 80}
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
        _decide(state, B, killed=2, other=1)  # a segfault, which has no outcome to score
        sw.close_cycle(state, UNITS, head="h", today="e")
        score = sw.write_summary(state, tmp_path)
        rows = (tmp_path / "mutation-summary.csv").read_text(encoding="utf-8").splitlines()
        assert rows == ["module,total,killed,survived,timeout,caught_pct,mutants,ci95_low,ci95_high",
                        "vera/b.py,5,3,1,1,80.0,5,37.6,96.4", "vera/a.py,5,5,0,0,100.0,7,56.6,100.0",
                        "TOTAL (vera),10,8,1,1,90.0,12,59.6,98.2"]
        assert score == 90.0
        badge = json.loads((tmp_path / "mutation.json").read_text(encoding="utf-8"))
        assert badge == {"schemaVersion": 1, "label": "mutation", "message": "90.0% ±19.3",
                         "color": "brightgreen"}
        assert (tmp_path / "mutation-survivors.csv").read_text(encoding="utf-8").splitlines() == [
            "module,mutant,status", "vera.b,x_g__mutmut_4@L4,survived", "vera.b,x_g__mutmut_5@L5,timeout"]

    def test_no_summary_is_written_before_a_cycle_has_closed(self, tmp_path: Path) -> None:
        with pytest.raises(sw.StateError):
            sw.write_summary(sw.empty_state("d"), tmp_path)

    def test_the_stitch_closes_a_complete_cycle_and_not_a_night_that_stopped_short(self) -> None:
        state = _state()
        _complete(state, {A: 4, B: 3})
        state["units"][C.ident].update(mutants=1, lines=_lines(1))
        done = {C.ident: _res(C, killed=1)}
        closed, night = _stitch([_record(0, 1, done)], json.loads(json.dumps(state)), jobs=1)
        assert night["closed"] and closed["cycle"] == 2
        kept, night = _stitch([_record(0, 2, done), _record(1, 2, {}, stopped="engine")],
                              json.loads(json.dumps(state)))
        assert not night["closed"] and kept["cycle"] == 1
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
        (step,) = [s for s in job["steps"] if "scripts/mutate_sweep.py night" in s.get("run", "")]
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
        (record,) = [s for s in self._steps("sweep") if str(s.get("uses", "")).startswith("actions/upload-artifact@")]
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


# ---------------------------------------------------------------------------
# The heartbeat
# ---------------------------------------------------------------------------


MEMINFO = ("MemTotal:       16368832 kB\nMemFree:         1000000 kB\nMemAvailable:   11503616 kB\n"
           "SwapTotal:       4194300 kB\nSwapFree:        3145724 kB\n")
LOADAVG = "3.91 3.80 3.40 5/1234 99999\n"


class TestHeartbeat:
    """A lost runner uploads no record, so what the slice printed is all that
    survives of it (#1751): a line every few minutes with the time, the
    runner's memory and load, and the engine's last status."""

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
    time.sleep(float(os.environ.get("FAKE_RUN_SLEEP", "0")))
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
    sys.stdout.write((state / "results.txt").read_text(encoding="utf-8"))
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
        assert run["args"][-2:] == ["vera.m.x_f__mutmut_*", "vera.m.x_g__mutmut_*"]
        window = json.loads((tmp_path / "work1" / "window.json").read_text(encoding="utf-8"))
        assert window["exact"] is True and window["lines"] == {"vera/m.py": [1, 2, 5, 6]}  # f at 1, g at 5
        code, state = _stitch_cli(repo, tmp_path, 1, None)
        assert code == 0 and state["cycle"] == 1
        assert state["units"]["vera/m.py::x_g"] == {"hash": state["units"]["vera/m.py::x_g"]["hash"],
                                                    "mutants": 2, "lines": lines, "window": None}
        assert state["units"]["vera/m.py::x_f"]["window"] == {"killed": 1, "survived": 1, "timeout": 0, "no_tests": 0,
                                                              "other": 0, "mutants": 2, "survivors": ["2@2:survived"]}

        code, record, calls = _night(repo, tmp_path, 2, (
            "    vera.m.x_g__mutmut_1: killed\n    vera.m.x_g__mutmut_2: killed\n"),
            state=tmp_path / "state1")
        assert code == 0 and record["state_in"] == sw.state_digest(tmp_path / "state1" / sw.STATE_FILE)
        assert record["counts"] == {}  # the state carried the counts
        (run,) = [c for c in calls if c["args"][0] == "run"]
        assert run["args"][-1:] == ["vera.m.x_g__mutmut_*"]
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

    def test_a_budget_stop_before_the_first_mutant_is_a_stop_of_its_own(
        self, repo: Path, tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        """A run the budget stopped before any mutant was decided lists at
        most what mutmut generated and decides nothing: the slice's exit and
        the night's problems say so (the four checker slices of 3 November
        2026, #1827)."""
        monkeypatch.setenv("FAKE_RUN_SLEEP", "30")
        monkeypatch.setenv("FAKE_COUNT", "1")
        monkeypatch.setattr(sw.md, "run_engine", lambda *a, **k: _quick_stop(*a, **k))
        monkeypatch.setattr(sw, "FIXED_S", 0)
        monkeypatch.setattr(sw, "OTHER_RATE_S", 0.01)  # both functions fit the two-second budget
        code, record, _ = _night(repo, tmp_path, 1, "    vera.m.x_f__mutmut_1: not checked\n", budget=2)
        assert [p["unit"] for p in record["planned"]] == ["vera/m.py::x_f", "vera/m.py::x_g"]
        assert record["stopped"] == "budget" and code == 2
        assert record["results"] == {}  # x_f's window undecided, x_g's not listed: both wait
        code, state = _stitch_cli(repo, tmp_path, 1, None)
        assert code == 2
        assert state["nights"][-1]["problems"] == ["slice 0: its budget ran out before its first mutant"]

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
        assert record["results"] == {}  # x_f's window waits: its segfault is the stop's, not a verdict

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

    def test_mutmut_itself_decides_a_night(self, repo: Path, tmp_path: Path) -> None:
        """Against the engine, under the fork server: its ``count`` is what
        mutmut generates for each function, mutmut runs the planned mutants
        by name in the narrowed tree, and the stitch closes the cycle."""
        pytest.importorskip("mutmut")
        code, record, _ = _night(repo, tmp_path, 1, "", real=True)
        assert code == 0 and record["stopped"] is None, record
        results = record["results"]
        assert set(results) == {"vera/m.py::x_f", "vera/m.py::x_g"}
        for ident, r in results.items():
            counted = record["counts"][ident]
            assert r["window"] == counted["mutants"] == sum(counted["lines"].values()) >= 1
            assert r["lines"] == sorted(int(line) for line in counted["lines"])  # every line sampled
            assert r["statuses"]["killed"] == r["window"] and r["survivors"] == []
        code, state = _stitch_cli(repo, tmp_path, 1, None)
        assert code == 0 and state["cycle"] == 2 and state["last_complete"]["modules"]["vera/m.py"]["survived"] == 0
        assert state["last_complete"]["sampled"] == state["last_complete"]["population"] == sum(
            c["mutants"] for c in record["counts"].values())
