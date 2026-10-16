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
SEP = "ǁ"


def _load() -> Any:
    path = ROOT / "scripts" / "mutate_sweep.py"
    spec = importlib.util.spec_from_file_location("mutate_sweep", path)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    sys.modules["mutate_sweep"] = module
    spec.loader.exec_module(module)
    return module


sw = _load()


def _u(path: str, key: str, start: int = 1, code: str = "h", estimate: int = 4) -> Any:
    return sw.SweepUnit(path=path, key=key, start=start, hash=code, estimate=estimate)


A = _u("vera/a.py", "x_f", 1)
B = _u("vera/a.py", f"x{SEP}C{SEP}m", 20)
C = _u("vera/b.py", "x_g", 1)
UNITS = [A, B, C]  # the tree's order
CORE_UNIT = _u("vera/verifier.py", "x_v", 1)


def _state(**counts: int | None) -> dict[str, Any]:
    """A reconciled state, each unit's count given by its key (None: unknown)."""
    state = sw.reconcile(sw.empty_state("2026-10-16"), UNITS, "3.8.0")
    for unit in UNITS:
        state["units"][unit.ident]["mutants"] = counts.get(unit.key.split(SEP)[-1].removeprefix("x_"))
    return state


def _decide(state: dict[str, Any], unit: Any, numbers: range | list[int], status: str = "killed") -> None:
    for n in numbers:
        state["units"][unit.ident]["statuses"][str(n)] = status


def _bins(picks: list[list[Any]]) -> list[list[tuple[str, Any]]]:
    return [[(p.unit.key, p.numbers) for p in b] for b in picks]


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
        assert units[1].estimate > units[0].estimate >= 1

    def test_a_units_identity_is_its_code_not_its_docstring_or_layout(self) -> None:
        (plain,) = [u for u in sw.units_of(SOURCE, "m.py") if u.key == "x_plain"]
        restyled = SOURCE.replace('    """A docstring."""\n', "").replace("x + 1", "x+1  # one more")
        (same,) = [u for u in sw.units_of(restyled, "m.py") if u.key == "x_plain"]
        changed = SOURCE.replace("x + 1", "x + 2")
        (other,) = [u for u in sw.units_of(changed, "m.py") if u.key == "x_plain"]
        assert same.hash == plain.hash != other.hash

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
        _decide(state, A, [1, 2])
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
        _decide(state, A, [1])
        _decide(state, B, [1])
        state = sw.reconcile(state, [_u("vera/a.py", "x_f", 1, code="other"), B, C], "3.8.0")
        assert state["units"][A.ident] == {"hash": "other", "mutants": None, "statuses": {}}
        assert state["units"][B.ident]["statuses"] == {"1": "killed"}

    def test_a_new_engine_starts_every_function_afresh(self) -> None:
        """mutmut numbers a function's mutants by its own rules, so a decided
        number means nothing under another version."""
        state = _state(f=4)
        _decide(state, A, [1])
        state = sw.reconcile(state, UNITS, "3.9.0")
        assert state["engine"] == "3.9.0"
        assert all(r == {"hash": "h", "mutants": None, "statuses": {}} for r in state["units"].values())

    def test_a_function_gone_from_the_tree_is_dropped(self) -> None:
        state = sw.reconcile(_state(), [A, B], "3.8.0")
        assert C.ident not in state["units"]


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
        quarter of the budget is left to mutants whatever they cost."""
        monkeypatch.setattr(sw, "FIXED_S", 30)
        assert _bins(sw.plan(_state(f=4, m=3, g=5), UNITS, jobs=1, budget_s=40)) == [[("x_f", (1, 2, 3, 4))]]
        assert _bins(sw.plan(_state(f=4, m=3, g=5), UNITS, jobs=1, budget_s=20)) == [[("x_f", (1, 2))]]

    def test_the_plan_takes_the_tree_in_order_up_to_a_jobs_capacity(self) -> None:
        bins = _plan(_state(f=4, m=3, g=5), mutants=7)
        assert _bins(bins) == [[("x_f", (1, 2, 3, 4)), (f"x{SEP}C{SEP}m", (1, 2, 3))]]

    def test_a_function_whose_count_is_known_splits_across_the_jobs(self) -> None:
        bins = _plan(_state(f=4, m=3, g=5), jobs=3, mutants=5)
        assert _bins(bins) == [[("x_f", (1, 2, 3, 4)), (f"x{SEP}C{SEP}m", (1,))],
                               [(f"x{SEP}C{SEP}m", (2, 3)), ("x_g", (1, 2, 3))],
                               [("x_g", (4, 5))]]

    def test_a_function_whose_count_is_unknown_goes_whole(self) -> None:
        """Its mutants have no names until mutmut generates them: it goes
        into one job, the next one when it does not fit a job already holding
        work."""
        state = _state(f=4)  # m and g unknown, estimated at 4 each
        bins = _plan(state, jobs=2, mutants=6)
        assert _bins(bins) == [[("x_f", (1, 2, 3, 4))], [(f"x{SEP}C{SEP}m", None)]]

    def test_a_jobs_first_piece_is_taken_whatever_it_costs(self) -> None:
        """A job with work open decides something, so a night cannot stall."""
        state = sw.reconcile(sw.empty_state("d"), [CORE_UNIT, C], "3.8.0")
        state["units"][CORE_UNIT.ident]["mutants"] = 3
        bins = sw.plan(state, [CORE_UNIT, C], jobs=2, budget_s=1)
        assert _bins(bins) == [[("x_v", (1,))], [("x_v", (2,))]]

    def test_decided_mutants_are_not_planned_again(self) -> None:
        state = _state(f=4, m=3, g=5)
        _decide(state, A, [1, 2, 3, 4])
        _decide(state, B, [2], "survived")
        bins = _plan(state, mutants=4)
        assert _bins(bins) == [[(f"x{SEP}C{SEP}m", (1, 3)), ("x_g", (1, 2))]]

    def test_every_job_of_the_night_computes_the_same_disjoint_bins(self) -> None:
        state = _state(f=4, m=3, g=5)
        first, second = _plan(state, jobs=3, mutants=4), _plan(json.loads(json.dumps(state)), jobs=3, mutants=4)
        assert _bins(first) == _bins(second)
        names = [sw.engine_targets(b) for b in first]
        flat = [n for b in names for n in b]
        assert len(flat) == len(set(flat)) == 12

    def test_the_calibration_scales_a_jobs_share(self) -> None:
        state = _state(f=4, m=3, g=5)
        state["calibration"] = 2.0
        assert _bins(_plan(state, mutants=8)) == [[("x_f", (1, 2, 3, 4))]]

    def test_a_whole_function_is_a_glob_and_a_part_is_its_names(self) -> None:
        picks = [sw.Pick(unit=A, numbers=(2, 3)), sw.Pick(unit=B, numbers=None)]
        assert sw.engine_targets(picks) == ["vera.a.x_f__mutmut_2", "vera.a.x_f__mutmut_3",
                                            f"vera.a.x{SEP}C{SEP}m__mutmut_*"]


# ---------------------------------------------------------------------------
# A slice's results, and the stitch
# ---------------------------------------------------------------------------


class TestSliceResults:
    def test_a_functions_count_is_mutmuts_listing_and_only_decided_mutants_count(self) -> None:
        picks = [sw.Pick(unit=A, numbers=None), sw.Pick(unit=C, numbers=(2,))]
        out = sw.slice_results(picks, {
            "vera.a.x_f__mutmut_1": "killed", "vera.a.x_f__mutmut_2": "not checked",
            "vera.a.x_f__mutmut_3": "check was interrupted by user",
            "vera.b.x_g__mutmut_1": "not checked", "vera.b.x_g__mutmut_2": "no tests"},
            cut_short=False)
        assert out == {A.ident: {"hash": "h", "mutants": 3, "statuses": {"1": "killed"}},
                       C.ident: {"hash": "h", "mutants": 2, "statuses": {"2": "no tests"}}}

    def test_a_status_a_budget_stop_can_leave_waits_for_a_run_it_did_not_stop(self) -> None:
        picks = [sw.Pick(unit=A, numbers=None)]
        results = {"vera.a.x_f__mutmut_1": "segfault", "vera.a.x_f__mutmut_2": "suspicious",
                   "vera.a.x_f__mutmut_3": "timeout"}
        assert sw.slice_results(picks, results, cut_short=True)[A.ident]["statuses"] == {"3": "timeout"}
        assert sw.slice_results(picks, results, cut_short=False)[A.ident]["statuses"] == {
            "1": "segfault", "2": "suspicious", "3": "timeout"}

    def test_a_result_for_a_function_the_night_did_not_plan_is_refused(self) -> None:
        with pytest.raises(sw.StateError):
            sw.slice_results([sw.Pick(unit=A, numbers=None)], {"vera.b.x_g__mutmut_1": "killed"},
                             cut_short=False)

    def test_a_listing_with_a_gap_in_its_numbers_is_refused(self) -> None:
        with pytest.raises(sw.StateError):
            sw.slice_results([sw.Pick(unit=A, numbers=None)],
                             {"vera.a.x_f__mutmut_1": "killed", "vera.a.x_f__mutmut_3": "killed"},
                             cut_short=False)


def _record(slice_: int, of: int, results: dict[str, Any], *, head: str = "h" * 40,
            digest: str = "none", stopped: str | None = None, planned: int = 1) -> dict[str, Any]:
    return {"schema": sw.SCHEMA, "slice": slice_, "of": of, "head": head, "state_in": digest,
            "engine": "3.8.0", "budget_s": 100.0, "planned": [{"unit": "u"}] * planned,
            "results": results, "stopped": stopped, "engine_s": sw.FIXED_S + 10.0,
            "dropped_tests": [], "subprocess_tests": []}


def _stitch(records: list[dict[str, Any]], state: dict[str, Any] | None = None, *, jobs: int = 2,
            ) -> tuple[dict[str, Any], dict[str, Any]]:
    return sw.stitch(state or sw.empty_state("d"), "none", records, jobs=jobs, head="h" * 40,
                     units=UNITS, today="2026-10-17")


class TestStitch:
    def test_the_nights_slices_fold_into_the_state(self) -> None:
        state, night = _stitch([
            _record(0, 2, {A.ident: {"hash": "h", "mutants": 4, "statuses": {"1": "killed", "2": "survived"}}}),
            _record(1, 2, {A.ident: {"hash": "h", "mutants": 4, "statuses": {"3": "timeout"}},
                           C.ident: {"hash": "h", "mutants": 2, "statuses": {}}}),
        ])
        assert night["problems"] == [] and night["moved"] == 5  # 3 decided, A and C counted
        assert state["units"][A.ident] == {"hash": "h", "mutants": 4,
                                           "statuses": {"1": "killed", "2": "survived", "3": "timeout"}}
        assert state["units"][C.ident]["mutants"] == 2 and state["units"][B.ident]["mutants"] is None
        assert state["nights"][-1] is night

    def test_a_slice_of_another_head_or_another_state_stops_the_night_short(self) -> None:
        good = _record(0, 2, {A.ident: {"hash": "h", "mutants": 4, "statuses": {"1": "killed"}}})
        _, night = _stitch([good, _record(1, 2, {}, head="e" * 40)])
        assert any("ran eeee" in p for p in night["problems"])
        _, night = _stitch([good, _record(1, 2, {}, digest="other")])
        assert any("another state" in p for p in night["problems"])

    def test_a_missing_slice_stops_the_night_short(self) -> None:
        _, night = _stitch([_record(0, 2, {A.ident: {"hash": "h", "mutants": 4, "statuses": {"1": "killed"}}})])
        assert night["problems"] == ["no record from slice(s) 1"]

    def test_a_slice_its_engine_stopped_stops_the_night_short_and_its_results_still_count(self) -> None:
        state, night = _stitch([
            _record(0, 2, {A.ident: {"hash": "h", "mutants": 4, "statuses": {"1": "killed"}}}),
            _record(1, 2, {}, stopped="engine")])
        assert night["problems"] == ["slice 1: stopped by the engine"]
        assert state["units"][A.ident]["statuses"] == {"1": "killed"}

    def test_a_night_that_decides_nothing_stops_short_and_survivors_never_do(self) -> None:
        state = _state(f=4)
        _, night = _stitch([_record(0, 1, {A.ident: {"hash": "h", "mutants": 4, "statuses": {}}})],
                           state, jobs=1)
        assert night["problems"] == ["the night decided no mutant and counted no function"]
        _, night = _stitch([_record(0, 1, {B.ident: {"hash": "h", "mutants": 0, "statuses": {}}})],
                           _state(f=4), jobs=1)
        assert night["problems"] == []  # counting a function with no mutant decides it
        _, night = _stitch([_record(0, 1, {A.ident: {"hash": "h", "mutants": 4,
                                                     "statuses": {"1": "survived"}}})], jobs=1)
        assert night["problems"] == []

    def test_a_slices_exit_is_two_only_when_it_failed_or_decided_nothing_it_held(self) -> None:
        decided = {A.ident: {"hash": "h", "mutants": 1, "statuses": {"1": "survived"}}}
        assert sw.slice_exit(_record(0, 1, decided)) == 0
        assert sw.slice_exit(_record(0, 1, decided, stopped="budget")) == 0
        assert sw.slice_exit(_record(0, 1, {}, planned=0)) == 0
        assert sw.slice_exit(_record(0, 1, {})) == 2
        whole = _record(0, 1, {B.ident: {"hash": "h", "mutants": 0, "statuses": {}}})
        whole["planned"] = [{"unit": B.ident, "hash": "h", "numbers": None}]
        assert sw.slice_exit(whole) == 0
        assert sw.slice_exit(_record(0, 1, decided, stopped="engine")) == 2

    def test_the_calibration_follows_what_the_mutants_cost(self) -> None:
        """Ten mutants estimated at 2.5 s each took 100 s past the fixed passes:
        the factor moves halfway from 1 to 4."""
        record = _record(0, 1, {A.ident: {"hash": "h", "mutants": 10,
                                          "statuses": {str(n): "killed" for n in range(1, 11)}}})
        record["engine_s"] = sw.FIXED_S + 100.0
        state, _ = _stitch([record], jobs=1)
        assert state["calibration"] == 2.5


# ---------------------------------------------------------------------------
# Closing a cycle, and the committed summary
# ---------------------------------------------------------------------------


def _complete(state: dict[str, Any], counts: dict[Any, int], status: str = "killed") -> None:
    for unit, n in counts.items():
        state["units"][unit.ident]["mutants"] = n
        _decide(state, unit, range(1, n + 1), status)


class TestCycle:
    def test_an_incomplete_cycle_stays_open(self) -> None:
        state = _state(f=4, m=3, g=5)
        _decide(state, A, [1, 2, 3, 4])
        assert sw.close_cycle(state, UNITS, head="h", today="e") is False
        assert state["cycle"] == 1 and state["last_complete"] is None

    def test_a_complete_cycle_closes_with_its_totals_and_opens_the_next(self) -> None:
        state = _state()
        _complete(state, {A: 4, B: 3, C: 5})
        _decide(state, C, [4], "survived")
        _decide(state, C, [5], "no tests")
        assert sw.close_cycle(state, UNITS, head="c" * 40, today="2026-11-30") is True
        assert state["cycle"] == 2 and state["cycle_started"] == "2026-11-30"
        assert all(r["statuses"] == {} and r["mutants"] for r in state["units"].values())
        last = state["last_complete"]
        assert last["cycle"] == 1 and last["finished"] == "2026-11-30" and last["head"] == "c" * 40
        assert last["modules"] == {
            "vera/a.py": {"killed": 7, "survived": 0, "timeout": 0, "no_tests": 0, "other": 0},
            "vera/b.py": {"killed": 3, "survived": 1, "timeout": 0, "no_tests": 1, "other": 0}}
        assert last["survivors"] == ["vera.b.x_g__mutmut_4:survived"]

    def test_the_summary_is_the_committed_csv_badge_and_inventory(self, tmp_path: Path) -> None:
        """mutation_report.py's format: a module's total is its mutants an
        in-process test reaches with a known outcome, so `no tests` and the
        cut-short statuses stay out of the score."""
        state = _state()
        _complete(state, {A: 4, B: 3, C: 5})
        _decide(state, C, [4], "survived")
        _decide(state, C, [5], "timeout")
        _decide(state, A, [4], "no tests")
        _decide(state, B, [3], "segfault")
        sw.close_cycle(state, UNITS, head="h", today="e")
        score = sw.write_summary(state, tmp_path)
        rows = (tmp_path / "mutation-summary.csv").read_text(encoding="utf-8").splitlines()
        assert rows == ["module,total,killed,survived,timeout,caught_pct",
                        "vera/b.py,5,3,1,1,80.0", "vera/a.py,5,5,0,0,100.0",
                        "TOTAL (vera),10,8,1,1,90.0"]
        assert score == 90.0
        badge = json.loads((tmp_path / "mutation.json").read_text(encoding="utf-8"))
        assert badge == {"schemaVersion": 1, "label": "mutation", "message": "90.0%", "color": "brightgreen"}
        assert (tmp_path / "mutation-survivors.csv").read_text(encoding="utf-8").splitlines() == [
            "module,mutant,status", "vera.b,x_g__mutmut_4,survived", "vera.b,x_g__mutmut_5,timeout"]

    def test_no_summary_is_written_before_a_cycle_has_closed(self, tmp_path: Path) -> None:
        with pytest.raises(sw.StateError):
            sw.write_summary(sw.empty_state("d"), tmp_path)

    def test_the_stitch_closes_a_complete_cycle_and_not_a_night_that_stopped_short(self) -> None:
        state = _state()
        _complete(state, {A: 4, B: 3})
        state["units"][C.ident]["mutants"] = 1
        done = {C.ident: {"hash": "h", "mutants": 1, "statuses": {"1": "killed"}}}
        closed, night = _stitch([_record(0, 1, done)], json.loads(json.dumps(state)), jobs=1)
        assert night["closed"] and closed["cycle"] == 2
        kept, night = _stitch([_record(0, 2, done)], json.loads(json.dumps(state)))
        assert not night["closed"] and kept["cycle"] == 1


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

    def test_the_jobs_are_the_setups_matrix_and_one_failing_slice_stops_no_other(self) -> None:
        sweep = self._wf()["jobs"]["sweep"]
        assert sweep["strategy"] == {"fail-fast": False,
                                     "matrix": {"slice": "${{ fromJSON(needs.setup.outputs.slices) }}"}}
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

    def test_the_tracking_issue_is_filed_only_for_a_scheduled_night_that_stopped_short(self) -> None:
        issue = self._wf()["jobs"]["issue"]
        assert issue["needs"] == ["setup", "sweep", "stitch"]
        assert issue["if"] == "failure() && github.event_name == 'schedule'"
        (step,) = issue["steps"]
        assert 'const LABEL = "mutation-sweep";' in step["with"]["script"]


# ---------------------------------------------------------------------------
# A night end to end
# ---------------------------------------------------------------------------


FAKE_ENGINE = '''
import json, os, sys
from pathlib import Path
state = Path(os.environ["FAKE_STATE"])
args = sys.argv[1:]
with (state / "calls.jsonl").open("a", encoding="utf-8") as fh:
    fh.write(json.dumps({"cwd": os.getcwd(), "args": args}) + "\\n")
if args[0] == "--version":
    print("mutmut, version 3.8.0")
    sys.exit(0)
if args[0] == "run":
    failing = os.environ.get("FAKE_COPY_FAILURE", "")
    config = Path("pyproject.toml").read_text(encoding="utf-8")
    if failing and f"--deselect={failing}" not in config:
        print("Running stats")
        print(f"FAILED {failing} - FileNotFoundError: x")
        print("failed to collect stats. runner returned 1")
        sys.exit(1)
    sys.exit(0)
if args[0] == "results":
    sys.stdout.write((state / "results.txt").read_text(encoding="utf-8"))
    sys.exit(0)
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
           engine: list[str] | None = None) -> tuple[int, dict[str, Any], list[dict[str, Any]]]:
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
                        "--engine", *(engine or [sys.executable, str(tmp_path / "fake_mutmut.py")])])
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


@pytest.mark.usefixtures("no_git_locators")
class TestEndToEnd:
    def test_two_nights_carry_the_state_and_close_the_cycle(self, repo: Path, tmp_path: Path) -> None:
        code, record, calls = _night(repo, tmp_path, 1, (
            "    vera.m.x_f__mutmut_1: killed\n    vera.m.x_f__mutmut_2: survived\n"
            "    vera.m.x_g__mutmut_1: killed\n    vera.m.x_g__mutmut_2: not checked\n"))
        assert code == 0 and record["stopped"] is None
        assert [p["numbers"] for p in record["planned"]] == [None, None]
        (run,) = [c for c in calls if c["args"][0] == "run"]
        assert run["args"][-2:] == ["vera.m.x_f__mutmut_*", "vera.m.x_g__mutmut_*"]
        code, state = _stitch_cli(repo, tmp_path, 1, None)
        assert code == 0 and state["cycle"] == 1
        assert state["units"]["vera/m.py::x_g"] == {"hash": state["units"]["vera/m.py::x_g"]["hash"],
                                                    "mutants": 2, "statuses": {"1": "killed"}}

        code, record, calls = _night(repo, tmp_path, 2, (
            "    vera.m.x_g__mutmut_1: not checked\n    vera.m.x_g__mutmut_2: killed\n"),
            state=tmp_path / "state1")
        assert code == 0 and record["state_in"] == sw.state_digest(tmp_path / "state1" / sw.STATE_FILE)
        (run,) = [c for c in calls if c["args"][0] == "run"]
        assert run["args"][-1:] == ["vera.m.x_g__mutmut_2"]
        code, state = _stitch_cli(repo, tmp_path, 2, tmp_path / "state1")
        assert code == 0 and state["cycle"] == 2
        assert state["last_complete"]["modules"]["vera/m.py"]["survived"] == 1
        assert (tmp_path / "state2" / "mutation-summary.csv").read_text(encoding="utf-8").splitlines()[-1] == (
            "TOTAL (vera),4,3,1,0,75.0")

    def test_the_copy_holds_the_whole_tree_and_the_oracle_every_admitted_test(
        self, repo: Path, tmp_path: Path,
    ) -> None:
        (repo / "README.md").write_text("read by a test\n", encoding="utf-8")
        _git(repo, "add", "-A")
        _git(repo, "commit", "-q", "-m", "readme")
        _night(repo, tmp_path, 1, "    vera.m.x_f__mutmut_1: killed\n    vera.m.x_g__mutmut_1: killed\n")
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
            "    vera.m.x_f__mutmut_1: killed\n    vera.m.x_g__mutmut_1: killed\n"))
        assert code == 0 and record["dropped_tests"] == ["tests/test_m.py::test_f"]
        assert len([c for c in calls if c["args"][0] == "run"]) == 2

    def test_a_failure_of_the_lane_is_a_record_with_exit_two(self, repo: Path, tmp_path: Path) -> None:
        broken = tmp_path / "broken_engine.py"
        broken.write_text("raise SystemExit(3)\n", encoding="utf-8")
        code, record, _ = _night(repo, tmp_path, 1, "", engine=[sys.executable, str(broken)])
        assert code == 2 and record["stopped"] == "lane"
        assert "version" in record["engine_tail"][0]

    def test_mutmut_itself_decides_a_night(self, repo: Path, tmp_path: Path) -> None:
        """Against the engine: mutmut generates and runs the planned
        functions' mutants in the narrowed tree, and the stitch counts them."""
        pytest.importorskip("mutmut")
        engine = [str(Path(sys.executable).with_name("mutmut"))]
        code, record, _ = _night(repo, tmp_path, 1, "", engine=engine)
        assert code == 0 and record["stopped"] is None, record
        statuses = {ident: r["statuses"] for ident, r in record["results"].items()}
        assert set(statuses) == {"vera/m.py::x_f", "vera/m.py::x_g"}
        assert all(r["mutants"] >= 1 and len(r["statuses"]) == r["mutants"] for r in record["results"].values())
        assert {s for st in statuses.values() for s in st.values()} == {"killed"}
        code, state = _stitch_cli(repo, tmp_path, 1, None)
        assert code == 0 and state["cycle"] == 2 and state["last_complete"]["modules"]["vera/m.py"]["survived"] == 0
