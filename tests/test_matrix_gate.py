"""The matrix gate (scripts/matrix_gate.py): the required check that holds a
pull request to the full test matrix exactly when it raises
`[project].version`.

The CI `matrix-gate` job runs on every run, after the `plan` job and the
`test` matrix whatever their outcome, and hands the script three results:
the plan job's, its answer to "does this change raise the version?", and the
matrix's.  The gate passes when the plan succeeded and either every cell of
the matrix passed or the version stays and the matrix was skipped; anything
else fails, so a plan that failed, a matrix skipped on a version-raising
pull request, or an answer it cannot read fails the check rather than
passing it.  The verdicts are pinned over every combination of the three.

Where the matrix ran, the gate also reads the run's job listing (#1659): the
matrix's result is the aggregate of the cells that ran in the current
attempt, which a cell re-run on its own and passing turns to `success` while
another cell is still failed.  The listing's cases run on listings recorded
from real runs (`tests/fixtures/matrix_gate/listings.json`): a nightly run
with every cell green, a run whose second attempt re-ran its one failed cell,
and a pull request's run with the shards and the matrix skipped.  The command
line reads the three results from its environment and lists the jobs through
`gh`, here a stand-in that serves the recordings.  The nightly run is a
run of nightly-matrix.yml, which calls ci.yml, and a call's run lists each
job of ci.yml under the calling job's name (`CI / test (macos-15, 3.12)`):
the recordings under that name are read as the push run's are, and the
watched cells it also lists (`watch (ubuntu-latest, 3.12)`) are named
when they fail and decide nothing.  The pins at the end hold the gate's
reading of cell names and of the advisory cell to ci.yml's matrix, and
the job to what the script reads.
"""

from __future__ import annotations

import importlib.util
import itertools
import json
import subprocess
from collections.abc import Callable
from pathlib import Path
from typing import Any

import pytest
import yaml

from tests.test_gate_placement import _matrix_cells, evaluate, render

ROOT = Path(__file__).resolve().parent.parent
SCRIPT = ROOT / "scripts" / "matrix_gate.py"
CI = ROOT / ".github" / "workflows" / "ci.yml"
LISTINGS = ROOT / "tests" / "fixtures" / "matrix_gate" / "listings.json"


def _load() -> Any:
    spec = importlib.util.spec_from_file_location("matrix_gate", SCRIPT)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


mg = _load()

# What `needs.<job>.result` can be, and what the plan job's `release` output
# can be: `true` or `false` where its step ran, empty where it did not.
RESULTS = ("success", "failure", "cancelled", "skipped")
RELEASES = ("true", "false", "")

# The combinations that pass, written out rather than recomputed.
PASSING = {
    ("success", "true", "success"),
    ("success", "false", "success"),
    ("success", "", "success"),
    ("success", "false", "skipped"),
}


@pytest.mark.parametrize(
    ("plan", "release", "matrix"), list(itertools.product(RESULTS, RELEASES, RESULTS)),
)
def test_every_combination(plan: str, release: str, matrix: str) -> None:
    passed, why = mg.decide(plan, release, matrix)
    assert passed is ((plan, release, matrix) in PASSING), why
    assert why.strip(), "every verdict carries its reason"


def test_a_pull_request_that_keeps_the_version_passes_with_the_matrix_skipped() -> None:
    passed, why = mg.decide("success", "false", "skipped")
    assert passed, why


def test_a_version_raising_pull_request_passes_when_every_cell_passed() -> None:
    passed, why = mg.decide("success", "true", "success")
    assert passed, why


def test_a_version_raising_pull_request_fails_when_a_cell_failed() -> None:
    passed, why = mg.decide("success", "true", "failure")
    assert not passed
    assert "failure" in why


def test_a_version_raising_pull_request_fails_when_the_matrix_was_skipped() -> None:
    """The matrix's own condition decides whether it runs; a skip on a
    change that raises the version is that condition gone wrong, and the
    gate does not read it as a pass."""
    passed, why = mg.decide("success", "true", "skipped")
    assert not passed
    assert "skipped" in why


def test_a_failed_plan_fails_even_after_it_wrote_its_answer() -> None:
    """The plan job writes `release` before it lists the changed files, so a
    plan that failed late can still hand over `false`; its matrix is skipped
    because the plan failed, not because the version stays."""
    passed, why = mg.decide("failure", "false", "skipped")
    assert not passed
    assert "plan" in why


def test_a_cancelled_matrix_fails() -> None:
    passed, _ = mg.decide("success", "true", "cancelled")
    assert not passed


@pytest.mark.parametrize(
    ("plan", "release", "matrix"),
    [
        ("success", "false", "neutral"),
        ("success", "false", ""),
        ("", "false", "skipped"),
        ("success", "yes", "skipped"),
        ("success", "False ", "skipped"),
    ],
)
def test_a_value_it_cannot_read_fails(plan: str, release: str, matrix: str) -> None:
    passed, why = mg.decide(plan, release, matrix)
    assert not passed, why


# ---------------------------------------------------------------------------
# The run's job listing
# ---------------------------------------------------------------------------

#: The recordings, each under the `gh` command that printed it.
NIGHTLY = "gh run view 38232649508 --json jobs"
FAILED_CELL = "gh run view 33709478610 --attempt 1 --json jobs"
RERUN = "gh run view 33709478610 --attempt 2 --json jobs"
PULL_REQUEST = "gh run view 38236511836 --json jobs"

#: Until #1656 the Linux 3.12 cell's name carried the suffix that made it a
#: required check of its own; the cell is named without it now.  This is the
#: one edit made to a recording before the gate reads it.
_RENAMED = {"test (ubuntu-latest, 3.12) + coverage": "test (ubuntu-latest, 3.12)"}

RERUN_CELL = "test (ubuntu-latest, 3.13)"
ADVISORY_CELL = "test (ubuntu-24.04-arm, 3.12)"

#: The cells each recorded run's matrix ran, its `strategy.job-total`, the
#: number the `test` job hands the gate as its `cells` output.
CELLS = "13"


def _raw(command: str) -> dict[str, Any]:
    """A recorded listing exactly as `gh` printed it."""
    listing: dict[str, Any] = json.loads(LISTINGS.read_text(encoding="utf-8"))[command]
    return listing


def _recorded(command: str) -> dict[str, Any]:
    """A recorded listing as `gh` printed it, its cells named as today."""
    return {"jobs": [{**job, "name": _RENAMED.get(job["name"], job["name"])} for job in _raw(command)["jobs"]]}


def _with(listing: dict[str, Any], conclusions: dict[str, str]) -> dict[str, Any]:
    """A listing with the named jobs' conclusions replaced; every name must
    be a job of the listing, so a misspelt one cannot leave it as it was."""
    names = {job["name"] for job in listing["jobs"]}
    assert set(conclusions) <= names, sorted(set(conclusions) - names)
    return {"jobs": [
        {**job, "conclusion": conclusions.get(job["name"], job["conclusion"])} for job in listing["jobs"]
    ]}


def _called(listing: dict[str, Any], caller: str = "CI") -> dict[str, Any]:
    """A listing as a call's run prints it: every job under the calling
    job's name, `<caller> / <name>`, the form python/cpython's runs of
    the workflow that calls its reusable ones show (run 40861881955:
    `Ubuntu / build and test (ubuntu-26.04)`)."""
    return {"jobs": [{**job, "name": f"{caller} / {job['name']}"} for job in listing["jobs"]]}


#: The watched images' cells as a nightly run lists them, each green.
WATCHED_CELLS = (
    "watch (ubuntu-latest, 3.12)", "watch (windows-latest, 3.12)",
    "watch (macos-latest, 3.12)", "watch (ubuntu-26.04, 3.12)",
)


def _watching(listing: dict[str, Any], failed: tuple[str, ...] = ()) -> dict[str, Any]:
    """A nightly run's listing: the cells of `listing` and the watched
    cells beside them, all under the calling job's name, the ones
    `failed` names failed."""
    assert set(failed) <= set(WATCHED_CELLS), failed
    watched = [
        {"name": name, "status": "completed", "conclusion": "failure" if name in failed else "success"}
        for name in WATCHED_CELLS
    ]
    return _called({"jobs": [*listing["jobs"], *watched]})


def _jobs(listing: dict[str, Any]) -> list[Any]:
    return list(mg.parse_jobs(json.dumps(listing)))


def _judge(listing: dict[str, Any], size: int = int(CELLS)) -> Any:
    return mg.judge(_jobs(listing), size)


class TestTheListing:
    def test_every_cell_green_passes(self) -> None:
        verdict = _judge(_recorded(NIGHTLY))
        assert verdict.passed, verdict.why
        assert verdict.failed == ()
        assert len(mg.blocking_cells(_jobs(_recorded(NIGHTLY)))) == 12

    def test_one_failed_cell_fails(self) -> None:
        verdict = _judge(_recorded(FAILED_CELL))
        assert not verdict.passed
        assert f"{RERUN_CELL} failure" in verdict.why, verdict.why
        assert verdict.failed == (RERUN_CELL,)

    def test_a_rerun_of_every_failed_cell_passes(self) -> None:
        """Run 33709478610's second attempt re-ran its one failed cell, which
        passed: the listing of that attempt is every cell green."""
        verdict = _judge(_recorded(RERUN))
        assert verdict.passed, verdict.why

    def test_a_rerun_attempt_lists_every_job(self) -> None:
        """What the gate relies on, as the recording shows it: a re-run
        attempt's listing carries every job of the run, the ones it ran
        again (started after every job of the first attempt) and a copy of
        each other one, with the start and the conclusion it had."""
        first = {job["name"]: job for job in _recorded(FAILED_CELL)["jobs"]}
        second = {job["name"]: job for job in _recorded(RERUN)["jobs"]}
        assert set(first) == set(second)
        latest = max(job["startedAt"] for job in first.values())
        rerun = {name for name, job in second.items() if job["startedAt"] > latest}
        assert rerun == {RERUN_CELL}
        for name in set(first) - rerun:
            assert (second[name]["startedAt"], second[name]["conclusion"]) == (
                first[name]["startedAt"], first[name]["conclusion"]
            ), name
        assert (first[RERUN_CELL]["conclusion"], second[RERUN_CELL]["conclusion"]) == ("failure", "success")

    def test_one_failed_cell_beside_a_rerun_of_another_fails(self) -> None:
        """Two cells failed and one of them was re-run on its own: the second
        attempt's listing carries the other's failure, whatever the matrix's
        result says (#1659)."""
        listing = _with(_recorded(RERUN), {"test (windows-latest, 3.11)": "failure"})
        verdict = _judge(listing)
        assert not verdict.passed
        assert "test (windows-latest, 3.11) failure" in verdict.why, verdict.why
        assert verdict.failed == ("test (windows-latest, 3.11)",)

    def test_the_advisory_cell_red_passes(self) -> None:
        verdict = _judge(_with(_recorded(NIGHTLY), {ADVISORY_CELL: "failure"}))
        assert verdict.passed, verdict.why
        assert verdict.failed == ()

    @pytest.mark.parametrize("conclusion", ["cancelled", "skipped", "", "timed_out", "neutral"])
    def test_a_cell_that_did_not_pass_fails(self, conclusion: str) -> None:
        verdict = _judge(_with(_recorded(NIGHTLY), {"test (macos-26, 3.13)": conclusion}))
        assert not verdict.passed, verdict.why
        assert "test (macos-26, 3.13)" in verdict.why
        assert verdict.failed == ()

    def test_the_shards_are_not_cells(self) -> None:
        """A pull request's run lists five shards of the suite, each a
        required check of its own; none of them is a cell of the full
        matrix, so a red shard beside a green matrix is not the gate's."""
        shards = [job for job in _recorded(PULL_REQUEST)["jobs"] if "shard" in job["name"]]
        assert len(shards) == 5, shards
        red = [{**shards[0], "conclusion": "failure"}, *shards[1:]]
        verdict = _judge({"jobs": _recorded(NIGHTLY)["jobs"] + red})
        assert verdict.passed, verdict.why

    def test_a_listing_without_a_cell_fails(self) -> None:
        listing = {"jobs": [job for job in _recorded(NIGHTLY)["jobs"] if not job["name"].startswith("test (")]}
        verdict = _judge(listing)
        assert not verdict.passed
        assert "no cell" in verdict.why, verdict.why

    def test_a_listing_missing_a_cell_fails(self) -> None:
        """The first attempt's listing without its one failed cell is every
        listed cell green; it is a listing of 12 of the 13 cells the matrix
        ran, and fails."""
        listing = {"jobs": [job for job in _recorded(FAILED_CELL)["jobs"] if job["name"] != RERUN_CELL]}
        verdict = _judge(listing)
        assert not verdict.passed
        assert "12 cells" in verdict.why and "runs 13" in verdict.why, verdict.why

    def test_a_listing_with_a_cell_too_many_fails(self) -> None:
        jobs = _recorded(NIGHTLY)["jobs"]
        twice = next(job for job in jobs if job["name"] == "test (macos-15, 3.12)")
        verdict = _judge({"jobs": [*jobs, twice]})
        assert not verdict.passed
        assert "14 cells" in verdict.why, verdict.why

    def test_a_cell_under_a_name_the_gate_does_not_read_is_missing(self) -> None:
        """The nightly recording as `gh` printed it, before #1656 dropped
        the Linux 3.12 cell's ` + coverage` suffix: the gate reads 12 cells
        where the matrix ran 13, and fails rather than pass a cell it never
        read."""
        verdict = _judge(_raw(NIGHTLY))
        assert not verdict.passed
        assert "12 cells" in verdict.why, verdict.why

    def test_the_skipped_matrix_is_not_a_green_one(self) -> None:
        """A skipped matrix is listed as one job under its unexpanded name;
        read where the matrix ran, it fails."""
        jobs = _jobs(_recorded(PULL_REQUEST))
        assert [job.name for job in mg.blocking_cells(jobs)] == [
            "test (${{ matrix.os }}, ${{ matrix.python-version }})"
        ]
        assert not mg.judge(jobs, int(CELLS)).passed
        assert not mg.judge(jobs, 1).passed


class TestANightlyRunsListing:
    """The nightly run is nightly-matrix.yml's call of ci.yml, whose run
    lists every job under the calling job's name.  Read through it, the
    listing is the push run's: the same cells under the names ci.yml gives
    them, the advisory one among them.  Without the reading, a nightly run
    lists no cell at all and its gate fails every night."""

    def test_every_cell_green_passes(self) -> None:
        verdict = _judge(_called(_recorded(NIGHTLY)))
        assert verdict.passed, verdict.why
        assert len(mg.blocking_cells(_jobs(_called(_recorded(NIGHTLY))))) == 12

    def test_a_failed_cell_is_named_as_ci_yml_names_it(self) -> None:
        verdict = _judge(_called(_recorded(FAILED_CELL)))
        assert not verdict.passed
        assert verdict.failed == (RERUN_CELL,)
        assert f"{RERUN_CELL} failure" in verdict.why, verdict.why

    def test_the_advisory_cell_red_passes(self) -> None:
        verdict = _judge(_called(_with(_recorded(NIGHTLY), {ADVISORY_CELL: "failure"})))
        assert verdict.passed, verdict.why

    def test_a_listing_missing_a_cell_fails(self) -> None:
        listing = {"jobs": [job for job in _recorded(FAILED_CELL)["jobs"] if job["name"] != RERUN_CELL]}
        verdict = _judge(_called(listing))
        assert not verdict.passed
        assert "12 cells" in verdict.why, verdict.why

    @pytest.mark.parametrize(
        ("listed", "named"),
        [
            ("CI / test (macos-15, 3.12)", "test (macos-15, 3.12)"),
            ("Nightly / watch (ubuntu-latest, 3.12)", "watch (ubuntu-latest, 3.12)"),
            ("test (macos-15, 3.12)", "test (macos-15, 3.12)"),
            ("test (ubuntu-24.04, 3.12, shard 1/3)", "test (ubuntu-24.04, 3.12, shard 1/3)"),
            ("CI / test (ubuntu-24.04, 3.12, shard 1/3)", "test (ubuntu-24.04, 3.12, shard 1/3)"),
            ("matrix-gate", "matrix-gate"),
        ],
    )
    def test_a_name_is_read_through_its_caller_alone(self, listed: str, named: str) -> None:
        """A shard's `K/N` has no space around its slash, so no name ci.yml
        gives a job loses anything."""
        assert mg.bare(listed) == named

    def test_a_name_under_two_callers_or_of_another_job_is_no_cell(self) -> None:
        """The gate reads through one caller's name, the one a call's run puts
        before a job's own, and no further: a job listed under two callers'
        names is no cell of ci.yml's, and neither is a job whose own name
        only begins as a cell's does, under a caller or not."""
        names = (
            "Nightly / CI / test (macos-15, 3.12)",
            "test-extra (macos-15, 3.12)",
            "CI / test-extra (macos-15, 3.12)",
        )
        jobs = [mg.Job(name, "completed", "failure") for name in names]
        assert mg.cells_of(jobs) == []
        assert mg.failed_cells(jobs) == ()

    def test_a_shard_under_a_caller_is_no_cell(self) -> None:
        shards = [job for job in _recorded(PULL_REQUEST)["jobs"] if "shard" in job["name"]]
        red = _called({"jobs": [{**shards[0], "conclusion": "failure"}, *shards[1:]]})
        verdict = _judge({"jobs": _called(_recorded(NIGHTLY))["jobs"] + red["jobs"]})
        assert verdict.passed, verdict.why


class TestTheWatchedCells:
    """The nightly run's watch job runs the floating labels and the newest
    image no cell of the full matrix runs.  Its cells are no cells of the
    full matrix: the verdict and the matrix's size read none of them, and
    the ones that failed are the `watched` output, which matrix-issue
    files."""

    def test_a_green_night_names_none(self) -> None:
        verdict = mg.gate("success", "", "success", CELLS, lambda: _jobs(_watching(_recorded(NIGHTLY))))
        assert verdict.passed, verdict.why
        assert (verdict.failed, verdict.watched) == ((), ())

    def test_a_failed_watched_cell_is_named_and_decides_nothing(self) -> None:
        failed = ("watch (ubuntu-latest, 3.12)", "watch (windows-latest, 3.12)")
        verdict = mg.gate("success", "", "success", CELLS, lambda: _jobs(_watching(_recorded(NIGHTLY), failed)))
        assert verdict.passed, verdict.why
        assert verdict.failed == ()
        assert verdict.watched == failed

    def test_a_failed_cell_and_a_failed_watched_cell_are_each_named(self) -> None:
        failed = ("watch (ubuntu-26.04, 3.12)",)
        verdict = mg.gate(
            "success", "", "failure", CELLS, lambda: _jobs(_watching(_recorded(FAILED_CELL), failed)),
        )
        assert not verdict.passed
        assert verdict.failed == (RERUN_CELL,)
        assert verdict.watched == failed

    def test_a_watched_cell_is_no_cell_of_the_matrix(self) -> None:
        jobs = _jobs(_watching(_recorded(NIGHTLY)))
        assert len(mg.cells_of(jobs)) == int(CELLS)
        assert [job.name for job in mg.watched_cells(jobs)] == list(WATCHED_CELLS)

    @pytest.mark.parametrize("conclusion", ["cancelled", "skipped", "", "timed_out"])
    def test_only_a_failure_is_named(self, conclusion: str) -> None:
        """`failure` is what a run that ran its tests and found one red
        concludes; any other conclusion is the run's page to show."""
        listing = _watching(_recorded(NIGHTLY))
        listing = _with(listing, {"CI / watch (macos-latest, 3.12)": conclusion})
        assert mg.failed_watched(_jobs(listing)) == ()

    def test_an_unreadable_listing_names_no_watched_cell(self) -> None:
        def unreadable() -> list[Any]:
            raise mg.ListingError("HTTP 502")

        verdict = mg.gate("success", "", "success", CELLS, unreadable)
        assert not verdict.passed
        assert verdict.watched == ()


class TestTheVerdict:
    """`gate`: `decide`'s verdict, and where the matrix ran the listing's
    too, over every combination of the three results and four listings."""

    LISTING_STATES = ("green", "red", "short", "unreadable")

    @staticmethod
    def _listing(state: str) -> Callable[[], list[Any]]:
        def read() -> list[Any]:
            if state == "unreadable":
                raise mg.ListingError("HTTP 502")
            listing = _recorded(RERUN)
            if state == "red":
                listing = _with(listing, {"test (windows-latest, 3.11)": "failure"})
            if state == "short":
                listing = {"jobs": [job for job in listing["jobs"] if job["name"] != "test (macos-26, 3.12)"]}
            return _jobs(listing)

        return read

    @pytest.mark.parametrize(
        ("plan", "release", "matrix", "listing"),
        list(itertools.product(RESULTS, RELEASES, RESULTS, LISTING_STATES)),
    )
    def test_every_combination(self, plan: str, release: str, matrix: str, listing: str) -> None:
        verdict = mg.gate(plan, release, matrix, CELLS, self._listing(listing))
        passes = (plan, release, matrix) in PASSING and (matrix == "skipped" or listing == "green")
        assert verdict.passed is passes, verdict.why
        assert verdict.why.strip()

    def test_a_single_cell_rerun_cannot_pass_the_gate(self) -> None:
        """The matrix's result reads `success` after the re-run of one of two
        failed cells; the listing does not."""
        verdict = mg.gate("success", "true", "success", CELLS, self._listing("red"))
        assert not verdict.passed
        assert verdict.failed == ("test (windows-latest, 3.11)",)

    @pytest.mark.parametrize(("plan", "release"), [("success", "false"), ("success", "true"),
                                                   ("success", ""), ("failure", "false")])
    def test_the_listing_is_not_read_where_the_matrix_was_skipped(self, plan: str, release: str) -> None:
        """Nor is the matrix's size, which a skipped matrix does not state."""
        def unread() -> list[Any]:
            raise AssertionError("the listing was read")

        verdict = mg.gate(plan, release, "skipped", "", unread)
        assert verdict.passed is mg.decide(plan, release, "skipped")[0]

    @pytest.mark.parametrize("matrix", ["success", "failure", "cancelled"])
    def test_the_listing_is_not_read_where_the_plan_failed(self, matrix: str) -> None:
        def unread() -> list[Any]:
            raise AssertionError("the listing was read")

        assert not mg.gate("failure", "true", matrix, CELLS, unread).passed

    def test_an_unreadable_listing_fails_closed(self) -> None:
        verdict = mg.gate("success", "true", "success", CELLS, self._listing("unreadable"))
        assert not verdict.passed
        assert "HTTP 502" in verdict.why

    @pytest.mark.parametrize("size", ["", "0", "-1", "x", "13 ", "1.5", "013"])
    def test_a_matrix_size_it_cannot_read_fails_closed(self, size: str) -> None:
        """Where the matrix ran, a size that is not a number of cells fails a
        green listing, and the cells a red one failed are still handed on."""
        green = mg.gate("success", "true", "success", size, self._listing("green"))
        assert not green.passed
        assert repr(size) in green.why, green.why
        red = mg.gate("success", "", "failure", size, self._listing("red"))
        assert not red.passed
        assert red.failed == ("test (windows-latest, 3.11)",)

    def test_a_failed_matrix_names_its_failed_cells(self) -> None:
        verdict = mg.gate("success", "true", "failure", CELLS, lambda: _jobs(_recorded(FAILED_CELL)))
        assert not verdict.passed
        assert verdict.failed == (RERUN_CELL,)


class TestReadingGh:
    def test_it_asks_gh_for_the_jobs_of_one_attempt(self) -> None:
        assert mg.gh_command("33709478610", "2") == [
            "gh", "run", "view", "33709478610", "--attempt", "2", "--json", "jobs",
        ]

    @pytest.mark.parametrize("size", ["1", "13", "100"])
    def test_it_reads_the_matrix_size(self, size: str) -> None:
        assert mg.matrix_size(size) == int(size)

    def test_it_reads_gh_json(self) -> None:
        jobs = _jobs(_recorded(FAILED_CELL))
        assert len(jobs) == 21
        assert mg.Job(RERUN_CELL, "completed", "failure") in jobs

    def test_a_job_still_running_reads_as_no_conclusion(self) -> None:
        """The gate's own job is running while it lists the run; the API's
        null conclusion reads as none, not as an unreadable listing."""
        text = json.dumps({"jobs": [{"name": "matrix-gate", "status": "in_progress", "conclusion": None}]})
        assert mg.parse_jobs(text) == [mg.Job("matrix-gate", "in_progress", "")]

    @pytest.mark.parametrize(
        "text",
        [
            "", "not json", "[]", "{}", '{"jobs": {}}', '{"jobs": [null]}',
            '{"jobs": [{"name": "lint"}]}',
            '{"jobs": [{"name": 1, "status": "completed", "conclusion": "success"}]}',
            '{"jobs": [{"name": "lint", "status": "completed", "conclusion": 0}]}',
        ],
    )
    def test_output_it_cannot_read_is_a_listing_error(self, text: str) -> None:
        with pytest.raises(mg.ListingError):
            mg.parse_jobs(text)


# ---------------------------------------------------------------------------
# The command line, against a stand-in for gh
# ---------------------------------------------------------------------------


def _serve(
    monkeypatch: pytest.MonkeyPatch, listings: dict[str, dict[str, Any]], asked: list[str] | None = None,
) -> None:
    """Stand in for `gh run view`: the listing recorded under the command
    the gate runs, or gh's own failure for a command nothing is recorded
    under."""

    def run(command: list[str], **_: Any) -> subprocess.CompletedProcess[str]:
        line = " ".join(command)
        if asked is not None:
            asked.append(line)
        if line not in listings:
            return subprocess.CompletedProcess(command, 1, "", f"no recording for {line}")
        return subprocess.CompletedProcess(command, 0, json.dumps(listings[line]), "")

    monkeypatch.setattr(subprocess, "run", run)


def _environment(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path, plan: str, release: str, matrix: str,
    run_id: str | None = "33709478610", attempt: str | None = "2", cells: str | None = CELLS,
) -> Path:
    output = tmp_path / "github_output"
    output.write_text("", encoding="utf-8")
    for name, value in {
        "PLAN_RESULT": plan, "RELEASE": release, "TEST_RESULT": matrix, "MATRIX_CELLS": cells,
        "GITHUB_RUN_ID": run_id, "GITHUB_RUN_ATTEMPT": attempt, "GITHUB_OUTPUT": str(output),
    }.items():
        if value is None:
            monkeypatch.delenv(name, raising=False)
        else:
            monkeypatch.setenv(name, value)
    return output


class TestTheCommand:
    def test_a_single_cell_rerun_does_not_pass(
        self, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str], tmp_path: Path,
    ) -> None:
        """#1659's repro: the second attempt re-ran one failed cell, which
        passed, and left another failed; the matrix's result reads
        `success`.  The gate fails, names the cell, and hands it on."""
        output = _environment(monkeypatch, tmp_path, "success", "true", "success")
        asked: list[str] = []
        _serve(monkeypatch, {RERUN: _with(_recorded(RERUN), {"test (windows-latest, 3.11)": "failure"})}, asked)
        assert mg.main() == 1
        out = capsys.readouterr().out
        assert out.startswith("::error::"), out
        assert "test (windows-latest, 3.11)" in out
        assert asked == [RERUN]
        assert output.read_text(encoding="utf-8") == 'failed=["test (windows-latest, 3.11)"]\n'

    def test_a_night_hands_on_its_failed_watched_cells(
        self, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str], tmp_path: Path,
    ) -> None:
        """A nightly run whose full matrix passed and one of whose watched
        cells failed: the gate passes, warns, and writes the watched cell to
        its `watched` output under the name ci.yml gives it."""
        output = _environment(monkeypatch, tmp_path, "success", "", "success",
                              run_id="38232649508", attempt="1")
        listing = _watching(_recorded(NIGHTLY), ("watch (windows-latest, 3.12)",))
        _serve(monkeypatch, {"gh run view 38232649508 --attempt 1 --json jobs": listing})
        assert mg.main() == 0
        out = capsys.readouterr().out
        assert "::warning::" in out and "watch (windows-latest, 3.12)" in out, out
        assert output.read_text(encoding="utf-8") == 'watched=["watch (windows-latest, 3.12)"]\n'

    def test_the_rerun_of_every_failed_cell_passes(
        self, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str], tmp_path: Path,
    ) -> None:
        output = _environment(monkeypatch, tmp_path, "success", "true", "success")
        _serve(monkeypatch, {RERUN: _recorded(RERUN)})
        assert mg.main() == 0, capsys.readouterr().out
        assert output.read_text(encoding="utf-8") == ""

    def test_gh_failing_fails_the_gate(
        self, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str], tmp_path: Path,
    ) -> None:
        _environment(monkeypatch, tmp_path, "success", "true", "success")
        _serve(monkeypatch, {})
        assert mg.main() == 1
        out = capsys.readouterr().out
        assert out.startswith("::error::"), out
        assert "no recording for" in out

    @pytest.mark.parametrize(
        ("run_id", "attempt"),
        [(None, "1"), ("", "1"), ("12x", "1"), ("²", "1"),
         ("33709478610", None), ("33709478610", ""), ("33709478610", "two"), ("33709478610", "0")],
    )
    def test_a_run_it_cannot_name_fails_closed(
        self, monkeypatch: pytest.MonkeyPatch, tmp_path: Path, run_id: str | None, attempt: str | None,
    ) -> None:
        """Actions sets the run's id and attempt on every run, so a missing
        or malformed one fails the gate before `gh` is asked anything."""
        _environment(monkeypatch, tmp_path, "success", "true", "success", run_id=run_id, attempt=attempt)
        asked: list[str] = []
        _serve(monkeypatch, {}, asked)
        assert mg.main() == 1
        assert asked == []

    @pytest.mark.parametrize("cells", [None, "", "twelve"])
    def test_a_matrix_size_it_cannot_read_fails_closed(
        self, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str], tmp_path: Path,
        cells: str | None,
    ) -> None:
        _environment(monkeypatch, tmp_path, "success", "true", "success", cells=cells)
        _serve(monkeypatch, {RERUN: _recorded(RERUN)})
        assert mg.main() == 1
        assert capsys.readouterr().out.startswith("::error::")

    def test_the_matrix_size_is_the_one_the_listing_is_held_to(
        self, monkeypatch: pytest.MonkeyPatch, tmp_path: Path,
    ) -> None:
        """A green listing of 13 cells fails a matrix that states 14."""
        _environment(monkeypatch, tmp_path, "success", "true", "success", cells="14")
        _serve(monkeypatch, {RERUN: _recorded(RERUN)})
        assert mg.main() == 1

    def test_a_failed_matrix_hands_on_its_failed_cells(
        self, monkeypatch: pytest.MonkeyPatch, tmp_path: Path,
    ) -> None:
        output = _environment(monkeypatch, tmp_path, "success", "", "failure", attempt="1")
        _serve(monkeypatch, {FAILED_CELL: _recorded(FAILED_CELL)})
        assert mg.main() == 1
        assert output.read_text(encoding="utf-8") == f'failed=["{RERUN_CELL}"]\n'

    def test_the_skipped_matrix_lists_nothing(
        self, monkeypatch: pytest.MonkeyPatch, tmp_path: Path,
    ) -> None:
        _environment(monkeypatch, tmp_path, "success", "false", "skipped")
        asked: list[str] = []
        _serve(monkeypatch, {}, asked)
        assert mg.main() == 0
        assert asked == []


@pytest.mark.parametrize(
    ("plan", "release", "matrix", "status"),
    [
        ("success", "false", "skipped", 0),
        ("success", "true", "success", 0),
        ("success", "true", "skipped", 1),
        ("failure", "", "skipped", 1),
    ],
)
def test_the_command_reads_its_environment(
    monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str], tmp_path: Path,
    plan: str, release: str, matrix: str, status: int,
) -> None:
    _environment(monkeypatch, tmp_path, plan, release, matrix)
    _serve(monkeypatch, {RERUN: _recorded(RERUN)})
    assert mg.main() == status
    out = capsys.readouterr().out
    assert out.strip(), "the verdict is printed for the log"
    if status:
        assert out.startswith("::error::"), out


def test_an_absent_variable_fails(monkeypatch: pytest.MonkeyPatch) -> None:
    for name in ("PLAN_RESULT", "RELEASE", "TEST_RESULT"):
        monkeypatch.delenv(name, raising=False)
    assert mg.main() == 1


# ---------------------------------------------------------------------------
# The workflow
# ---------------------------------------------------------------------------


def _ci_jobs() -> dict[str, Any]:
    return dict(yaml.safe_load(CI.read_text(encoding="utf-8"))["jobs"])


def _cell_names(job_name: str) -> dict[str, dict[str, object]]:
    """The name each cell of a matrix job runs under, with the cell."""
    job = _ci_jobs()[job_name]
    return {render(str(job["name"]), cell): cell for cell in _matrix_cells(job)}


class TestTheWorkflow:
    def test_every_cell_of_the_matrix_is_a_cell_the_gate_reads(self) -> None:
        names = _cell_names("test")
        assert len(names) == 13, sorted(names)
        for name in names:
            assert mg.CELL.fullmatch(name), name

    def test_the_advisory_cells_are_the_matrix_s(self) -> None:
        """A cell the gate lets fail is one the job lets fail: a cell
        `ADVISORY` named that ci.yml made blocking would pass the gate red,
        and one ci.yml made advisory but `ADVISORY` missed would fail it."""
        job = _ci_jobs()["test"]
        advisory = {
            name for name, cell in _cell_names("test").items()
            if evaluate(str(job["continue-on-error"]), cell)
        }
        assert advisory == mg.ADVISORY == {ADVISORY_CELL}

    def test_no_shard_is_a_cell(self) -> None:
        names = _cell_names("shard")
        assert len(names) == 5, sorted(names)
        for name in names:
            assert not mg.CELL.fullmatch(name), name

    def test_every_cell_names_its_image(self) -> None:
        """No cell runs on a label GitHub moves (`ubuntu-latest`,
        `macos-latest`, `windows-latest`): README § Supported platforms
        names the images the full matrix tests, Ubuntu 24.04 on x86_64 and
        aarch64 and Windows Server 2025 among them.  The floating labels are
        the watch job's, on the nightly run alone."""
        runners = {str(cell["matrix.os"]) for cell in _cell_names("test").values()}
        assert runners == {"ubuntu-24.04", "ubuntu-24.04-arm", "macos-15", "macos-26", "windows-2025-vs2026"}, runners
        for runner in runners:
            assert "latest" not in runner, runner

    def test_every_watched_cell_is_one_the_gate_reads_as_watched(self) -> None:
        names = _cell_names("watch")
        assert sorted(names) == sorted(WATCHED_CELLS), sorted(names)
        for name in names:
            assert mg.WATCHED.fullmatch(name) and not mg.CELL.fullmatch(name), name

    def test_the_job_hands_the_script_its_results_and_a_token(self) -> None:
        """The job runs after the plan, the matrix and the watched images
        whatever happened to them (`always()`), and passes the script the
        plan's and the matrix's results and the plan's answer under the
        names it reads, with a token that can list the run's jobs; the run's
        id and attempt are Actions' own variables.  It hands on the failed
        cells and the failed watched cells, as two outputs."""
        job = _ci_jobs()["matrix-gate"]
        needs = job["needs"]
        assert {"plan", "test", "watch"} <= set([needs] if isinstance(needs, str) else needs), needs
        assert str(job["if"]).replace("${{", "").replace("}}", "").strip() == "always()", job["if"]
        assert job["permissions"] == {"actions": "read", "contents": "read"}
        steps = [step for step in job["steps"] if "scripts/matrix_gate.py" in str(step.get("run", ""))]
        assert len(steps) == 1, job["steps"]
        assert steps[0]["env"] == {
            "PLAN_RESULT": "${{ needs.plan.result }}",
            "RELEASE": "${{ needs.plan.outputs.release }}",
            "TEST_RESULT": "${{ needs.test.result }}",
            "MATRIX_CELLS": "${{ needs.test.outputs.cells }}",
            "GH_TOKEN": "${{ github.token }}",
            "GH_REPO": "${{ github.repository }}",
        }
        assert job["outputs"] == {
            name: f"${{{{ steps.{steps[0]['id']}.outputs.{name} }}}}" for name in ("failed", "watched")
        }

    def test_the_matrix_states_its_size(self) -> None:
        """Every cell sets the `test` job's `cells` output to the matrix's
        size, `strategy.job-total`, so whichever cell sets it last, it is
        the number of cells the gate holds the listing to: the 13 the
        workflow's matrix runs."""
        assert _ci_jobs()["test"]["outputs"] == {"cells": "${{ strategy.job-total }}"}
        assert len(_cell_names("test")) == 13
