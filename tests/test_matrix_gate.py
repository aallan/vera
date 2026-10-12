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
`gh`, here a stand-in that serves the recordings.  The pins at the end hold
the gate's reading of cell names and of the advisory cell to ci.yml's
matrix, and the job to what the script reads.
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


def _recorded(command: str) -> dict[str, Any]:
    """A recorded listing as `gh` printed it, its cells named as today."""
    listing = json.loads(LISTINGS.read_text(encoding="utf-8"))[command]
    return {"jobs": [{**job, "name": _RENAMED.get(job["name"], job["name"])} for job in listing["jobs"]]}


def _with(listing: dict[str, Any], conclusions: dict[str, str]) -> dict[str, Any]:
    """A listing with the named jobs' conclusions replaced; every name must
    be a job of the listing, so a misspelt one cannot leave it as it was."""
    names = {job["name"] for job in listing["jobs"]}
    assert set(conclusions) <= names, sorted(set(conclusions) - names)
    return {"jobs": [
        {**job, "conclusion": conclusions.get(job["name"], job["conclusion"])} for job in listing["jobs"]
    ]}


def _jobs(listing: dict[str, Any]) -> list[Any]:
    return list(mg.parse_jobs(json.dumps(listing)))


def _judge(listing: dict[str, Any]) -> Any:
    return mg.judge(_jobs(listing))


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

    def test_the_skipped_matrix_is_not_a_green_one(self) -> None:
        """A skipped matrix is listed as one job under its unexpanded name;
        read where the matrix ran, it fails."""
        jobs = _jobs(_recorded(PULL_REQUEST))
        assert [job.name for job in mg.blocking_cells(jobs)] == [
            "test (${{ matrix.os }}, ${{ matrix.python-version }})"
        ]
        assert not mg.judge(jobs).passed


class TestTheVerdict:
    """`gate`: `decide`'s verdict, and where the matrix ran the listing's
    too, over every combination of the three results and three listings."""

    LISTING_STATES = ("green", "red", "unreadable")

    @staticmethod
    def _listing(state: str) -> Callable[[], list[Any]]:
        def read() -> list[Any]:
            if state == "unreadable":
                raise mg.ListingError("HTTP 502")
            listing = _recorded(RERUN)
            if state == "red":
                listing = _with(listing, {"test (windows-latest, 3.11)": "failure"})
            return _jobs(listing)

        return read

    @pytest.mark.parametrize(
        ("plan", "release", "matrix", "listing"),
        list(itertools.product(RESULTS, RELEASES, RESULTS, LISTING_STATES)),
    )
    def test_every_combination(self, plan: str, release: str, matrix: str, listing: str) -> None:
        verdict = mg.gate(plan, release, matrix, self._listing(listing))
        passes = (plan, release, matrix) in PASSING and (matrix == "skipped" or listing == "green")
        assert verdict.passed is passes, verdict.why
        assert verdict.why.strip()

    def test_a_single_cell_rerun_cannot_pass_the_gate(self) -> None:
        """The matrix's result reads `success` after the re-run of one of two
        failed cells; the listing does not."""
        verdict = mg.gate("success", "true", "success", self._listing("red"))
        assert not verdict.passed
        assert verdict.failed == ("test (windows-latest, 3.11)",)

    @pytest.mark.parametrize(("plan", "release"), [("success", "false"), ("success", "true"),
                                                   ("success", ""), ("failure", "false")])
    def test_the_listing_is_not_read_where_the_matrix_was_skipped(self, plan: str, release: str) -> None:
        def unread() -> list[Any]:
            raise AssertionError("the listing was read")

        verdict = mg.gate(plan, release, "skipped", unread)
        assert verdict.passed is mg.decide(plan, release, "skipped")[0]

    @pytest.mark.parametrize("matrix", ["success", "failure", "cancelled"])
    def test_the_listing_is_not_read_where_the_plan_failed(self, matrix: str) -> None:
        def unread() -> list[Any]:
            raise AssertionError("the listing was read")

        assert not mg.gate("failure", "true", matrix, unread).passed

    def test_an_unreadable_listing_fails_closed(self) -> None:
        verdict = mg.gate("success", "true", "success", self._listing("unreadable"))
        assert not verdict.passed
        assert "HTTP 502" in verdict.why

    def test_a_failed_matrix_names_its_failed_cells(self) -> None:
        verdict = mg.gate("success", "true", "failure", lambda: _jobs(_recorded(FAILED_CELL)))
        assert not verdict.passed
        assert verdict.failed == (RERUN_CELL,)


class TestReadingGh:
    def test_it_asks_gh_for_the_jobs_of_one_attempt(self) -> None:
        assert mg.gh_command("33709478610", "2") == [
            "gh", "run", "view", "33709478610", "--attempt", "2", "--json", "jobs",
        ]
        assert mg.gh_command("38232649508", "") == ["gh", "run", "view", "38232649508", "--json", "jobs"]

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
    run_id: str | None = "33709478610", attempt: str | None = "2",
) -> Path:
    output = tmp_path / "github_output"
    output.write_text("", encoding="utf-8")
    for name, value in {
        "PLAN_RESULT": plan, "RELEASE": release, "TEST_RESULT": matrix,
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

    def test_the_rerun_of_every_failed_cell_passes(
        self, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str], tmp_path: Path,
    ) -> None:
        output = _environment(monkeypatch, tmp_path, "success", "true", "success")
        _serve(monkeypatch, {RERUN: _recorded(RERUN)})
        assert mg.main() == 0, capsys.readouterr().out
        assert output.read_text(encoding="utf-8") == ""

    def test_without_an_attempt_it_lists_the_run(
        self, monkeypatch: pytest.MonkeyPatch, tmp_path: Path,
    ) -> None:
        _environment(monkeypatch, tmp_path, "success", "", "success", run_id="38232649508", attempt=None)
        asked: list[str] = []
        _serve(monkeypatch, {NIGHTLY: _recorded(NIGHTLY)}, asked)
        assert mg.main() == 0
        assert asked == [NIGHTLY]

    def test_gh_failing_fails_the_gate(
        self, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str], tmp_path: Path,
    ) -> None:
        _environment(monkeypatch, tmp_path, "success", "true", "success")
        _serve(monkeypatch, {})
        assert mg.main() == 1
        out = capsys.readouterr().out
        assert out.startswith("::error::"), out
        assert "no recording for" in out

    @pytest.mark.parametrize(("run_id", "attempt"), [(None, "1"), ("", "1"), ("12x", "1"), ("33709478610", "two")])
    def test_a_run_it_cannot_name_fails_closed(
        self, monkeypatch: pytest.MonkeyPatch, tmp_path: Path, run_id: str | None, attempt: str,
    ) -> None:
        _environment(monkeypatch, tmp_path, "success", "true", "success", run_id=run_id, attempt=attempt)
        asked: list[str] = []
        _serve(monkeypatch, {}, asked)
        assert mg.main() == 1
        assert asked == []

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

    def test_the_linux_and_macos_cells_name_their_release(self) -> None:
        """No cell runs on an alias GitHub moves (`ubuntu-latest`,
        `macos-latest`): README § Supported platforms names the releases the
        full matrix tests, Ubuntu 24.04 on x86_64 and aarch64 among them."""
        runners = {str(cell["matrix.os"]) for cell in _cell_names("test").values()}
        assert {"ubuntu-24.04", "ubuntu-24.04-arm", "macos-15", "macos-26"} <= runners, runners
        for runner in runners:
            if runner.startswith(("ubuntu", "macos")):
                assert "latest" not in runner, runner

    def test_the_job_hands_the_script_its_results_and_a_token(self) -> None:
        """The job runs after the plan and the matrix whatever happened to them
        (`always()`), and passes the script their results and the plan's
        answer under the names it reads, with a token that can list the
        run's jobs; the run's id and attempt are Actions' own variables."""
        job = _ci_jobs()["matrix-gate"]
        needs = job["needs"]
        assert {"plan", "test"} <= set([needs] if isinstance(needs, str) else needs), needs
        assert str(job["if"]).replace("${{", "").replace("}}", "").strip() == "always()", job["if"]
        assert job["permissions"] == {"actions": "read", "contents": "read"}
        steps = [step for step in job["steps"] if "scripts/matrix_gate.py" in str(step.get("run", ""))]
        assert len(steps) == 1, job["steps"]
        assert steps[0]["env"] == {
            "PLAN_RESULT": "${{ needs.plan.result }}",
            "RELEASE": "${{ needs.plan.outputs.release }}",
            "TEST_RESULT": "${{ needs.test.result }}",
            "GH_TOKEN": "${{ github.token }}",
            "GH_REPO": "${{ github.repository }}",
        }
        assert job["outputs"] == {"failed": f"${{{{ steps.{steps[0]['id']}.outputs.failed }}}}"}
