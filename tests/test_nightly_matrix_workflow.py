"""The nightly full matrix is a workflow of its own, and every gating job runs on a pinned image.

`release.yml` starts on the completion of the workflow named CI (ci.yml),
and its gate goes on only for CI's successful push run on main.  The nightly
full matrix was a schedule of ci.yml's own, so each night's completion
started a release run that the gate skipped whole, a grey run on the
Actions page every morning (run 40857508689, 2026-10-29).  The nightly run
is `nightly-matrix.yml`, Nightly matrix, which calls ci.yml with
`nightly: true`.  A called workflow's jobs run inside its caller's run,
which carries the caller's name and event: python/cpython's
`reusable-docs.yml` is called by its `build.yml` and pushed to directly,
and its run list holds its own push and dispatch runs and none of the calls
(measured 2026-10-29), so no run of Nightly matrix is a run of CI.  The
matrix keeps one definition, ci.yml's, and the release workflow is as it
was.

The runners: every job of every workflow runs on an explicit image (README
§ Supported platforms), so a label GitHub moves to a new OS release never
changes what a merge or a release is tested on; macOS was pinned for that
reason before.  The nightly run alone also runs the `watch` job on the
floating `-latest` labels and the newest release image no pinned cell runs:
advisory cells, whose failure files an issue (matrix-issue) and blocks
nothing.  Under every push and pull-request event, no job that runs takes a
runner outside the pinned images.
"""

from __future__ import annotations

import re
from pathlib import Path
from typing import Any

import yaml

from tests.test_gate_placement import EVENTS, _matrix_cells, evaluate, render

ROOT = Path(__file__).resolve().parent.parent
WORKFLOWS = ROOT / ".github" / "workflows"
CI = WORKFLOWS / "ci.yml"
NIGHTLY = WORKFLOWS / "nightly-matrix.yml"
RELEASE = WORKFLOWS / "release.yml"

#: The images every job runs on, the watch job's cells apart: the ones README
#: § Supported platforms names.  `windows-2025-vs2026` is the Windows Server
#: 2025 image by its own name: GitHub moved `windows-latest` and
#: `windows-2025` to it from the Visual Studio 2022 image in June 2026
#: (actions/runner-images#14017).
PINNED = frozenset({"ubuntu-24.04", "ubuntu-24.04-arm", "macos-15", "macos-26", "windows-2025-vs2026"})

#: The images the nightly run watches: the floating labels, and the newest
#: release image GitHub lists that no pinned cell runs.  The newest macOS
#: and Windows release images, `macos-26` and `windows-2025-vs2026`, are
#: pinned cells; `xcode-27`, macOS 27 with Xcode 27, is a preview, which
#: joins when GitHub lists it as a release image.
WATCHED = frozenset({"ubuntu-latest", "windows-latest", "macos-latest", "ubuntu-26.04"})

#: The events on which the merge path runs: every pull request and push.
GATING = tuple(event for event in EVENTS if not event.startswith("nightly"))
NIGHTLY_EVENTS = ("nightly schedule", "nightly dispatch")


def _load(path: Path) -> dict[Any, Any]:
    return dict(yaml.safe_load(path.read_text(encoding="utf-8")))


def _triggers(workflow: dict[Any, Any]) -> dict[str, Any]:
    # YAML 1.1 reads the bare key `on` as True.
    return dict(workflow["on"] if "on" in workflow else workflow[True])


def _runners(job: dict[str, Any]) -> list[str]:
    """The runner each of a job's cells takes; a runner that names no matrix
    value is every cell's."""
    runs_on = str(job.get("runs-on", ""))
    if "${{" not in runs_on:
        return [runs_on]
    return [render(runs_on, cell) for cell in _matrix_cells(job)]


def _runs(job: dict[str, Any], event: str) -> bool:
    condition = job.get("if")
    return condition is None or bool(evaluate(str(condition), EVENTS[event]))


# ---------------------------------------------------------------------------
# The nightly run is a workflow of its own, which calls ci.yml
# ---------------------------------------------------------------------------


def test_ci_runs_on_a_push_a_pull_request_and_a_call_and_on_no_schedule() -> None:
    """A schedule of ci.yml's own is a run of CI, whose completion starts a
    release run; the nightly run's schedule is nightly-matrix.yml's."""
    on = _triggers(_load(CI))
    assert "schedule" not in on
    assert set(on) == {"push", "pull_request", "workflow_call"}, on
    assert on["push"] == {"branches": ["main"]} and on["pull_request"] == {"branches": ["main"]}


def test_ci_takes_the_nightly_input_and_the_one_secret_it_reads() -> None:
    """`nightly` is what runs the full matrix and the watched images on a
    call, and the Codecov token is the one secret ci.yml reads beyond the
    token every called workflow gets."""
    call = _triggers(_load(CI))["workflow_call"]
    assert set(call["inputs"]) == {"nightly"}
    assert call["inputs"]["nightly"]["type"] == "boolean"
    assert call["inputs"]["nightly"]["default"] is False
    read = set(re.findall(r"\bsecrets\.(\w+)", CI.read_text(encoding="utf-8"))) - {"GITHUB_TOKEN"}
    assert read == {"CODECOV_TOKEN"}
    assert call["secrets"] == {name: {"required": False} for name in read}


def test_the_nightly_runs_on_its_schedule_and_on_demand() -> None:
    nightly = _load(NIGHTLY)
    assert nightly["name"] == "Nightly matrix"
    on = _triggers(nightly)
    assert set(on) == {"schedule", "workflow_dispatch"}, on
    assert on["schedule"] == [{"cron": "0 3 * * *"}]
    assert on["workflow_dispatch"] is None


def test_the_nightly_calls_ci_and_defines_no_matrix_of_its_own() -> None:
    """One definition of the full matrix: the nightly's one job is a call of
    ci.yml with `nightly: true`, so the test and watch matrices, matrix-gate
    and matrix-issue are ci.yml's own jobs, the run lists them under the
    job's name (`CI / test (ubuntu-24.04, 3.11)`), and nothing here runs a
    step."""
    nightly = _load(NIGHTLY)
    assert list(nightly["jobs"]) == ["ci"], nightly["jobs"]
    job = nightly["jobs"]["ci"]
    assert job["name"] == "CI"
    assert job["uses"] == "./.github/workflows/ci.yml"
    assert job["with"] == {"nightly": True}
    assert not {"strategy", "steps", "runs-on"} & set(job), job


def test_the_call_grants_what_ci_s_jobs_ask_and_passes_the_secrets_they_read() -> None:
    """A called workflow's jobs get no more than the caller grants, and a
    secret only when the caller passes it; the workflow itself grants
    nothing."""
    ci = _load(CI)
    asked: dict[str, str] = {}
    for job in ci["jobs"].values():
        for scope, level in (job.get("permissions") or {}).items():
            if asked.get(scope) != "write":
                asked[scope] = level
    nightly = _load(NIGHTLY)
    job = nightly["jobs"]["ci"]
    assert nightly["permissions"] == {}
    assert job["permissions"] == asked, (job["permissions"], asked)
    declared = _triggers(ci)["workflow_call"]["secrets"]
    assert job["secrets"] == {name: f"${{{{ secrets.{name} }}}}" for name in declared}


def test_the_nightly_sets_no_concurrency_group_of_its_own() -> None:
    """ci.yml's group governs the called run, under the caller's name, and
    a caller group of the same name would wait on itself."""
    nightly = _load(NIGHTLY)
    assert "concurrency" not in nightly
    assert all("concurrency" not in job for job in nightly["jobs"].values())


def test_the_nightly_run_has_a_concurrency_group_of_its_own() -> None:
    """A called workflow's `github.workflow` is its caller's, so the nightly
    run's group is neither a push run's nor a pull request's, and the
    `schedule` branch the group carried is gone."""
    concurrency = _load(CI)["concurrency"]
    assert "schedule" not in str(concurrency["group"])
    groups = {event: render(str(concurrency["group"]), {**EVENTS[event], "github.sha": "1" * 40})
              for event in EVENTS}
    assert groups["nightly schedule"] == "Nightly matrix-refs/heads/main"
    assert groups["nightly schedule"] not in {groups[event] for event in GATING}
    assert not evaluate(str(concurrency["cancel-in-progress"]), EVENTS["nightly schedule"])


def test_the_full_matrix_runs_nightly_and_where_the_version_rises() -> None:
    """The test job runs on the nightly run, scheduled or dispatched, and on
    a pull request or push that raises [project].version, and nowhere
    else."""
    job = _load(CI)["jobs"]["test"]
    running = {event for event in EVENTS if _runs(job, event)}
    assert running == {
        "pull request that raises the version", "push of a release merge into main", *NIGHTLY_EVENTS,
    }, running


def test_a_failed_cell_files_on_the_scheduled_nightly_and_the_push_run() -> None:
    """matrix-issue files where no pull request's checks show the failure:
    the push run and the scheduled nightly run.  A dispatched nightly run is
    watched by whoever started it."""
    job = _load(CI)["jobs"]["matrix-issue"]
    failed = {"needs.test.result": "failure", "needs.matrix-gate.outputs.failed": '["test (macos-15, 3.11)"]'}
    filing = {event for event in EVENTS if evaluate(str(job["if"]), {**EVENTS[event], **failed})}
    assert filing == {"push of a merge into main", "push of a release merge into main", "nightly schedule"}, filing


def test_a_failed_watched_cell_alone_files_where_a_failed_cell_does() -> None:
    """A night on which only a watched cell failed: the matrix passed, the
    gate named no failed cell, and its `watched` output names one.
    matrix-issue files on the events it files a failed cell on, and on no
    other."""
    job = _load(CI)["jobs"]["matrix-issue"]
    watched = {"needs.matrix-gate.outputs.watched": '["watch (ubuntu-latest, 3.12)"]'}
    filing = {event for event in EVENTS if evaluate(str(job["if"]), {**EVENTS[event], **watched})}
    assert filing == {"push of a merge into main", "push of a release merge into main", "nightly schedule"}, filing


def test_the_release_trigger_and_gate_are_as_they_were() -> None:
    """The move asks nothing of release.yml: it hears CI's completed runs on
    main, and its gate admits a dispatch and CI's successful push run of
    this repository on main.  Pinned as text, so an edit to either is a
    deliberate one; tests/test_await_ci.py evaluates the gate over every
    run it can hear."""
    release = _load(RELEASE)
    assert _triggers(release)["workflow_run"] == {
        "workflows": ["CI"], "types": ["completed"], "branches": ["main"],
    }
    assert release["jobs"]["ci"]["if"] == (
        "github.event_name == 'workflow_dispatch'"
        " || (github.event.workflow_run.conclusion == 'success'"
        " && github.event.workflow_run.event == 'push'"
        " && github.event.workflow_run.head_branch == 'main'"
        " && github.event.workflow_run.head_repository.full_name == github.repository)"
    )
    assert _load(CI)["name"] == "CI"


# ---------------------------------------------------------------------------
# The images: pinned for gating, latest for watching
# ---------------------------------------------------------------------------


def test_every_job_but_the_watch_job_runs_on_a_pinned_image() -> None:
    """Every workflow's every job, every cell of a matrix job's, names an
    explicit image; a call runs the called workflow's jobs, which the loop
    reads there."""
    for path in sorted(WORKFLOWS.glob("*.yml")):
        for job_id, job in _load(path)["jobs"].items():
            if "uses" in job or (path.name, job_id) == ("ci.yml", "watch"):
                continue
            for runner in _runners(job):
                assert runner in PINNED, (path.name, job_id, runner)


def test_no_running_job_of_a_push_or_pull_request_takes_an_image_outside_the_pinned() -> None:
    """The merge path's events, the required checks among their jobs: under
    each, every job that runs takes a pinned image on every cell."""
    jobs = _load(CI)["jobs"]
    for event in GATING:
        for job_id, job in jobs.items():
            if _runs(job, event):
                for runner in _runners(job):
                    assert runner in PINNED, (event, job_id, runner)


def test_the_watched_images_run_on_the_nightly_alone_and_block_nothing() -> None:
    """The watch job's cells are the floating labels and the newest release
    image no pinned cell runs, at Python 3.12; it runs on the nightly run
    alone, and each cell may fail without failing the run."""
    job = _load(CI)["jobs"]["watch"]
    assert set(_runners(job)) == WATCHED and len(_runners(job)) == len(WATCHED)
    assert {cell["matrix.python-version"] for cell in _matrix_cells(job)} == {"3.12"}
    assert not WATCHED & PINNED
    assert {event for event in EVENTS if _runs(job, event)} == set(NIGHTLY_EVENTS)
    assert job["continue-on-error"] is True


def test_the_watched_labels_appear_in_no_other_job() -> None:
    """A watched label in any other job's runner or matrix, in any workflow,
    would run it where the watch job's condition does not hold."""
    for path in sorted(WORKFLOWS.glob("*.yml")):
        for job_id, job in _load(path)["jobs"].items():
            if (path.name, job_id) == ("ci.yml", "watch"):
                continue
            text = yaml.safe_dump({key: job.get(key) for key in ("runs-on", "strategy")})
            for label in sorted(WATCHED):
                assert label not in text, (path.name, job_id, label)


def test_the_watch_cells_run_what_the_test_cells_run() -> None:
    """The same steps (the image record among them), runner, permissions
    and dependency as the full matrix's, so a watched cell's red is the
    image's, not a step of its own."""
    jobs = _load(CI)["jobs"]
    assert jobs["watch"]["steps"] == jobs["test"]["steps"]
    for key in ("runs-on", "permissions", "needs"):
        assert jobs["watch"][key] == jobs["test"][key], key


def test_every_cell_records_the_image_it_ran_on() -> None:
    """A label names an image only until GitHub moves it, so a cell's first
    steps keep the image its runner booted, by `ImageOS` and `ImageVersion`,
    in a record named for the cell, and matrix-gate waits for every cell
    whose record matrix-issue reads.  The upload fails soft: the record is
    a diagnostic, and an artifact service's error on a version-raising pull
    request would otherwise fail a cell matrix-gate reads."""
    jobs = _load(CI)["jobs"]
    record, keep = jobs["test"]["steps"][:2]
    assert record["name"] == "Record the runner image"
    assert "$ImageOS" in record["run"] and "$ImageVersion" in record["run"]
    assert keep["uses"].startswith("actions/upload-artifact@")
    assert keep["with"]["name"] == "runner-image-${{ github.job }}-${{ matrix.os }}-${{ matrix.python-version }}"
    assert keep["with"]["overwrite"] is True
    assert keep["continue-on-error"] is True
    assert {"test", "watch"} <= set(jobs["matrix-gate"]["needs"])
