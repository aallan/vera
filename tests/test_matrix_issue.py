"""A failed cell of the full test matrix files an issue (ci.yml `matrix-issue`).

On the push and nightly runs, where no pull request's checks page shows the
failure, the `matrix-issue` job files one issue per workflow and branch, or
comments on it when it is already open: the `actions/github-script` pattern
of `nightly-stress.yml`, deduplicated on the issue's title and labelled
`bug` and `ci`.  The cells it names are the ones `matrix-gate` read as
failed from the run's job listing, handed over as the gate's `failed`
output, and on the nightly run the watched images' cells the gate read as
failed, its `watched` output (scripts/matrix_gate.py), so the job lists no
jobs of its own.  Beside each cell it names the image the cell's runner
booted, from the record the cell's first step keeps (`ImageOS` and
`ImageVersion`, a line each), so the issue says which build broke.  The
nightly run is nightly-matrix.yml's call of ci.yml, whose workflow name,
`Nightly matrix`, is in the issue's title.  The script is run here under
Node with a recording stand-in for the GitHub client, case by case: the
first failure files the issue, a repeat comments on the open one, a pull
request or another issue with the title is not it, the branch is in the
title, a missing label is created, the cells that failed are named with
their images, or the run is pointed to when the gate named none, and a
night on which a watched image alone failed says so.  The job's condition
is evaluated as well: it files on a push or scheduled nightly run whose
matrix failed, or where the gate's listing shows a failed cell that the
matrix's result does not (#1659), or a failed watched cell, and on nothing
else.
"""

from __future__ import annotations

import json
import os
import shutil
import subprocess
from pathlib import Path
from typing import Any

import pytest
import yaml

ROOT = Path(__file__).resolve().parent.parent
CI = ROOT / ".github" / "workflows" / "ci.yml"
NODE = shutil.which("node")

TITLE = "CI: full test matrix failing on main"
NIGHTLY_TITLE = "Nightly matrix: full test matrix failing on main"
RUN_URL = "https://github.com/aallan/vera/actions/runs/4242"


def _job() -> dict[str, Any]:
    return dict(yaml.safe_load(CI.read_text(encoding="utf-8"))["jobs"]["matrix-issue"])


def _step() -> dict[str, Any]:
    steps = [
        step for step in _job()["steps"]
        if str(step.get("uses", "")).startswith("actions/github-script@")
    ]
    assert len(steps) == 1, _job()["steps"]
    return dict(steps[0])


def _script() -> str:
    return str(_step()["with"]["script"])


# The stand-in for what actions/github-script hands a script: an Octokit
# client that records each call, the run's context, `core` and `require`.
# The script runs as the body of an async function of those four names, as
# the action runs it, with the step's variables set as the case says.  The
# client has no `actions` API: a script that lists the run's jobs fails.
_HARNESS = r"""
const fs = require("fs");
const [scriptPath, casePath] = process.argv.slice(2);
const script = fs.readFileSync(scriptPath, "utf8");
const c = JSON.parse(fs.readFileSync(casePath, "utf8"));
for (const [name, value] of Object.entries(c.env)) {
  if (value === null) delete process.env[name]; else process.env[name] = value;
}
const calls = [];
const labels = new Set(c.labels);
const record = (name, params) => calls.push({ name, params });
const github = {
  rest: {
    issues: {
      listForRepo: async (p) => { record("listForRepo", p); return { data: c.open }; },
      getLabel: async (p) => {
        record("getLabel", p);
        if (!labels.has(p.name)) throw Object.assign(new Error("Not Found"), { status: 404 });
        return { data: { name: p.name } };
      },
      createLabel: async (p) => { record("createLabel", p); labels.add(p.name); return { data: p }; },
      create: async (p) => { record("create", p); return { data: { number: 9001 } }; },
      createComment: async (p) => { record("createComment", p); return { data: { id: 1 } }; },
    },
  },
  // Octokit's paginate unwraps a list endpoint's array.
  paginate: async (method, params) => (await method(params)).data,
};
const context = {
  workflow: c.workflow, ref: c.ref, sha: "0123456789abcdef0123456789abcdef01234567",
  runId: 4242, serverUrl: "https://github.com", eventName: c.event,
  repo: { owner: "aallan", repo: "vera" },
};
const core = {
  info: (m) => record("info", m), warning: (m) => record("warning", m),
  setFailed: (m) => record("setFailed", m),
};
const AsyncFunction = Object.getPrototypeOf(async function () {}).constructor;
new AsyncFunction("github", "context", "core", "require", script)(github, context, core, require)
  .then(() => process.stdout.write(JSON.stringify(calls)))
  .catch((e) => { process.stderr.write(String(e && e.stack || e)); process.exit(1); });
"""

# What matrix-gate hands on for a run whose two cells failed.
_FAILED = json.dumps(["test (windows-latest, 3.13)", "test (macos-15, 3.11)"])


def _issue(number: int, title: str, **extra: Any) -> dict[str, Any]:
    return {"number": number, "title": title, **extra}


def _file(
    tmp_path: Path, *, open_items: list[dict[str, Any]] | None = None, labels: tuple[str, ...] = ("bug", "ci"),
    ref: str = "refs/heads/main", event: str = "push", workflow: str = "CI",
    failed: str | None = _FAILED, watched: str | None = None, test_result: str = "failure",
    records: dict[str, str] | None = None, images: Path | None = None,
) -> list[dict[str, Any]]:
    """The calls the script makes for one case.  `records` are the image
    records the cells left, each file's text by its name; `images` is the
    directory the step names instead, which may not exist."""
    assert NODE is not None
    (tmp_path / "harness.js").write_text(_HARNESS, encoding="utf-8")
    (tmp_path / "script.js").write_text(_script(), encoding="utf-8")
    if records is not None:
        images = tmp_path / "runner-image"
        images.mkdir()
        for name, text in records.items():
            (images / name).write_text(text, encoding="utf-8")
    env = {
        "FAILED": failed, "WATCHED": watched, "TEST_RESULT": test_result,
        "IMAGES": None if images is None else str(images),
    }
    (tmp_path / "case.json").write_text(json.dumps({
        "open": open_items or [], "labels": list(labels), "ref": ref, "event": event,
        "workflow": workflow, "env": env,
    }), encoding="utf-8")
    result = subprocess.run(
        [NODE, str(tmp_path / "harness.js"), str(tmp_path / "script.js"), str(tmp_path / "case.json")],
        capture_output=True, text=True, encoding="utf-8", check=False,
    )
    assert result.returncode == 0, result.stderr
    calls: list[dict[str, Any]] = json.loads(result.stdout)
    return calls


def _named(calls: list[dict[str, Any]], name: str) -> list[dict[str, Any]]:
    return [call["params"] for call in calls if call["name"] == name]


needs_node = pytest.mark.skipif(NODE is None, reason="the github-script runs under Node.js, which is not installed")


@needs_node
class TestTheScript:
    def test_the_first_failure_files_the_issue(self, tmp_path: Path) -> None:
        calls = _file(tmp_path, open_items=[_issue(5, "Nightly stress regression on main (tracking)")])
        (created,) = _named(calls, "create")
        assert created["title"] == TITLE
        assert sorted(created["labels"]) == ["bug", "ci"]
        assert (created["owner"], created["repo"]) == ("aallan", "vera")
        assert _named(calls, "createComment") == []
        body = created["body"]
        assert RUN_URL in body
        assert "0123456" in body
        assert "Failed cells: `test (macos-15, 3.11)`, `test (windows-latest, 3.13)`." in body

    def test_a_repeat_comments_on_the_open_issue(self, tmp_path: Path) -> None:
        calls = _file(tmp_path, open_items=[_issue(5, "Something else"), _issue(77, TITLE)])
        assert _named(calls, "create") == []
        (comment,) = _named(calls, "createComment")
        assert comment["issue_number"] == 77
        assert RUN_URL in comment["body"]

    def test_a_pull_request_with_the_title_is_not_the_issue(self, tmp_path: Path) -> None:
        calls = _file(tmp_path, open_items=[_issue(78, TITLE, pull_request={"url": "x"})])
        assert _named(calls, "createComment") == []
        assert len(_named(calls, "create")) == 1

    def test_the_listing_asks_for_every_open_issue(self, tmp_path: Path) -> None:
        """Dedupe is on the title alone, so the search cannot be narrowed by
        a label someone may have taken off the issue."""
        calls = _file(tmp_path)
        (listing,) = _named(calls, "listForRepo")
        assert listing["state"] == "open"
        assert "labels" not in listing

    def test_the_branch_is_in_the_title(self, tmp_path: Path) -> None:
        calls = _file(tmp_path, ref="refs/heads/release/v9", open_items=[_issue(77, TITLE)])
        assert _named(calls, "createComment") == []
        (created,) = _named(calls, "create")
        assert created["title"] == "CI: full test matrix failing on release/v9"

    def test_a_missing_label_is_created(self, tmp_path: Path) -> None:
        calls = _file(tmp_path, labels=("bug",))
        assert [label["name"] for label in _named(calls, "createLabel")] == ["ci"]
        assert len(_named(calls, "create")) == 1

    @pytest.mark.parametrize("failed", [None, "", "not json", '{"cells": 1}', "[]"])
    def test_no_cell_from_the_gate_still_files(self, tmp_path: Path, failed: str | None) -> None:
        """The gate names no cell where it could not read the listing, and
        the matrix's own result filed: the body points to the run."""
        calls = _file(tmp_path, failed=failed)
        (created,) = _named(calls, "create")
        assert "The run's page lists the failed cells." in created["body"]
        assert RUN_URL in created["body"]
        assert "Failed cells" not in created["body"]
        assert created["body"].startswith("The full test matrix failed")

    def test_the_nightly_run_says_so(self, tmp_path: Path) -> None:
        nightly = _named(_file(tmp_path, event="schedule"), "create")[0]["body"]
        push = _named(_file(tmp_path, event="push"), "create")[0]["body"]
        assert "nightly" in nightly
        assert "nightly" not in push

    def test_the_nightly_run_files_under_its_own_workflow_s_name(self, tmp_path: Path) -> None:
        """A called workflow's run carries its caller's name, so the nightly
        run's issue is Nightly matrix's, and a repeat comments on it."""
        calls = _file(tmp_path, event="schedule", workflow="Nightly matrix")
        (created,) = _named(calls, "create")
        assert created["title"] == NIGHTLY_TITLE
        assert "in the nightly run of Nightly matrix on `main`" in created["body"]
        repeat = tmp_path / "repeat"
        repeat.mkdir()
        again = _file(repeat, event="schedule", workflow="Nightly matrix",
                      open_items=[_issue(77, TITLE), _issue(78, NIGHTLY_TITLE)])
        assert [comment["issue_number"] for comment in _named(again, "createComment")] == [78]

    def test_each_cell_is_named_with_the_image_it_ran_on(self, tmp_path: Path) -> None:
        """A cell's record names its image; a cell with no record is named
        alone, and a line that is no record names nothing."""
        calls = _file(tmp_path, records={
            "test-windows-latest-3.13.tsv": "test (windows-latest, 3.13)\twin25\t20261026.1.0\n",
            "test-macos-26-3.12.tsv": "test (macos-26, 3.12)\tmacos26\t20261020.3\n",
            "stray.tsv": "test (macos-15, 3.11)\tmacos15\n",
        })
        (created,) = _named(calls, "create")
        assert ("Failed cells: `test (macos-15, 3.11)`, `test (windows-latest, 3.13)` on win25 20261026.1.0."
                in created["body"]), created["body"]

    @pytest.mark.parametrize("missing", ["no directory", "no variable"])
    def test_no_record_still_names_every_cell(self, tmp_path: Path, missing: str) -> None:
        """The records come from the run's artifacts, which a download that
        failed leaves absent: the cells are named without an image."""
        images = tmp_path / "absent" if missing == "no directory" else None
        calls = _file(tmp_path, images=images)
        (created,) = _named(calls, "create")
        assert "Failed cells: `test (macos-15, 3.11)`, `test (windows-latest, 3.13)`." in created["body"]
        assert any("no runner image records" in str(message) for message in _named(calls, "info"))

    def test_a_watched_image_alone_files_and_says_so(self, tmp_path: Path) -> None:
        """A night whose full matrix passed and one of whose watched cells
        failed: the issue says a watched image failed, names the cell and
        its image, and blocks nothing."""
        calls = _file(
            tmp_path, event="schedule", workflow="Nightly matrix", failed=None, test_result="success",
            watched='["watch (ubuntu-latest, 3.12)"]',
            records={"watch-ubuntu-latest-3.12.tsv": "watch (ubuntu-latest, 3.12)\tubuntu26\t20261026.2\n"},
        )
        (created,) = _named(calls, "create")
        body = created["body"]
        assert created["title"] == NIGHTLY_TITLE
        assert body.startswith("A watched runner image failed in the nightly run of Nightly matrix"), body
        assert ("Failed watched cells, which block nothing: `watch (ubuntu-latest, 3.12)` on ubuntu26 20261026.2."
                in body), body
        assert "Failed cells:" not in body
        assert "The run's page lists" not in body

    def test_a_failed_cell_beside_a_failed_watched_cell_names_both(self, tmp_path: Path) -> None:
        calls = _file(tmp_path, event="schedule", workflow="Nightly matrix",
                      watched='["watch (windows-latest, 3.12)"]')
        body = _named(calls, "create")[0]["body"]
        assert body.startswith("The full test matrix failed"), body
        assert "Failed cells: `test (macos-15, 3.11)`, `test (windows-latest, 3.13)`." in body
        assert "Failed watched cells, which block nothing: `watch (windows-latest, 3.12)`." in body

    def test_a_failed_matrix_the_gate_named_no_cell_of_leads(self, tmp_path: Path) -> None:
        """The matrix failed and the gate named no cell of it (a cancelled
        cell, say) while a watched cell failed: the matrix's failure leads,
        and the run's page is where its cells are."""
        calls = _file(tmp_path, event="schedule", workflow="Nightly matrix", failed=None,
                      test_result="failure", watched='["watch (macos-latest, 3.12)"]')
        body = _named(calls, "create")[0]["body"]
        assert body.startswith("The full test matrix failed"), body
        assert "The run's page lists the failed cells." in body
        assert "Failed watched cells, which block nothing: `watch (macos-latest, 3.12)`." in body


@pytest.mark.parametrize("event", ["push", "schedule", "pull_request", "workflow_dispatch"])
@pytest.mark.parametrize("result", ["success", "failure", "cancelled", "skipped"])
@pytest.mark.parametrize("failed", ["", '["test (macos-15, 3.11)"]'])
@pytest.mark.parametrize("watched", ["", '["watch (ubuntu-latest, 3.12)"]'])
def test_it_files_where_a_cell_failed_on_a_push_or_nightly_run(
    event: str, result: str, failed: str, watched: str,
) -> None:
    """A failed matrix files, and so does a failed cell the gate read where
    the matrix's result is `success`: one of two failed cells re-run on its
    own (#1659), and a failed watched cell.  The nightly run is a call of
    ci.yml, whose event is its caller's: the schedule's files, and a
    dispatched run, watched by whoever started it, files nothing."""
    from tests.test_gate_placement import evaluate

    job = _job()
    files = bool(evaluate(str(job["if"]), {
        "github.event_name": event, "needs.test.result": result,
        "needs.matrix-gate.outputs.failed": failed, "needs.matrix-gate.outputs.watched": watched,
    }))
    assert files is (event in ("push", "schedule") and (result == "failure" or failed != "" or watched != ""))


def test_the_failed_cells_are_the_gate_s() -> None:
    """The job waits for the matrix and the gate, takes the gate's `failed`
    and `watched` outputs and the matrix's result as the script's variables,
    and lists no jobs of its own: it can write issues, and reads nothing of
    the run but the image records its cells keep, which the download
    fetches with the run's own token, failing soft."""
    job = _job()
    needs = job["needs"]
    assert {"test", "matrix-gate"} <= set([needs] if isinstance(needs, str) else needs), needs
    assert job["permissions"] == {"issues": "write"}
    assert _step()["env"] == {
        "FAILED": "${{ needs.matrix-gate.outputs.failed }}",
        "WATCHED": "${{ needs.matrix-gate.outputs.watched }}",
        "TEST_RESULT": "${{ needs.test.result }}",
        "IMAGES": "${{ runner.temp }}/runner-image",
    }
    assert "listJobsForWorkflowRun" not in _script()
    (download,) = [step for step in job["steps"] if str(step.get("uses", "")).startswith("actions/download-artifact@")]
    assert download["with"] == {
        "pattern": "runner-image-*", "path": "${{ runner.temp }}/runner-image", "merge-multiple": True,
    }
    assert download["continue-on-error"] is True
    assert job["steps"].index(download) < job["steps"].index(_step())


@needs_node
@pytest.mark.skipif(os.name == "nt" or shutil.which("bash") is None,
                    reason="the step is a bash script; the runners run it under bash")
@pytest.mark.parametrize(("job_id", "os_label"), [("test", "windows-2025-vs2026"), ("watch", "ubuntu-latest")])
def test_the_record_a_cell_keeps_is_the_one_the_issue_reads(tmp_path: Path, job_id: str, os_label: str) -> None:
    """The record is a contract between two steps: a cell's first step
    writes it, and matrix-issue's script reads it.  The step runs here as
    the runner runs a `shell: bash` step, with the environment a runner
    gives it, and the issue the script files over its record names the
    cell's image, which the job's summary shows too."""
    from tests.test_gate_placement import render

    step = yaml.safe_load(CI.read_text(encoding="utf-8"))["jobs"][job_id]["steps"][0]
    assert step["name"] == "Record the runner image" and step["shell"] == "bash"
    cell = {"github.job": job_id, "matrix.os": os_label, "matrix.python-version": "3.12"}
    temp = tmp_path / "runner-temp"
    temp.mkdir()
    summary = tmp_path / "summary.md"
    script = tmp_path / "step.sh"
    script.write_text(str(step["run"]), encoding="utf-8")
    env = {name: value for name, value in os.environ.items() if name not in ("BASH_ENV", "ENV")}
    env.update({name: render(str(value), cell) for name, value in step["env"].items()})
    env.update({"ImageOS": "image26", "ImageVersion": "20261026.7", "RUNNER_TEMP": str(temp),
                "GITHUB_STEP_SUMMARY": str(summary)})
    proc = subprocess.run(["bash", "--noprofile", "--norc", "-eo", "pipefail", str(script)],
                          cwd=tmp_path, env=env, check=False, capture_output=True, text=True, encoding="utf-8")
    assert proc.returncode == 0, proc.stderr
    assert "Runner image: image26 20261026.7" in proc.stdout
    assert summary.read_text(encoding="utf-8") == "Runner image: image26 20261026.7\n"
    name = f"{job_id} ({os_label}, 3.12)"
    issue = tmp_path / "issue"
    issue.mkdir()
    kind = "failed" if job_id == "test" else "watched"
    calls = _file(issue, event="schedule", workflow="Nightly matrix", test_result="success",
                  failed=json.dumps([name]) if kind == "failed" else None,
                  watched=json.dumps([name]) if kind == "watched" else None,
                  images=temp / "runner-image")
    body = _named(calls, "create")[0]["body"]
    assert f"`{name}` on image26 20261026.7" in body, body
