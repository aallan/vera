"""A failed cell of the full test matrix files an issue (ci.yml `matrix-issue`).

On the push and nightly runs, where no pull request's checks page shows the
failure, the `matrix-issue` job files one issue per workflow and branch, or
comments on it when it is already open: the `actions/github-script` pattern
of `nightly-stress.yml`, deduplicated on the issue's title and labelled
`bug` and `ci`.  The cells it names are the ones `matrix-gate` read as
failed from the run's job listing, handed over as the gate's `failed`
output (scripts/matrix_gate.py), so the job lists no jobs of its own.  The
script is run here under Node with a recording stand-in for the GitHub
client, case by case: the first failure files the issue, a repeat comments
on the open one, a pull request or another issue with the title is not it,
the branch is in the title, a missing label is created, and the cells that
failed are named, or the run is pointed to when the gate named none.  The
job's condition is evaluated as well: it files on a push or nightly run
whose matrix failed, or where the gate's listing shows a failed cell that
the matrix's result does not (#1659), and on nothing else.
"""

from __future__ import annotations

import json
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
# client that records each call, the run's context, and `core`.  The script
# runs as the body of an async function of those three names, as the action
# runs it, with the step's `FAILED` variable set as the case says.  The
# client has no `actions` API: a script that lists the run's jobs fails.
_HARNESS = r"""
const fs = require("fs");
const [scriptPath, casePath] = process.argv.slice(2);
const script = fs.readFileSync(scriptPath, "utf8");
const c = JSON.parse(fs.readFileSync(casePath, "utf8"));
if (c.failed === null) delete process.env.FAILED; else process.env.FAILED = c.failed;
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
  workflow: "CI", ref: c.ref, sha: "0123456789abcdef0123456789abcdef01234567",
  runId: 4242, serverUrl: "https://github.com", eventName: c.event,
  repo: { owner: "aallan", repo: "vera" },
};
const core = {
  info: (m) => record("info", m), warning: (m) => record("warning", m),
  setFailed: (m) => record("setFailed", m),
};
const AsyncFunction = Object.getPrototypeOf(async function () {}).constructor;
new AsyncFunction("github", "context", "core", script)(github, context, core)
  .then(() => process.stdout.write(JSON.stringify(calls)))
  .catch((e) => { process.stderr.write(String(e && e.stack || e)); process.exit(1); });
"""

# What matrix-gate hands on for a run whose two cells failed.
_FAILED = json.dumps(["test (windows-latest, 3.13)", "test (macos-15, 3.11)"])


def _issue(number: int, title: str, **extra: Any) -> dict[str, Any]:
    return {"number": number, "title": title, **extra}


def _file(
    tmp_path: Path, *, open_items: list[dict[str, Any]] | None = None, labels: tuple[str, ...] = ("bug", "ci"),
    ref: str = "refs/heads/main", event: str = "push", failed: str | None = _FAILED,
) -> list[dict[str, Any]]:
    assert NODE is not None
    (tmp_path / "harness.js").write_text(_HARNESS, encoding="utf-8")
    (tmp_path / "script.js").write_text(_script(), encoding="utf-8")
    (tmp_path / "case.json").write_text(json.dumps({
        "open": open_items or [], "labels": list(labels), "ref": ref, "event": event, "failed": failed,
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

    def test_the_nightly_run_says_so(self, tmp_path: Path) -> None:
        nightly = _named(_file(tmp_path, event="schedule"), "create")[0]["body"]
        push = _named(_file(tmp_path, event="push"), "create")[0]["body"]
        assert "nightly" in nightly
        assert "nightly" not in push


@pytest.mark.parametrize("event", ["push", "schedule", "pull_request"])
@pytest.mark.parametrize("result", ["success", "failure", "cancelled", "skipped"])
@pytest.mark.parametrize("failed", ["", '["test (macos-15, 3.11)"]'])
def test_it_files_where_a_cell_failed_on_a_push_or_nightly_run(event: str, result: str, failed: str) -> None:
    """A failed matrix files, and so does a failed cell the gate read where
    the matrix's result is `success`: one of two failed cells re-run on its
    own (#1659)."""
    from tests.test_gate_placement import evaluate

    job = _job()
    files = bool(evaluate(str(job["if"]), {
        "github.event_name": event, "needs.test.result": result,
        "needs.matrix-gate.outputs.failed": failed,
    }))
    assert files is (event in ("push", "schedule") and (result == "failure" or failed != ""))


def test_the_failed_cells_are_the_gate_s() -> None:
    """The job waits for the matrix and the gate, takes the gate's `failed`
    output as the script's `FAILED`, and lists no jobs of its own: it can
    write issues and read nothing of the run."""
    job = _job()
    needs = job["needs"]
    assert {"test", "matrix-gate"} <= set([needs] if isinstance(needs, str) else needs), needs
    assert job["permissions"] == {"issues": "write"}
    assert _step()["env"] == {"FAILED": "${{ needs.matrix-gate.outputs.failed }}"}
    assert "listJobsForWorkflowRun" not in _script()
