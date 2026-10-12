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
passing it.  The verdicts are pinned over every combination of the three, the
script's command line reads them from its environment, and the job hands it
exactly those three values.
"""

from __future__ import annotations

import importlib.util
import itertools
from pathlib import Path
from typing import Any

import pytest
import yaml

ROOT = Path(__file__).resolve().parent.parent
SCRIPT = ROOT / "scripts" / "matrix_gate.py"
CI = ROOT / ".github" / "workflows" / "ci.yml"


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
    monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str],
    plan: str, release: str, matrix: str, status: int,
) -> None:
    monkeypatch.setenv("PLAN_RESULT", plan)
    monkeypatch.setenv("RELEASE", release)
    monkeypatch.setenv("TEST_RESULT", matrix)
    assert mg.main() == status
    out = capsys.readouterr().out
    assert out.strip(), "the verdict is printed for the log"
    if status:
        assert out.startswith("::error::"), out


def test_an_absent_variable_fails(monkeypatch: pytest.MonkeyPatch) -> None:
    for name in ("PLAN_RESULT", "RELEASE", "TEST_RESULT"):
        monkeypatch.delenv(name, raising=False)
    assert mg.main() == 1


def test_the_job_hands_the_script_the_three_results() -> None:
    """The job runs after the plan and the matrix whatever happened to them
    (`always()`), and passes the script their results and the plan's
    answer under the names it reads."""
    job = yaml.safe_load(CI.read_text(encoding="utf-8"))["jobs"]["matrix-gate"]
    needs = job["needs"]
    assert {"plan", "test"} <= set([needs] if isinstance(needs, str) else needs), needs
    assert str(job["if"]).replace("${{", "").replace("}}", "").strip() == "always()", job["if"]
    steps = [step for step in job["steps"] if "scripts/matrix_gate.py" in str(step.get("run", ""))]
    assert len(steps) == 1, job["steps"]
    assert steps[0]["env"] == {
        "PLAN_RESULT": "${{ needs.plan.result }}",
        "RELEASE": "${{ needs.plan.outputs.release }}",
        "TEST_RESULT": "${{ needs.test.result }}",
    }
