"""scripts/ci_changes.py, and the path filter ci.yml builds on it.

On a pull request the plan job asks scripts/ci_changes.py whether every
file the pull request changes is one no filtered job reads: one of the VS
Code extension's own files, which vscode-extension.yml builds and tests.
On ``inert=true`` the suite's shards, typecheck, eager-gc, browser-parity,
wheel-preflight, dependency-audit, package-distribution and sbom stand
down; plan, lint, security and matrix-gate run on every pull request.

Branch protection requires its checks by name, and a required check no job
reports blocks the merge.  A job its own `if:` skips reports success under
its name, so a filtered job with no matrix is skipped at the job level.  A
matrix job its `if:` skips reports one check under its unexpanded name, so
the shard job's cells, five required checks, run and skip their steps
instead.  These tests read the workflow as data, through the expression
evaluator tests/test_gate_placement.py tests first, and the classifier as
code, over the tracked tree and a scratch repository.
"""

from __future__ import annotations

import importlib.util
import os
import re
import subprocess
import sys
from pathlib import Path
from typing import Any

import pytest
import yaml

from tests.test_gate_placement import EVENTS, _matrix_cells, _runs, render

ROOT = Path(__file__).resolve().parent.parent
CI = ROOT / ".github" / "workflows" / "ci.yml"
_SCRIPT = ROOT / "scripts" / "ci_changes.py"


def _load(path: Path, name: str) -> Any:
    spec = importlib.util.spec_from_file_location(name, path)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


cc = _load(_SCRIPT, "ci_changes")


def _workflow() -> dict[Any, Any]:
    return dict(yaml.safe_load(CI.read_text(encoding="utf-8")))


def _scrubbed_env(**extra: str) -> dict[str, str]:
    env = {k: v for k, v in os.environ.items() if not k.startswith("GIT_")}
    env.update(extra)
    return env


def _tracked(prefix: str) -> list[str]:
    listing = subprocess.run(
        ["git", "ls-files", "-z", "--", prefix], cwd=ROOT, capture_output=True,
        check=True, env=_scrubbed_env())
    return sorted(p for p in listing.stdout.decode("utf-8").split("\0") if p)


# The checks branch protection requires that ci.yml reports (the other
# required check, `analyze`, is codeql.yml's), as the repository's settings
# list them on 2026-10-21.  The maintainer edits that list by hand, so a job
# rename here would leave a required check no job reports.
REQUIRED = (
    "typecheck", "lint", "wheel-preflight", "browser-parity", "security", "eager-gc",
    "test (ubuntu-latest, 3.12, shard 1/3)", "test (ubuntu-latest, 3.12, shard 2/3)",
    "test (ubuntu-latest, 3.12, shard 3/3)", "test (windows-latest, 3.12, shard 1/2)",
    "test (windows-latest, 3.12, shard 2/2)", "matrix-gate",
)

# The jobs that stand down on a pull request whose every file is inert, at
# the job level, and the one that skips its steps, cell by cell.
SKIPPED_JOBS = (
    "typecheck", "eager-gc", "browser-parity", "wheel-preflight",
    "dependency-audit", "package-distribution", "sbom",
)
STEP_SKIPPED_JOBS = ("shard",)
# The jobs that run on every pull request, whatever it changes.
ALWAYS = ("plan", "lint", "security", "matrix-gate")

INERT_EVENT = "pull request that changes only the VS Code extension's own files"
ORDINARY_EVENT = "pull request into main"


# ---------------------------------------------------------------------------
# The classifier
# ---------------------------------------------------------------------------


class TestTheClassifier:
    @pytest.mark.parametrize(("path", "inert"), [
        # What a Dependabot npm bump changes.
        ("editors/vscode/package.json", True),
        ("editors/vscode/package-lock.json", True),
        # The extension's code, assets and ignore files.
        ("editors/vscode/extension.js", True),
        ("editors/vscode/esbuild.js", True),
        ("editors/vscode/test/check-package-contents.test.js", True),
        ("editors/vscode/images/vera-icon.png", True),
        ("editors/vscode/language-configuration.json", True),
        ("editors/vscode/.vscodeignore", True),
        ("editors/vscode/.gitignore", True),
        ("editors/vscode/LICENSE", True),
        # A document: the doc-example gate's coverage rule reads every tracked
        # document, so one could gain a Vera block.
        ("editors/vscode/README.md", False),
        ("editors/vscode/CHANGELOG.md", False),
        ("editors/vscode/notes.txt", False),
        ("editors/vscode/page.html", False),
        # A grammar, by its directory or its name: scripts/render_lists.py
        # renders the effect list into the one there and discovers any other.
        ("editors/vscode/syntaxes/vera.tmLanguage.json", False),
        ("editors/vscode/syntaxes/other.json", False),
        ("editors/vscode/grammars/syntax/vera.json", False),
        ("editors/vscode/vera.tmLanguage.json", False),
        ("editors/vscode/queries/highlights.scm", False),
        ("editors/vscode/Vera.sublime-syntax", False),
        # A kind the tables do not name: source a gate or a hook reads.
        ("editors/vscode/helper.py", False),
        ("editors/vscode/sample.vera", False),
        ("editors/vscode/config.yml", False),
        ("editors/vscode/src/extension.ts", False),
        # Anywhere else.
        ("editors/vim-veralang/ftdetect/veralang.vim", False),
        ("editors/README.md", False),
        ("vera/cli.py", False),
        (".github/workflows/vscode-extension.yml", False),
        ("Editors/vscode/package.json", False),
        ("editors/vscode", False),
        ("editors/vscodeplus/package.json", False),
    ])
    def test_a_path_is_inert_only_as_one_of_the_extensions_own_files(
        self, path: str, inert: bool,
    ) -> None:
        assert cc.is_inert(path) is inert

    def test_every_path_must_be_inert(self) -> None:
        assert cc.inert(["editors/vscode/package.json", "editors/vscode/package-lock.json"])
        assert not cc.inert(["editors/vscode/package.json", "vera/cli.py"])
        assert not cc.inert(["editors/vscode/package.json", "editors/vscode/README.md"])

    def test_a_diff_that_changes_nothing_is_not_inert(self) -> None:
        """An empty listing is as likely a failure to list as a change of
        nothing, so it runs every job."""
        assert not cc.inert([])

    def test_the_tracked_extension_splits_as_its_readers_require(self) -> None:
        tracked = _tracked("editors/vscode/")
        assert {p for p in tracked if not cc.is_inert(p)} == {
            "editors/vscode/CHANGELOG.md",
            "editors/vscode/README.md",
            "editors/vscode/syntaxes/vera.tmLanguage.json",
        }

    def test_the_tables_agree_with_the_gates_that_read_the_files(self) -> None:
        """The classifier runs in the plan job, before anything is
        installed, so it holds its own copy of the grammar gate's tables,
        which this holds to the gate, and names no document's suffix among
        the inert kinds."""
        render_lists = _load(ROOT / "scripts" / "render_lists.py", "ci_changes_render_lists")
        assert cc.GRAMMAR_DIRS == render_lists._GRAMMAR_DIRS
        assert cc.GRAMMAR_SUFFIXES == render_lists._GRAMMAR_SUFFIXES
        doc_examples = _load(ROOT / "scripts" / "check_doc_examples.py",
                             "ci_changes_check_doc_examples")
        documents = doc_examples.DOCUMENT_SUFFIXES
        assert not [s for s in cc.INERT_SUFFIXES if s.endswith(documents)]
        assert not [n for n in cc.INERT_NAMES if n.lower().endswith(documents)]
        assert not any(s.endswith(cc.GRAMMAR_SUFFIXES) for s in cc.INERT_SUFFIXES)

    def test_no_test_or_gate_reads_an_inert_file(self) -> None:
        """A tracked inert file no test, script, compiler module or hook
        names: the day one does, it stops being inert here first.  Three
        test files name `editors/vscode/package.json` as a path to classify,
        which reads nothing: this one, the changelog gate's and the gate
        placement test's."""
        inert = [p for p in _tracked("editors/vscode/") if cc.is_inert(p)]
        assert "editors/vscode/package.json" in inert
        readers = [
            *sorted((ROOT / "tests").rglob("*.py")), *sorted((ROOT / "scripts").glob("*.py")),
            *sorted((ROOT / "vera").rglob("*.py")), ROOT / ".pre-commit-config.yaml", CI,
        ]
        allowed = {
            (Path(__file__).resolve(), path) for path in inert
        } | {
            ((ROOT / "tests" / name).resolve(), "editors/vscode/package.json")
            for name in ("test_check_changelog_updated.py", "test_gate_placement.py")
        }
        named = [
            (reader.relative_to(ROOT).as_posix(), path)
            for reader in readers
            for path in inert
            if path in reader.read_text(encoding="utf-8")
            and (reader.resolve(), path) not in allowed
        ]
        assert named == []


# ---------------------------------------------------------------------------
# The command, against a scratch repository
# ---------------------------------------------------------------------------


def _git(repo: Path, *args: str) -> None:
    subprocess.run(
        ["git", "-C", str(repo), *args], check=True, capture_output=True,
        env=_scrubbed_env(GIT_AUTHOR_NAME="t", GIT_AUTHOR_EMAIL="t@example.invalid",
                          GIT_COMMITTER_NAME="t", GIT_COMMITTER_EMAIL="t@example.invalid"))


def _write(repo: Path, path: str, text: str) -> None:
    target = repo / path
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(text, encoding="utf-8")


@pytest.fixture
def repo(tmp_path: Path) -> Path:
    root = tmp_path / "repo"
    root.mkdir()
    _git(root, "init", "-q", "-b", "main")
    _write(root, "editors/vscode/package.json", "{}\n")
    _write(root, "editors/vscode/README.md", "# x\n")
    _write(root, "vera/cli.py", "x = 1\n")
    _git(root, "add", "-A")
    _git(root, "commit", "-q", "-m", "base")
    _git(root, "checkout", "-q", "-b", "head")
    return root


def _classify(repo: Path, monkeypatch: pytest.MonkeyPatch) -> subprocess.CompletedProcess[str]:
    """The command as the plan job runs it, with a hook's GIT_DIR pointing
    elsewhere: the repository is the working directory's."""
    env = _scrubbed_env(GIT_DIR=str(repo.parent / "nowhere" / ".git"))
    return subprocess.run(
        [sys.executable, str(_SCRIPT), "main", "head"], cwd=repo, env=env,
        capture_output=True, text=True, encoding="utf-8", check=False)


class TestTheCommand:
    def test_a_bump_of_the_extensions_dependencies_is_inert(
        self, repo: Path, monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        _write(repo, "editors/vscode/package.json", '{"version": "2"}\n')
        _write(repo, "editors/vscode/package-lock.json", "{}\n")
        _git(repo, "add", "-A")
        _git(repo, "commit", "-q", "-m", "bump")
        result = _classify(repo, monkeypatch)
        assert (result.returncode, result.stdout) == (0, "inert=true\n"), result.stderr

    def test_a_change_to_the_extensions_readme_is_not(
        self, repo: Path, monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        _write(repo, "editors/vscode/package.json", '{"version": "2"}\n')
        _write(repo, "editors/vscode/README.md", "# y\n")
        _git(repo, "add", "-A")
        _git(repo, "commit", "-q", "-m", "docs")
        result = _classify(repo, monkeypatch)
        assert (result.returncode, result.stdout) == (0, "inert=false\n"), result.stderr

    def test_a_rename_counts_its_old_name_too(
        self, repo: Path, monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        """`vera/cli.py` moved under the extension leaves the compiler
        without it: a change every job reads."""
        _git(repo, "mv", "vera/cli.py", "editors/vscode/cli.js")
        _git(repo, "commit", "-q", "-m", "move")
        result = _classify(repo, monkeypatch)
        assert (result.returncode, result.stdout) == (0, "inert=false\n"), result.stderr

    def test_a_commit_git_cannot_find_fails_the_step(
        self, repo: Path, monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        env = _scrubbed_env()
        result = subprocess.run(
            [sys.executable, str(_SCRIPT), "main", "no-such-commit"], cwd=repo, env=env,
            capture_output=True, text=True, encoding="utf-8", check=False)
        assert result.returncode != 0 and result.stdout == ""

    def test_it_takes_exactly_a_base_and_a_head(self, repo: Path) -> None:
        result = subprocess.run(
            [sys.executable, str(_SCRIPT), "main"], cwd=repo, env=_scrubbed_env(),
            capture_output=True, text=True, encoding="utf-8", check=False)
        assert result.returncode == 2 and result.stdout == ""


# ---------------------------------------------------------------------------
# The workflow
# ---------------------------------------------------------------------------


def _names(job: dict[str, Any], job_id: str) -> list[str]:
    """The check names a job reports when it runs: its `name:` rendered per
    matrix cell, or its id when it has no name."""
    name = str(job.get("name", job_id))
    if "strategy" not in job:
        return [name]
    return [render(name, cell) for cell in _matrix_cells(job)]


def _reported(workflow: dict[Any, Any], context: dict[str, object]) -> dict[str, str]:
    """The checks a run reports in `context`, each `runs` or `skipped`, a
    job's `needs` taken to have succeeded.  A job its `if:` skips reports
    success under its name; a matrix job its `if:` skips reports none of its
    cells' names."""
    out: dict[str, str] = {}
    for job_id, job in workflow["jobs"].items():
        runs = _runs(job, context, f"job {job_id}")
        if runs:
            out.update(dict.fromkeys(_names(job, job_id), "runs"))
        elif "strategy" not in job:
            out[str(job.get("name", job_id))] = "skipped"
    return out


def _steps_that_run(job: dict[str, Any], context: dict[str, object], job_id: str) -> list[str]:
    return [
        str(step.get("name") or step.get("uses"))
        for step in job.get("steps", [])
        if _runs(step, context, f"job {job_id}, step {step.get('name')!r}")
    ]


class TestThePlanJob:
    def test_it_asks_the_classifier_on_a_pull_request(self) -> None:
        plan = _workflow()["jobs"]["plan"]
        assert plan["outputs"]["inert"] == "${{ steps.inert.outputs.inert }}"
        (step,) = [s for s in plan["steps"] if s.get("id") == "inert"]
        assert step["if"] == "github.event_name == 'pull_request'"
        assert step["env"] == {
            "BASE_SHA": "${{ github.event.pull_request.base.sha }}",
            "HEAD_SHA": "${{ github.event.pull_request.head.sha }}",
        }
        assert step["run"].strip() == (
            'python scripts/ci_changes.py "$BASE_SHA" "$HEAD_SHA" >> "$GITHUB_OUTPUT"')

    def test_it_checks_out_the_history_the_diff_needs(self) -> None:
        plan = _workflow()["jobs"]["plan"]
        checkout = next(s for s in plan["steps"] if str(s.get("uses", "")).startswith("actions/checkout@"))
        assert checkout["with"]["fetch-depth"] == 0
        assert checkout["with"]["persist-credentials"] is False


class TestEveryRequiredCheckReports:
    """Branch protection reads the checks of a pull request, so the
    pull-request events are the ones whose every required check must
    report."""

    @pytest.mark.parametrize("event", sorted(
        e for e, context in EVENTS.items() if context["github.event_name"] == "pull_request"))
    def test_on_every_pull_request(self, event: str) -> None:
        reported = _reported(_workflow(), EVENTS[event])
        missing = [name for name in REQUIRED if name not in reported]
        assert missing == [], f"{event}: no job reports {missing}"

    def test_a_skipped_matrix_job_would_not(self) -> None:
        """The premise of the step-level filter, on a synthetic job: skipped
        at the job level, a matrix reports none of its cells' names."""
        job = {"name": "test (${{ matrix.os }})", "if": "x == 'y'",
               "strategy": {"matrix": {"os": ["a", "b"]}}, "steps": []}
        workflow = {"jobs": {"cells": job}}
        assert _reported(workflow, {"x": "y"}) == {"test (a)": "runs", "test (b)": "runs"}
        assert _reported(workflow, {"x": "z"}) == {}


class TestThePathFilter:
    def test_the_filtered_jobs_stand_down_on_an_inert_pull_request(self) -> None:
        workflow = _workflow()
        context = EVENTS[INERT_EVENT]
        reported = _reported(workflow, context)
        for job_id in SKIPPED_JOBS:
            job = workflow["jobs"][job_id]
            assert "strategy" not in job, job_id
            assert reported[str(job["name"])] == "skipped", job_id
        for job_id in STEP_SKIPPED_JOBS:
            job = workflow["jobs"][job_id]
            assert all(reported[name] == "runs" for name in _names(job, job_id)), job_id
            for cell in _matrix_cells(job):
                assert _steps_that_run(job, {**context, **cell}, job_id) == [], (job_id, cell)

    def test_the_rest_run_as_on_any_pull_request(self) -> None:
        workflow = _workflow()
        for job_id in ALWAYS:
            job = workflow["jobs"][job_id]
            for event in (INERT_EVENT, ORDINARY_EVENT):
                assert _runs(job, EVENTS[event], job_id), (job_id, event)
            assert (_steps_that_run(job, EVENTS[INERT_EVENT], job_id)
                    == _steps_that_run(job, EVENTS[ORDINARY_EVENT], job_id)), job_id

    def test_on_an_ordinary_pull_request_every_filtered_job_runs_every_step(self) -> None:
        workflow = _workflow()
        context = EVENTS[ORDINARY_EVENT]
        for job_id in (*SKIPPED_JOBS, *STEP_SKIPPED_JOBS):
            job = workflow["jobs"][job_id]
            cells = _matrix_cells(job) if "strategy" in job else [{}]
            for cell in cells:
                assert _runs(job, {**context, **cell}, job_id), job_id
                assert len(_steps_that_run(job, {**context, **cell}, job_id)) == len(job["steps"])

    def test_a_missing_answer_runs_everything(self) -> None:
        """The filter tests `!= 'true'`: on a push, the nightly run, or a
        plan that wrote no answer, the output is empty and every job runs."""
        workflow = _workflow()
        context = {**EVENTS[ORDINARY_EVENT], "needs.plan.outputs.inert": ""}
        for job_id in (*SKIPPED_JOBS, *STEP_SKIPPED_JOBS):
            job = workflow["jobs"][job_id]
            assert "plan" in (job["needs"] if isinstance(job["needs"], list) else [job["needs"]])
            cells = _matrix_cells(job) if "strategy" in job else [{}]
            for cell in cells:
                assert _runs(job, {**context, **cell}, job_id), job_id
                assert len(_steps_that_run(job, {**context, **cell}, job_id)) == len(job["steps"])

    def test_every_filter_reads_the_plan_jobs_answer_the_same_way(self) -> None:
        workflow = _workflow()
        condition = "needs.plan.outputs.inert != 'true'"
        for job_id in SKIPPED_JOBS:
            assert condition in str(workflow["jobs"][job_id]["if"]), job_id
        for job_id in STEP_SKIPPED_JOBS:
            for step in workflow["jobs"][job_id]["steps"]:
                assert condition in str(step["if"]), (job_id, step.get("name"))


# ---------------------------------------------------------------------------
# The rest of the workflow's shape
# ---------------------------------------------------------------------------


class TestTheWorkflow:
    def test_no_run_command_holds_an_expression(self) -> None:
        """Every context value reaches a shell through `env:`, where the
        shell reads it as data, never as the command's text."""
        found = [
            (job_id, step.get("name"))
            for job_id, job in _workflow()["jobs"].items()
            for step in job.get("steps", [])
            if "${{" in str(step.get("run", ""))
        ]
        assert found == []

    def test_the_coverage_floor_is_94(self) -> None:
        steps = _workflow()["jobs"]["coverage"]["steps"]
        (step,) = [s for s in steps if "--cov=vera" in str(s.get("run", ""))]
        assert re.search(r"--cov-fail-under=(\d+)\b", step["run"]).group(1) == "94"  # type: ignore[union-attr]

    def test_lint_leaves_the_suites_work_to_the_suite(self) -> None:
        """The examples' check and verify (tests/test_verifier_contracts.py,
        tests/test_pipeline.py), every document's gate
        (tests/test_check_doc_examples.py) and the examples' runs
        (tests/test_check_examples_run.py) are the suite's."""
        runs = "\n".join(str(s.get("run", "")) for s in _workflow()["jobs"]["lint"]["steps"])
        for script in ("check_examples.py", "check_doc_examples.py", "check_examples_run.py"):
            assert f"scripts/{script}" not in runs, script

    def test_eager_gc_is_a_pytest_run(self) -> None:
        job = _workflow()["jobs"]["eager-gc"]
        gated = [s for s in job["steps"] if "VERA_EAGER_GC" in (s.get("env") or {})]
        assert [s["env"]["VERA_EAGER_GC"] for s in gated] == ["1"]
        (step,) = gated
        assert step["run"].split() == [
            "pytest", "tests/test_conformance.py",
            "tests/test_check_examples_run.py::TestRealExamples", "-k", "run", "-n", "auto"]

    def test_the_changelog_gate_reads_the_pull_requests_base(self) -> None:
        (step,) = [s for s in _workflow()["jobs"]["lint"]["steps"]
                   if "scripts/check_changelog_updated.py" in str(s.get("run", ""))]
        assert step["env"] == {"BASE_REF": "${{ github.base_ref || 'main' }}"}
        assert step["run"].strip() == 'python scripts/check_changelog_updated.py "origin/$BASE_REF"'

    def test_the_test_matrix_keeps_the_default_mode_on_a_pull_request(self) -> None:
        """On a pull request the matrix's pytest takes no `--matrix`, the
        default that runs a changed matrix whole from VERA_MATRIX_CHANGED;
        an explicit `--matrix=sample` would sample it.  Elsewhere it takes
        `--matrix=full`."""
        (step,) = [s for s in _workflow()["jobs"]["test"]["steps"]
                   if str(s.get("run", "")).startswith("pytest")]
        for event, context in EVENTS.items():
            command = render(str(step["run"]), context, step.get("env"))
            pull_request = context["github.event_name"] == "pull_request"
            want = ["pytest", "-v", "-n", "auto"] + ([] if pull_request else ["--matrix=full"])
            assert command.split() == want, (event, command)


# ---------------------------------------------------------------------------
# The shell that reads a value from `env:`
# ---------------------------------------------------------------------------

WORKFLOWS = ROOT / ".github" / "workflows"

#: A variable a command reads as bash reads it, `$NAME` or `${NAME}`;
#: PowerShell's environment drive, `$env:NAME`, is not one.
_VARIABLE = re.compile(r"\$\{[A-Za-z_]\w*\}|\$[A-Za-z_]\w*(?![\w:])")


def _runners(job: dict[str, Any]) -> list[str]:
    """The runner each of a job's cells takes, its matrix read cell by cell."""
    cells = _matrix_cells(job) if "strategy" in job else [{}]
    return [render(str(job.get("runs-on", "")), cell) for cell in cells]


def _shell(workflow: dict[Any, Any], job: dict[str, Any], step: dict[str, Any]) -> str | None:
    """The shell a step names, by its own `shell:` or else its job's or its
    workflow's `defaults`; None leaves the runner's default."""
    if step.get("shell"):
        return str(step["shell"])
    for owner in (job, workflow):
        shell = ((owner.get("defaults") or {}).get("run") or {}).get("shell")
        if shell:
            return str(shell)
    return None


def unread_on_windows(workflow: dict[Any, Any]) -> list[tuple[str, str]]:
    """The steps a Windows runner takes whose command reads a variable as bash
    does, under a shell other than bash.  A Windows runner's default shell is
    pwsh, which reads `$NAME` as a PowerShell variable of its own, so the
    value the step's `env:` gives the name never reaches the command."""
    found = []
    for job_id, job in (workflow.get("jobs") or {}).items():
        if not any("windows" in runner.lower() for runner in _runners(job)):
            continue
        for step in job.get("steps") or []:
            if _VARIABLE.search(str(step.get("run", ""))) and _shell(workflow, job, step) != "bash":
                found.append((str(job_id), str(step.get("name"))))
    return found


def _one_step(*, runs_on: str = "windows-latest", run: str = 'pytest --shard="$SHARD"',
              shell: str | None = None, job_shell: str | None = None,
              workflow_shell: str | None = None,
              matrix: dict[str, Any] | None = None) -> dict[str, Any]:
    step: dict[str, Any] = {"name": "the step", "run": run}
    if shell is not None:
        step["shell"] = shell
    job: dict[str, Any] = {"runs-on": runs_on, "steps": [step]}
    if job_shell is not None:
        job["defaults"] = {"run": {"shell": job_shell}}
    if matrix is not None:
        job["strategy"] = {"matrix": matrix}
    workflow: dict[str, Any] = {"jobs": {"the job": job}}
    if workflow_shell is not None:
        workflow["defaults"] = {"run": {"shell": workflow_shell}}
    return workflow


class TestTheShellThatReadsAValue:
    """A value a step's `env:` gives reaches its command only through a shell
    that reads `$NAME` from the environment: bash does on every runner, and
    pwsh, a Windows runner's default shell, does not.  The first run of
    #1770 handed both Windows shards `--shard=''`, so every step a Windows
    runner takes that reads one runs under bash."""

    @pytest.mark.parametrize("path", sorted(WORKFLOWS.glob("*.yml")), ids=lambda p: p.name)
    def test_every_workflow_reads_its_values_under_bash_on_windows(self, path: Path) -> None:
        assert unread_on_windows(dict(yaml.safe_load(path.read_text(encoding="utf-8")))) == []

    def test_the_steps_a_windows_runner_takes_that_read_one(self) -> None:
        """The shards' and the test matrix's pytest read `$SHARD` and
        `$MATRIX_ARGS`; the rule above reaches them, as the bash they name
        shows when it is taken away."""
        workflow = _workflow()
        for job_id in ("shard", "test"):
            for step in workflow["jobs"][job_id]["steps"]:
                step.pop("shell", None)
        assert unread_on_windows(workflow) == [("shard", "Run tests"), ("test", "Run tests")]

    @pytest.mark.parametrize(
        ("shape", "flagged"),
        [
            pytest.param({}, True, id="a Windows runner's default shell"),
            pytest.param({"shell": "bash"}, False, id="bash on the step"),
            pytest.param({"job_shell": "bash"}, False, id="bash as the job's default"),
            pytest.param({"workflow_shell": "bash"}, False, id="bash as the workflow's default"),
            pytest.param({"shell": "pwsh"}, True, id="pwsh named"),
            pytest.param({"job_shell": "pwsh", "workflow_shell": "bash"}, True,
                         id="the job's pwsh over the workflow's bash"),
            pytest.param({"runs_on": "${{ matrix.os }}",
                          "matrix": {"os": ["ubuntu-latest", "windows-latest"]}}, True,
                         id="a matrix axis that takes Windows"),
            pytest.param({"runs_on": "${{ matrix.os }}",
                          "matrix": {"include": [{"os": "ubuntu-latest"}, {"os": "windows-latest"}]}},
                         True, id="a matrix include that takes Windows"),
            pytest.param({"runs_on": "${{ matrix.os }}",
                          "matrix": {"os": ["ubuntu-24.04", "macos-15"]}}, False,
                         id="a matrix that never takes Windows"),
            pytest.param({"runs_on": "ubuntu-latest"}, False, id="a Linux runner, whose default is bash"),
            pytest.param({"run": 'pip install -e ".[dev]"'}, False, id="a command that reads no variable"),
            pytest.param({"run": "pytest --shard=$env:SHARD"}, False, id="PowerShell's own $env:NAME"),
            pytest.param({"run": 'pytest --shard="${SHARD}"'}, True, id="a braced variable"),
            pytest.param({"run": 'echo "$RUNNER_TEMP"'}, True, id="a variable the runner sets"),
        ],
    )
    def test_which_steps_need_bash(self, shape: dict[str, Any], flagged: bool) -> None:
        assert unread_on_windows(_one_step(**shape)) == ([("the job", "the step")] if flagged else [])
