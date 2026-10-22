"""The release goes on only from CI's successful run on its commit.

`release.yml` starts when CI's run completes: its first job, the gate, goes
on only for a successful push run of this repository on main, and every
later job reads the commit that run tested.  A dispatched production
recovery, which no CI run started, waits for CI's run on its commit
(scripts/await_ci.py).  The wait's decision is a function of what `gh run
list` reports and the time spent: a completed run passes when it concluded
`success` and fails on any other conclusion; a run that has not appeared,
has not completed, or cannot be listed is waited for until the timeout, and
fails there.  The newest run on the commit decides, the wait is capped at
180 minutes, and the gate is a job that every other job of the release
needs.
"""

from __future__ import annotations

import importlib.util
import io
import json
import os
import re
import shutil
import subprocess
import sys
from collections.abc import Callable, Iterator
from pathlib import Path
from typing import Any

import pytest
import yaml

ROOT = Path(__file__).resolve().parent.parent
SCRIPT = ROOT / "scripts" / "await_ci.py"
RELEASE = ROOT / ".github" / "workflows" / "release.yml"


def _load() -> Any:
    spec = importlib.util.spec_from_file_location("await_ci", SCRIPT)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    # A dataclass resolves its annotations through sys.modules.
    sys.modules["await_ci"] = module
    spec.loader.exec_module(module)
    return module


ac = _load()

MINUTE = 60.0
TIMEOUT = 180 * MINUTE


def _run(id_: int, status: str, conclusion: str = "") -> Any:
    return ac.Run(id=id_, status=status, conclusion=conclusion, url=f"https://ci/{id_}")


# ---------------------------------------------------------------------------
# The decision
# ---------------------------------------------------------------------------


class TestTheDecision:
    def test_a_successful_run_passes(self) -> None:
        verdict, _ = ac.decide([_run(7, "completed", "success")], 5 * MINUTE, TIMEOUT)
        assert verdict == "pass"

    @pytest.mark.parametrize(
        "conclusion",
        ["failure", "cancelled", "timed_out", "skipped", "neutral", "action_required",
         "startup_failure", "stale", ""],
    )
    def test_any_other_conclusion_fails(self, conclusion: str) -> None:
        verdict, why = ac.decide([_run(7, "completed", conclusion)], 5 * MINUTE, TIMEOUT)
        assert verdict == "fail"
        assert "https://ci/7" in why

    @pytest.mark.parametrize("status", ["queued", "in_progress", "waiting", "requested", "pending"])
    def test_a_run_not_yet_completed_is_waited_for(self, status: str) -> None:
        verdict, _ = ac.decide([_run(7, status)], 5 * MINUTE, TIMEOUT)
        assert verdict == "wait"

    def test_no_run_yet_is_waited_for(self) -> None:
        verdict, _ = ac.decide([], 5 * MINUTE, TIMEOUT)
        assert verdict == "wait"

    def test_no_run_within_the_timeout_fails(self) -> None:
        verdict, why = ac.decide([], TIMEOUT, TIMEOUT)
        assert verdict == "fail"
        assert "180 minutes" in why

    def test_a_run_still_going_at_the_timeout_fails(self) -> None:
        verdict, why = ac.decide([_run(7, "in_progress")], TIMEOUT + 1, TIMEOUT)
        assert verdict == "fail"
        assert "in_progress" in why

    def test_a_run_that_completed_is_judged_whenever_it_is_seen(self) -> None:
        """The timeout ends a wait; it does not overrule a conclusion."""
        assert ac.decide([_run(7, "completed", "success")], TIMEOUT * 2, TIMEOUT)[0] == "pass"
        assert ac.decide([_run(7, "completed", "failure")], TIMEOUT * 2, TIMEOUT)[0] == "fail"

    def test_the_newest_run_decides(self) -> None:
        """A run started again for the same commit (a second push of it)
        supersedes the earlier one."""
        old_red_new_green = [_run(1, "completed", "failure"), _run(2, "completed", "success")]
        assert ac.decide(old_red_new_green, MINUTE, TIMEOUT)[0] == "pass"
        old_green_new_going = [_run(2, "in_progress"), _run(1, "completed", "success")]
        assert ac.decide(old_green_new_going, MINUTE, TIMEOUT)[0] == "wait"

    def test_a_listing_that_failed_is_waited_through(self) -> None:
        assert ac.decide(None, MINUTE, TIMEOUT, error="HTTP 502")[0] == "wait"
        verdict, why = ac.decide(None, TIMEOUT, TIMEOUT, error="HTTP 502")
        assert verdict == "fail"
        assert "HTTP 502" in why


# ---------------------------------------------------------------------------
# The wait
# ---------------------------------------------------------------------------


class _Clock:
    """A clock the fake sleep moves, so a 180-minute wait takes no time."""

    def __init__(self) -> None:
        self.now = 0.0
        self.sleeps: list[float] = []

    def __call__(self) -> float:
        return self.now

    def sleep(self, seconds: float) -> None:
        self.sleeps.append(seconds)
        self.now += seconds
        # A wait that outlives any timeout is the bug under test, not a hang.
        assert len(self.sleeps) < 1000, "the wait never ended"


def _listing(*answers: Any) -> Callable[[], list[Any]]:
    """The successive answers of `gh run list`; the last one repeats.  An
    exception instance is raised instead of returned."""
    it: Iterator[Any] = iter(answers)
    last: list[Any] = [None]

    def list_runs() -> list[Any]:
        try:
            last[0] = next(it)
        except StopIteration:
            pass
        if isinstance(last[0], BaseException):
            raise last[0]
        return list(last[0])

    return list_runs


def _wait(list_runs: Callable[[], list[Any]], clock: _Clock, timeout_minutes: int = 180) -> tuple[int, list[str]]:
    lines: list[str] = []
    status = ac.wait(
        list_runs, timeout_minutes=timeout_minutes, interval_seconds=30,
        clock=clock, sleep=clock.sleep, out=lines.append,
    )
    return status, lines


class TestTheWait:
    def test_it_waits_until_the_run_succeeds(self) -> None:
        clock = _Clock()
        status, lines = _wait(
            _listing([], [_run(3, "queued")], [_run(3, "in_progress")], [_run(3, "completed", "success")]),
            clock,
        )
        assert status == 0, lines
        assert clock.sleeps == [30, 30, 30]

    def test_it_fails_when_the_run_fails(self) -> None:
        clock = _Clock()
        status, lines = _wait(_listing([_run(3, "in_progress")], [_run(3, "completed", "failure")]), clock)
        assert status == 1
        assert any(line.startswith("::error::") and "failure" in line for line in lines), lines

    def test_it_gives_up_on_a_run_that_never_appears(self) -> None:
        clock = _Clock()
        status, lines = _wait(_listing([]), clock)
        assert status == 1
        assert clock.now >= TIMEOUT
        assert clock.now < TIMEOUT + 31
        assert any(line.startswith("::error::") for line in lines), lines

    def test_it_gives_up_on_a_run_that_never_completes(self) -> None:
        clock = _Clock()
        status, _ = _wait(_listing([_run(3, "in_progress")]), clock, timeout_minutes=10)
        assert status == 1
        assert 10 * MINUTE <= clock.now < 10 * MINUTE + 31

    def test_a_failed_listing_is_retried(self) -> None:
        clock = _Clock()
        status, lines = _wait(
            _listing(ac.GhError("HTTP 502"), [_run(3, "completed", "success")]), clock,
        )
        assert status == 0, lines
        assert any("HTTP 502" in line for line in lines), lines

    def test_each_line_reaches_the_log_when_it_is_printed(self, monkeypatch: pytest.MonkeyPatch) -> None:
        """Actions' stdout is not a terminal, so Python buffers it: a line
        not flushed would show only when the wait ends, up to 180 minutes
        later."""

        class Recorder(io.StringIO):
            def __init__(self) -> None:
                super().__init__()
                self.flushed: list[str] = []

            def flush(self) -> None:
                self.flushed.append(self.getvalue())
                super().flush()

        recorder = Recorder()
        monkeypatch.setattr(sys, "stdout", recorder)
        clock = _Clock()
        assert ac.wait(_listing([], [_run(3, "completed", "success")]), clock=clock, sleep=clock.sleep) == 0
        assert recorder.flushed, "nothing was flushed"
        assert recorder.flushed[0] == "no CI run on the commit yet\n", recorder.flushed
        assert recorder.flushed[-1].endswith("succeeded\n"), recorder.flushed

    def test_a_listing_that_keeps_failing_fails_at_the_timeout(self) -> None:
        clock = _Clock()
        status, lines = _wait(_listing(ac.GhError("HTTP 502")), clock, timeout_minutes=5)
        assert status == 1
        assert any(line.startswith("::error::") and "HTTP 502" in line for line in lines), lines


# ---------------------------------------------------------------------------
# The command line, and gh
# ---------------------------------------------------------------------------


class TestTheCommand:
    def test_the_timeout_is_180_minutes_by_default(self) -> None:
        """The full matrix's push run on v0.2.5's release commit took 106
        minutes (CI run 39744875795), past the 100 the wait then allowed."""
        assert ac.parse_args(["--commit", "abc"]).timeout_minutes == 180

    @pytest.mark.parametrize("minutes", ["1", "100", "180"])
    def test_the_timeout_is_any_whole_number_of_minutes_up_to_the_cap(self, minutes: str) -> None:
        assert ac.parse_args(["--commit", "abc", "--timeout-minutes", minutes]).timeout_minutes == int(minutes)

    @pytest.mark.parametrize("minutes", ["181", "1000", "0", "-5", "ten"])
    def test_the_timeout_is_capped_at_180_minutes(self, minutes: str) -> None:
        with pytest.raises(SystemExit):
            ac.parse_args(["--commit", "abc", "--timeout-minutes", minutes])

    def test_the_wait_fits_inside_its_job(self) -> None:
        """The job that waits outlasts the longest wait, so a run that fails
        at the cap reports its `::error::` line rather than the job's
        timeout."""
        jobs = _release_jobs()
        assert int(jobs[_waiting_job(jobs)]["timeout-minutes"]) > ac.CAP_MINUTES

    def test_it_asks_gh_for_the_workflow_runs_on_the_commit(self) -> None:
        assert ac.gh_command("abc123", "ci.yml", "push") == [
            "gh", "run", "list", "--commit", "abc123", "--workflow", "ci.yml",
            "--event", "push", "--json", "databaseId,status,conclusion,url", "--limit", "20",
        ]

    def test_it_reads_gh_json(self) -> None:
        text = json.dumps([
            {"databaseId": 11, "status": "completed", "conclusion": "success", "url": "u11"},
            {"databaseId": 12, "status": "in_progress", "conclusion": "", "url": "u12"},
        ])
        assert ac.parse_runs(text) == [
            ac.Run(id=11, status="completed", conclusion="success", url="u11"),
            ac.Run(id=12, status="in_progress", conclusion="", url="u12"),
        ]

    @pytest.mark.parametrize("text", ["", "not json", "{}", '[{"status": "completed"}]'])
    def test_unreadable_gh_output_is_a_failed_listing(self, text: str) -> None:
        with pytest.raises(ac.GhError):
            ac.parse_runs(text)

    def test_main_waits_on_the_commit_it_is_given(self) -> None:
        clock = _Clock()
        asked: list[tuple[str, str, str]] = []

        def list_runs(commit: str, workflow: str, event: str) -> list[Any]:
            asked.append((commit, workflow, event))
            return [_run(9, "completed", "success")]

        assert ac.main(["--commit", "f00"], list_runs=list_runs, clock=clock, sleep=clock.sleep) == 0
        assert asked == [("f00", "ci.yml", "push")]


# ---------------------------------------------------------------------------
# The run it waits for
# ---------------------------------------------------------------------------


def _concurrency(context: dict[str, object]) -> tuple[object, object]:
    """CI's concurrency group and cancel-in-progress for one run."""
    from tests.test_gate_placement import evaluate, render

    ci = yaml.safe_load((ROOT / ".github" / "workflows" / "ci.yml").read_text(encoding="utf-8"))
    concurrency = ci["concurrency"]
    return (
        render(str(concurrency["group"]), context),
        evaluate(str(concurrency["cancel-in-progress"]), context),
    )


def _push(sha: str) -> dict[str, object]:
    return {
        "github.workflow": "CI", "github.event_name": "push",
        "github.ref": "refs/heads/main", "github.sha": sha,
    }


def test_every_push_run_to_main_runs() -> None:
    """The release starts from CI's push run on its commit, so that run must
    not be dropped.  A concurrency group holds one pending run and a newer
    arrival replaces it, so a push run has a group of its own, its commit:
    two pushes never share one, and a push run is never cancelled.  A pull
    request's runs share its group, so a new push cancels the old run, and
    the nightly run has a group of its own."""
    first, second = _concurrency(_push("1" * 40)), _concurrency(_push("2" * 40))
    assert first[0] != second[0], (first, second)
    assert first[1] is False and second[1] is False
    pull_request = {
        "github.workflow": "CI", "github.event_name": "pull_request",
        "github.ref": "refs/pull/7/merge", "github.sha": "3" * 40,
    }
    again = {**pull_request, "github.sha": "4" * 40}
    assert _concurrency(pull_request)[0] == _concurrency(again)[0]
    assert _concurrency(pull_request)[1] is True
    nightly = {**_push("1" * 40), "github.event_name": "schedule"}
    assert _concurrency(nightly)[0] not in (first[0], _concurrency(pull_request)[0])


# ---------------------------------------------------------------------------
# The release workflow
# ---------------------------------------------------------------------------


def _release_jobs() -> dict[str, Any]:
    return dict(yaml.safe_load(RELEASE.read_text(encoding="utf-8"))["jobs"])


def test_every_release_run_waits_its_turn() -> None:
    """Release runs share one group and none is cancelled, so no two
    overlap.  A group without a queue holds one pending run, which a newer
    arrival replaces, so a release that waits behind another while a third
    push arrives would be dropped; `queue: max` keeps every pending run, in
    order."""
    concurrency = yaml.safe_load(RELEASE.read_text(encoding="utf-8"))["concurrency"]
    assert concurrency == {"group": "vera-release", "cancel-in-progress": False, "queue": "max"}


def _needs(job: dict[str, Any]) -> list[str]:
    needs = job.get("needs") or []
    return [needs] if isinstance(needs, str) else list(needs)


def _waiting_job(jobs: dict[str, Any]) -> str:
    names = [
        name for name, job in jobs.items()
        if any("scripts/await_ci.py" in str(step.get("run", "")) for step in job.get("steps", []))
    ]
    assert len(names) == 1, names
    return names[0]


class TestTheReleaseWorkflow:
    def test_every_other_job_waits_for_ci(self) -> None:
        """The gate needs nothing, and every other job needs it, at first
        hand or through the jobs it needs, so nothing of a release starts
        before the gate has seen CI's run on the commit succeed."""
        jobs = _release_jobs()
        first = _waiting_job(jobs)
        assert _needs(jobs[first]) == []
        assert first in _needs(jobs["prepare"])

        def ancestors(name: str) -> set[str]:
            found: set[str] = set()
            for parent in _needs(jobs[name]):
                found |= {parent, *ancestors(parent)}
            return found

        for name in jobs:
            if name != first:
                assert first in ancestors(name), name

    def test_it_asks_prepare_its_own_questions(self) -> None:
        """The gate plans the merge and a production recovery with the very
        steps `prepare` runs, the same command under the same condition and
        environment, so a recovery waits exactly where `prepare` will
        publish to PyPI, and a run `prepare` refuses fails at once rather
        than after a wait for a CI run that never comes."""
        jobs = _release_jobs()
        waiting = {step.get("id"): step for step in jobs[_waiting_job(jobs)]["steps"] if step.get("id")}
        planning = {step.get("id"): step for step in jobs["prepare"]["steps"] if step.get("id")}
        for name in ("push", "recovery"):
            assert name in waiting and name in planning, name
            for key in ("if", "env", "run"):
                assert waiting[name].get(key) == planning[name].get(key), (name, key)

    @pytest.mark.parametrize(
        ("context", "waits"),
        [
            ({"github.event_name": "workflow_run", "steps.push.outputs.publish": "true"}, False),
            ({"github.event_name": "workflow_run", "steps.push.outputs.publish": "false"}, False),
            ({"github.event_name": "workflow_dispatch", "steps.recovery.outputs.publish": "true"}, True),
            ({"github.event_name": "workflow_dispatch"}, False),
        ],
    )
    def test_it_waits_where_a_recovery_publishes_to_pypi(
        self, context: dict[str, str], waits: bool,
    ) -> None:
        """A production recovery publishes to PyPI with no CI run behind it,
        so it waits for CI's push run on the dispatched commit.  A run CI's
        completion started does not wait, whether the merge raises the
        version or not: the gate let it through because that run succeeded.
        Neither does a TestPyPI staging run, where neither planning step
        runs."""
        from tests.test_gate_placement import evaluate

        jobs = _release_jobs()
        job = jobs[_waiting_job(jobs)]
        context = {"steps.push.outputs.publish": "", "steps.recovery.outputs.publish": "", **context}
        wait = next(step for step in job["steps"] if "scripts/await_ci.py" in str(step.get("run", "")))
        assert bool(evaluate(str(wait["if"]), context)) is waits
        assert '--commit "$RELEASE_SHA"' in str(wait["run"])
        assert wait["env"]["RELEASE_SHA"] == "${{ steps.commit.outputs.sha }}"


# ---------------------------------------------------------------------------
# The release starts when CI's run on the commit completes
# ---------------------------------------------------------------------------


def _release() -> dict[Any, Any]:
    return dict(yaml.safe_load(RELEASE.read_text(encoding="utf-8")))


def _triggers(workflow: dict[Any, Any]) -> dict[str, Any]:
    """The workflow's `on:` block, which YAML 1.1 reads as the key True."""
    return dict(workflow["on"] if "on" in workflow else workflow[True])


_REPOSITORY = "aallan/vera"

#: Every conclusion a completed workflow run can carry.
_CONCLUSIONS = ["success", "failure", "cancelled", "timed_out", "skipped", "neutral",
                "action_required", "startup_failure", "stale"]


def _completed_run(conclusion: str, event: str, branch: str, repository: str) -> dict[str, object]:
    """The context of a release run that CI's completed run started."""
    return {
        "github.event_name": "workflow_run", "github.repository": _REPOSITORY,
        "github.event.workflow_run.conclusion": conclusion,
        "github.event.workflow_run.event": event,
        "github.event.workflow_run.head_branch": branch,
        "github.event.workflow_run.head_repository.full_name": repository,
    }


class TestTheReleaseStartsWhenCiCompletes:
    """`release.yml` starts when CI's run completes, rather than polling for
    it from a push run of its own: its first job is a gate that goes on only
    for a successful push run of this repository on main, and every later
    use of the commit reads the one that run tested.  Under `workflow_run`,
    `github.sha` is the default branch's tip when the event fires, which a
    later merge can have moved past the commit the run tested."""

    def test_it_starts_when_ci_completes_on_main(self) -> None:
        """A `workflow_run` trigger on CI's completed runs on main, named as
        ci.yml names itself, and no `push` trigger, which would start a
        second run on every merge.  The dispatch path keeps its inputs."""
        on = _triggers(_release())
        ci_name = yaml.safe_load((ROOT / ".github" / "workflows" / "ci.yml").read_text(encoding="utf-8"))["name"]
        assert set(on) == {"workflow_run", "workflow_dispatch"}, on
        assert on["workflow_run"] == {"workflows": [ci_name], "types": ["completed"], "branches": ["main"]}
        assert set(on["workflow_dispatch"]["inputs"]) == {"target", "confirm_version"}

    @pytest.mark.parametrize("conclusion", _CONCLUSIONS)
    @pytest.mark.parametrize("event", ["push", "pull_request", "schedule", "workflow_dispatch"])
    @pytest.mark.parametrize("branch", ["main", "feature"])
    @pytest.mark.parametrize("repository", [_REPOSITORY, "someone/vera"])
    def test_the_gate_admits_only_a_successful_push_run_of_this_repository_on_main(
        self, conclusion: str, event: str, branch: str, repository: str,
    ) -> None:
        """`branches: [main]` matches a run's head branch, which a fork's
        pull request can name `main` too, and CI also completes for pull
        requests and the nightly run; so the gate reads the conclusion, the
        event, the branch and the repository, and goes on for one cell of
        the 144: a successful push run of this repository on main."""
        from tests.test_gate_placement import evaluate

        jobs = _release_jobs()
        gate = jobs[_waiting_job(jobs)]
        assert "if" in gate, "the first job has no condition: every completed CI run would start a release"
        admitted = bool(evaluate(str(gate["if"]), _completed_run(conclusion, event, branch, repository)))
        expected = (conclusion, event, branch, repository) == ("success", "push", "main", _REPOSITORY)
        assert admitted is expected

    @pytest.mark.parametrize("target", ["testpypi", "production-recovery"])
    def test_a_dispatched_run_passes_the_gate(self, target: str) -> None:
        """A dispatch has no CI run behind it: the gate lets it through, and
        its own steps plan it (`prepare`) and wait for CI where it publishes
        to PyPI (`await_ci.py`)."""
        from tests.test_gate_placement import evaluate

        jobs = _release_jobs()
        gate = jobs[_waiting_job(jobs)]
        context: dict[str, object] = {
            **{key: None for key in _completed_run("", "", "", "")},
            "github.event_name": "workflow_dispatch", "github.repository": _REPOSITORY,
            "inputs.target": target,
        }
        assert bool(evaluate(str(gate.get("if", "true")), context)) is True

    def test_every_step_reads_the_commit_ci_ran_on(self) -> None:
        """`github.sha` is read in one place, where the gate names the commit
        (`github.event.workflow_run.head_sha` under `workflow_run`, and
        `github.sha` itself on a dispatch, where it is the dispatched
        commit), and nowhere else: not as `$GITHUB_SHA` in a shell, not
        through an `actions/checkout` that names no `ref:`, whose default is
        `github.sha`, and not through `github.event.before`, which a
        `workflow_run` event does not carry."""
        text = RELEASE.read_text(encoding="utf-8")
        reads = [line.strip() for line in text.splitlines()
                 if ("github.sha" in line or "GITHUB_SHA" in line)
                 and not line.strip().startswith("#")]
        assert reads == ["SHA: ${{ github.event.workflow_run.head_sha || github.sha }}"], reads
        assert "github.event.before" not in text
        for name, job in _release_jobs().items():
            for step in job.get("steps", []):
                if str(step.get("uses", "")).startswith("actions/checkout@"):
                    ref = str((step.get("with") or {}).get("ref", ""))
                    assert re.fullmatch(r"\$\{\{ (needs\.\w+|steps\.\w+)\.outputs\.sha \}\}", ref), (name, ref)


# ---------------------------------------------------------------------------
# The Latest mark
# ---------------------------------------------------------------------------


#: gh as the release step calls it: the tag's read (the tag exists at the
#: release commit), the listing of the published Releases, which answers
#: with what the step's `--jq` makes of them (`STUB_FAIL` fails it), and the
#: release's creation.
_STUB_GH = '''#!{python}
import json, os, sys
args = sys.argv[1:]
with open(os.environ["STUB_LOG"], "a", encoding="utf-8") as log:
    log.write(json.dumps(args) + "\\n")
if args[:1] == ["api"] and "/git/ref/tags/" in args[1]:
    print(os.environ["RELEASE_SHA"])
elif args[:1] == ["api"] and args[1].endswith("/releases"):
    if os.environ.get("STUB_FAIL"):
        sys.exit("HTTP 502")
    print("\\n".join(os.environ["STUB_RELEASES"].split()))
elif args[:2] != ["release", "create"]:
    sys.exit(f"unexpected gh call: {{args}}")
'''


@pytest.mark.skipif(os.name == "nt" or shutil.which("bash") is None,
                    reason="the step is a bash script for ubuntu-latest")
class TestTheLatestMark:
    """Releases start in the order their merges' CI runs complete, and a
    second version-raising merge's run can complete first, so the GitHub
    Release is marked Latest only when no higher version is already
    released.  The tag and release step runs here as the runner runs it
    (`bash -e`), with a stand-in `gh`."""

    def _release(self, tmp_path: Path, version: str, released: str,
                 **extra: str) -> tuple[int, list[list[str]]]:
        (step,) = [s for s in _release_jobs()["github-release"]["steps"]
                   if s.get("name") == "Create immutable tag and GitHub Release"]
        bin_dir = tmp_path / "bin"
        bin_dir.mkdir()
        gh = bin_dir / "gh"
        gh.write_text(_STUB_GH.format(python=sys.executable), encoding="utf-8")
        gh.chmod(0o755)
        script = tmp_path / "step.sh"
        script.write_text(str(step["run"]), encoding="utf-8")
        log = tmp_path / "gh.jsonl"
        # No startup file: one that sets PATH would find the real gh first.
        env = {name: value for name, value in os.environ.items() if name not in ("BASH_ENV", "ENV")}
        env.update({"PATH": f"{bin_dir}{os.pathsep}{os.environ.get('PATH', '')}",
                    "GITHUB_REPOSITORY": "aallan/vera", "GH_TOKEN": "token", "VERSION": version,
                    "RELEASE_SHA": "a" * 40, "STUB_LOG": str(log), "STUB_RELEASES": released,
                    **extra})
        proc = subprocess.run(["bash", "-e", str(script)], cwd=tmp_path, env=env, check=False,
                              capture_output=True, text=True, encoding="utf-8")
        calls = [json.loads(line) for line in log.read_text(encoding="utf-8").splitlines()]
        return proc.returncode, calls

    @pytest.mark.parametrize(("version", "released", "latest"), [
        ("0.2.6", "0.2.4 0.2.5", "true"),
        ("0.2.6", "0.2.5 0.2.7", "false"),
        ("0.2.10", "0.2.8 0.2.9", "true"),
        ("0.2.9", "0.2.8 0.2.10", "false"),
        ("0.3.0", "0.2.9 scode-1.0.0 1.0.0rc1", "true"),
        ("0.1.0", "", "true"),
    ])
    def test_a_release_is_latest_only_when_no_higher_version_is_released(
        self, tmp_path: Path, version: str, released: str, latest: str,
    ) -> None:
        """Versions compare as versions, not as text; a Release that is not
        a release version (`vscode-1.0.0` reads as `scode-1.0.0` once the
        prefix goes) is no rival, and nor is a tag with no published Release,
        which the listing does not hold; the first release is Latest."""
        code, calls = self._release(tmp_path, version, released)
        assert code == 0
        (create,) = [c for c in calls if c[:2] == ["release", "create"]]
        assert create[2] == f"v{version}" and f"--latest={latest}" in create
        assert "--latest" not in create

    def test_a_failed_read_of_the_releases_creates_no_release(self, tmp_path: Path) -> None:
        """A listing that fails says nothing about the versions released, so
        the step stops before the release is created, rather than mark it."""
        code, calls = self._release(tmp_path, "0.2.6", "0.2.5", STUB_FAIL="1")
        assert code != 0
        assert not [c for c in calls if c[:2] == ["release", "create"]]
