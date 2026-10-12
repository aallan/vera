"""The release waits for CI (scripts/await_ci.py).

`release.yml`'s first job waits for the CI workflow's run on the commit it
releases and lets the release go on only when that run succeeded.  The
decision is a function of what `gh run list` reports and the time spent: a
completed run passes when it concluded `success` and fails on any other
conclusion; a run that has not appeared, has not completed, or cannot be
listed is waited for until the timeout, and fails there.  The newest run on
the commit decides, the wait is capped at 100 minutes, and the job is one
that every other job of the release needs.
"""

from __future__ import annotations

import importlib.util
import json
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
TIMEOUT = 100 * MINUTE


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
        assert "100 minutes" in why

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
    """A clock the fake sleep moves, so a 100-minute wait takes no time."""

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


def _wait(list_runs: Callable[[], list[Any]], clock: _Clock, timeout_minutes: int = 100) -> tuple[int, list[str]]:
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

    def test_a_listing_that_keeps_failing_fails_at_the_timeout(self) -> None:
        clock = _Clock()
        status, lines = _wait(_listing(ac.GhError("HTTP 502")), clock, timeout_minutes=5)
        assert status == 1
        assert any(line.startswith("::error::") and "HTTP 502" in line for line in lines), lines


# ---------------------------------------------------------------------------
# The command line, and gh
# ---------------------------------------------------------------------------


class TestTheCommand:
    def test_the_timeout_is_a_hundred_minutes_by_default(self) -> None:
        assert ac.parse_args(["--commit", "abc"]).timeout_minutes == 100

    @pytest.mark.parametrize("minutes", ["101", "1000", "0", "-5", "ten"])
    def test_the_timeout_is_capped_at_a_hundred_minutes(self, minutes: str) -> None:
        with pytest.raises(SystemExit):
            ac.parse_args(["--commit", "abc", "--timeout-minutes", minutes])

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
# The release workflow
# ---------------------------------------------------------------------------


def _release_jobs() -> dict[str, Any]:
    return dict(yaml.safe_load(RELEASE.read_text(encoding="utf-8"))["jobs"])


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
        """The waiting job needs nothing, and every other job needs it, at
        first hand or through the jobs it needs, so nothing of a release
        starts before CI's run on the commit succeeded."""
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

    @pytest.mark.parametrize(
        ("context", "waits"),
        [
            ({"github.event_name": "push", "steps.release.outputs.publish": "true"}, True),
            ({"github.event_name": "push", "steps.release.outputs.publish": "false"}, False),
            ({"github.event_name": "workflow_dispatch", "inputs.target": "production-recovery",
              "steps.release.outputs.publish": ""}, True),
            ({"github.event_name": "workflow_dispatch", "inputs.target": "testpypi",
              "steps.release.outputs.publish": ""}, False),
        ],
    )
    def test_it_waits_wherever_the_release_publishes_to_pypi(
        self, context: dict[str, str], waits: bool,
    ) -> None:
        """A push that raises the version and a production recovery publish
        to PyPI, so they wait; a push that releases nothing and a TestPyPI
        staging run do not.  The push's answer is `release.py prepare`'s own,
        the step `prepare` itself runs."""
        from tests.test_gate_placement import evaluate

        jobs = _release_jobs()
        job = jobs[_waiting_job(jobs)]
        context = {"inputs.target": "", **context}
        steps = {step.get("id"): step for step in job["steps"] if step.get("id")}
        detect = steps["release"]
        assert "scripts/release.py prepare" in " ".join(str(detect["run"]).split())
        assert "--mode push" in " ".join(str(detect["run"]).split())
        wait = next(step for step in job["steps"] if "scripts/await_ci.py" in str(step.get("run", "")))
        assert bool(evaluate(str(wait["if"]), context)) is waits
        assert '--commit "$GITHUB_SHA"' in str(wait["run"])
