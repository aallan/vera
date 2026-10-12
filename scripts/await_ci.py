#!/usr/bin/env python
"""Wait for CI's run on a commit, and pass only if it succeeded.

``release.yml``'s first job runs this before anything of a release starts,
since the full test matrix runs after the merge rather than on the pull
request: the push event a version-raising merge produces on ``main`` runs it
in CI, and the release publishes only once that run has succeeded.  The
script asks ``gh run list`` for the runs of the CI workflow on the commit,
every thirty seconds, and the newest one decides:

- a run that completed with the conclusion ``success`` passes;
- a run that completed with any other conclusion fails;
- a run not yet completed, no run yet, or a listing ``gh`` could not make is
  waited for, until the timeout, where it fails.

The timeout is 100 minutes by default and at most: the post-merge run of the
full matrix takes about half that, including the wait for macOS runners.
A failure prints a ``::error::`` line, which Actions shows on the run.
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
import time
from collections.abc import Callable, Sequence
from dataclasses import dataclass

CAP_MINUTES = 100
INTERVAL_SECONDS = 30


def _say(line: str) -> None:
    """Print a line now: stdout is not a terminal in Actions, so it would be
    buffered, and a wait of many minutes would show nothing until its end."""
    print(line, flush=True)


class GhError(Exception):
    """`gh run list` failed or printed something that is not its JSON."""


@dataclass(frozen=True)
class Run:
    """What the decision reads of one workflow run."""

    id: int
    status: str
    conclusion: str
    url: str


def gh_command(commit: str, workflow: str, event: str) -> list[str]:
    """The `gh` invocation that lists `workflow`'s runs for `event` on `commit`."""
    return [
        "gh", "run", "list", "--commit", commit, "--workflow", workflow,
        "--event", event, "--json", "databaseId,status,conclusion,url", "--limit", "20",
    ]


def parse_runs(text: str) -> list[Run]:
    """The runs in `gh run list --json` output."""
    try:
        data = json.loads(text)
        if not isinstance(data, list):
            raise TypeError(f"a {type(data).__name__}, not a list")
        return [
            Run(
                id=int(item["databaseId"]), status=str(item["status"]),
                conclusion=str(item.get("conclusion") or ""), url=str(item["url"]),
            )
            for item in data
        ]
    except (ValueError, TypeError, KeyError) as exc:
        raise GhError(f"cannot read gh's output ({exc}): {text[:200]!r}") from exc


def gh_list_runs(commit: str, workflow: str, event: str) -> list[Run]:
    """The runs `gh` lists, or GhError."""
    try:
        result = subprocess.run(
            gh_command(commit, workflow, event), capture_output=True, text=True,
            encoding="utf-8", check=False, timeout=120,
        )
    except (OSError, subprocess.SubprocessError) as exc:
        raise GhError(str(exc)) from exc
    if result.returncode != 0:
        raise GhError(result.stderr.strip() or f"gh exited {result.returncode}")
    return parse_runs(result.stdout)


def decide(
    runs: Sequence[Run] | None, elapsed: float, timeout: float, error: str | None = None,
) -> tuple[str, str]:
    """`("pass" | "fail" | "wait", why)` for what a listing showed after
    `elapsed` seconds of a `timeout`-second wait.  `runs` is None when the
    listing failed, with `error` saying why."""
    minutes = f"{timeout / 60:g} minutes"
    if runs is None:
        if elapsed >= timeout:
            return "fail", f"could not list the CI runs within {minutes}: {error}"
        return "wait", f"could not list the CI runs ({error}); trying again"
    if not runs:
        if elapsed >= timeout:
            return "fail", f"no CI run on the commit within {minutes}"
        return "wait", "no CI run on the commit yet"
    run = max(runs, key=lambda r: r.id)
    if run.status != "completed":
        if elapsed >= timeout:
            return "fail", f"the CI run {run.url} is still {run.status} after {minutes}"
        return "wait", f"the CI run {run.url} is {run.status}"
    if run.conclusion == "success":
        return "pass", f"the CI run {run.url} succeeded"
    return "fail", f"the CI run {run.url} concluded {run.conclusion or 'without a conclusion'}"


def wait(
    list_runs: Callable[[], list[Run]],
    *,
    timeout_minutes: int = CAP_MINUTES,
    interval_seconds: float = INTERVAL_SECONDS,
    clock: Callable[[], float] = time.monotonic,
    sleep: Callable[[float], None] = time.sleep,
    out: Callable[[str], None] = _say,
) -> int:
    """Poll until the decision is made; 0 for a pass, 1 for a failure.
    A state is printed when it changes, not on every poll."""
    timeout = timeout_minutes * 60.0
    start = clock()
    last = ""
    while True:
        runs: list[Run] | None
        error: str | None = None
        try:
            runs = list_runs()
        except GhError as exc:
            runs, error = None, str(exc)
        verdict, why = decide(runs, clock() - start, timeout, error)
        if verdict == "pass":
            out(why)
            return 0
        if verdict == "fail":
            out(f"::error::{why}")
            return 1
        if why != last:
            out(why)
            last = why
        sleep(interval_seconds)


def _minutes(value: str) -> int:
    try:
        minutes = int(value)
    except ValueError as exc:
        raise argparse.ArgumentTypeError(f"{value!r} is not a whole number of minutes") from exc
    if not 1 <= minutes <= CAP_MINUTES:
        raise argparse.ArgumentTypeError(f"the timeout is 1 to {CAP_MINUTES} minutes, not {minutes}")
    return minutes


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--commit", required=True, help="the commit whose CI run to wait for")
    parser.add_argument("--workflow", default="ci.yml", help="the CI workflow's file (default: ci.yml)")
    parser.add_argument("--event", default="push", help="the event of the run (default: push)")
    parser.add_argument(
        "--timeout-minutes", type=_minutes, default=CAP_MINUTES,
        help=f"how long to wait, at most {CAP_MINUTES} (the default)",
    )
    return parser.parse_args(argv)


def main(
    argv: Sequence[str] | None = None,
    *,
    list_runs: Callable[[str, str, str], list[Run]] = gh_list_runs,
    clock: Callable[[], float] = time.monotonic,
    sleep: Callable[[float], None] = time.sleep,
) -> int:
    args = parse_args(argv)
    _say(f"Waiting for the {args.workflow} {args.event} run on {args.commit}.")
    return wait(
        lambda: list_runs(args.commit, args.workflow, args.event),
        timeout_minutes=args.timeout_minutes, clock=clock, sleep=sleep,
    )


if __name__ == "__main__":
    sys.exit(main())
