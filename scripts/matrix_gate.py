#!/usr/bin/env python
"""The matrix gate: whether the full test matrix ran where it had to, and passed.

ci.yml's ``matrix-gate`` job runs on every run once the ``plan`` job and the
``test`` matrix are done, whatever their outcome, and is the required check
that makes the full OS x Python matrix mandatory on a pull request that
raises ``[project].version`` and absent from every other: the matrix's own
cells are not required checks, since they report nothing on a pull request
that keeps the version.  The job hands this script three values:

- ``PLAN_RESULT``: the plan job's result, ``needs.plan.result``;
- ``RELEASE``: the plan job's answer to "does this change raise the
  version?", ``true`` or ``false``, and empty on the nightly run, where the
  step that answers does not run;
- ``TEST_RESULT``: the matrix's result, ``needs.test.result``.

The gate passes when the plan succeeded and either every cell of the matrix
passed, or the version stays (``RELEASE`` is ``false``) and the matrix was
skipped.  Anything else fails it: a plan that failed (its matrix is skipped
for that reason, not because the version stays, and the shard jobs that
need it are skipped too), a cell that failed or was cancelled, a matrix
skipped on a change that raises the version, and any value the gate cannot
read.

The matrix's result alone does not say every cell passed (#1659).  It is
the aggregate GitHub computes over the cells that ran in the current attempt
of the run, so where one of two failed cells is re-run on its own and
passes, the new attempt's result reads ``success`` while the other cell is
still failed.  So wherever the matrix ran, the gate also lists the run's
jobs, ``gh run view $GITHUB_RUN_ID --attempt $GITHUB_RUN_ATTEMPT --json
jobs`` with the job's ``GH_TOKEN``, and passes only when that listing holds
as many cells as the matrix runs, ``MATRIX_CELLS`` (the ``test`` job's
``cells`` output, ``strategy.job-total``), and every one of them, the
advisory cell apart, concluded ``success``.  A re-run attempt lists every
job of the run: the ones it ran again, and a copy of each other job with the
conclusion it had (tests/fixtures/matrix_gate/ holds the two attempts of a
run whose second re-ran its one failed cell).  A listing the gate cannot
read, a run id, attempt or size it cannot read, and a listing that holds
another number of cells each fail it.

The blocking cells whose conclusion is ``failure`` go to the step's
``failed`` output, a JSON list written only when it is not empty, which
``matrix-issue`` names in the issue it files.

The nightly run is a run of ``nightly-matrix.yml``, which calls ci.yml, and
a call's run lists every job of the called workflow under the calling job's
name: ``CI / test (ubuntu-24.04, 3.11)``.  The gate reads a cell's name
through that prefix, so the nightly run's listing holds the cells a push
run's does, and names them as ci.yml does.  On the nightly run the listing
also holds the ``watch`` job's cells, ``watch (<os>, <python>)``, on the
floating ``-latest`` labels and the newest image no cell of the matrix
runs.  They are advisory and no cell of the full matrix: the verdict reads
none of them, and the ones whose conclusion is ``failure`` go to the
step's ``watched`` output, a JSON list written only when it is not empty,
which ``matrix-issue`` files too.
"""

from __future__ import annotations

import json
import os
import re
import subprocess
import sys
from collections.abc import Callable, Sequence
from typing import NamedTuple

_RESULTS = frozenset({"success", "failure", "cancelled", "skipped"})
_RELEASES = frozenset({"true", "false", ""})

#: The matrix's results under which it ran, so its listing has cells to read.
_RAN = frozenset({"success", "failure", "cancelled"})

#: A cell of the full matrix as ci.yml names it: the ``test`` job's name,
#: ``test (<os>, <python>)``.  A shard of a pull request's suite,
#: ``test (<os>, 3.12, shard K/N)``, has a third part and is no cell.
CELL = re.compile(r"test \([^,()]+, [^,()]+\)")

#: A cell of the watched images as ci.yml names it: the ``watch`` job's
#: name, ``watch (<os>, <python>)``, on the nightly run alone.
WATCHED = re.compile(r"watch \([^,()]+, [^,()]+\)")

#: The calling job's name before a job's own, as a call's run lists the
#: called workflow's jobs: ``CI / ``.  A shard's ``K/N`` has no space
#: around its slash, so no name ci.yml gives a job holds one.
_CALLER = re.compile(r"[^/]+ / ")

#: The cells allowed to fail: the matrix's ``advisory`` entries, which ci.yml
#: runs with ``continue-on-error`` (README § Supported platforms).
ADVISORY = frozenset({"test (ubuntu-24.04-arm, 3.12)"})

#: How long ``gh run view`` has to answer, in seconds.
TIMEOUT = 120

#: A run's id, its attempt's number and the matrix's size, as Actions writes
#: them: a positive decimal number.
_NUMBER = re.compile(r"[1-9][0-9]*")


class Job(NamedTuple):
    """What the gate reads of one job in the run's listing."""

    name: str
    status: str
    conclusion: str


class Verdict(NamedTuple):
    """The gate's answer, why, the blocking cells that failed, and the
    watched cells that failed, which the answer does not read."""

    passed: bool
    why: str
    failed: tuple[str, ...]
    watched: tuple[str, ...] = ()


class ListingError(Exception):
    """The run's job listing could not be read."""


def decide(plan: str, release: str, matrix: str) -> tuple[bool, str]:
    """Whether the gate passes, and why, from the plan job's result, its
    release answer and the matrix's result."""
    if plan not in _RESULTS:
        return False, f"the plan job's result {plan!r} is not one the gate can read"
    if release not in _RELEASES:
        return False, f"the plan job's release answer {release!r} is not true or false"
    if matrix not in _RESULTS:
        return False, f"the matrix's result {matrix!r} is not one the gate can read"
    if plan != "success":
        return False, (
            f"the plan job's result is {plan}, so whether the full matrix must"
            " run is not known"
        )
    if matrix == "success":
        return True, "the full test matrix ran and every cell passed"
    if matrix == "skipped":
        if release == "false":
            return True, "the change keeps [project].version, so the full test matrix does not run"
        if release == "true":
            return False, "the change raises [project].version and the full test matrix was skipped"
        return False, "the full test matrix was skipped and the plan job gave no release answer"
    return False, f"the full test matrix concluded {matrix}"


def gh_command(run_id: str, attempt: str) -> list[str]:
    """The `gh` invocation that lists a run's jobs in one attempt."""
    return ["gh", "run", "view", run_id, "--attempt", attempt, "--json", "jobs"]


def matrix_size(text: str) -> int:
    """The number of cells the matrix runs, as the `test` job's `cells`
    output states it, or ListingError."""
    if not _NUMBER.fullmatch(text):
        raise ListingError(
            f"the matrix's size {text!r}, the test job's `cells` output, is not a number of cells"
        )
    return int(text)


def parse_jobs(text: str) -> list[Job]:
    """The jobs in `gh run view --json jobs` output, or ListingError.  A job
    still running has no conclusion, which reads as the empty string."""
    try:
        data = json.loads(text)
    except ValueError as exc:
        raise ListingError(f"gh's output is not JSON ({exc}): {text[:200]!r}") from None
    jobs = data.get("jobs") if isinstance(data, dict) else None
    if not isinstance(jobs, list):
        raise ListingError(f"gh's output holds no list of jobs: {text[:200]!r}")
    out = []
    for job in jobs:
        if not (
            isinstance(job, dict)
            and isinstance(job.get("name"), str)
            and isinstance(job.get("status"), str)
            and isinstance(job.get("conclusion"), (str, type(None)))
        ):
            raise ListingError(f"a job in the listing has no name, status and conclusion: {job!r:.200}")
        out.append(Job(job["name"], job["status"], job["conclusion"] or ""))
    return out


def gh_list_jobs(run_id: str, attempt: str) -> list[Job]:
    """The jobs of the run `run_id`, in its attempt `attempt`, as `gh` lists
    them, or ListingError."""
    if not _NUMBER.fullmatch(run_id):
        raise ListingError(f"GITHUB_RUN_ID {run_id!r} is not a run's id")
    if not _NUMBER.fullmatch(attempt):
        raise ListingError(f"GITHUB_RUN_ATTEMPT {attempt!r} is not an attempt's number")
    command = gh_command(run_id, attempt)
    try:
        result = subprocess.run(
            command, capture_output=True, text=True, encoding="utf-8", check=False, timeout=TIMEOUT,
        )
    except (OSError, subprocess.SubprocessError) as exc:
        raise ListingError(f"`{' '.join(command)}` did not run: {exc}") from None
    if result.returncode != 0:
        detail = result.stderr.strip() or f"exit status {result.returncode}"
        raise ListingError(f"`{' '.join(command)}` failed: {detail}")
    return parse_jobs(result.stdout)


def bare(name: str) -> str:
    """A job's name as ci.yml gives it: the listing's name without the
    calling job's, which a run of the nightly workflow puts before it."""
    caller = _CALLER.match(name)
    return name[caller.end():] if caller else name


def cells_of(jobs: Sequence[Job]) -> list[Job]:
    """The cells of the full matrix in a listing, the advisory ones too,
    each under the name ci.yml gives it."""
    return [job._replace(name=bare(job.name)) for job in jobs if CELL.fullmatch(bare(job.name))]


def watched_cells(jobs: Sequence[Job]) -> list[Job]:
    """The watched images' cells in a listing, each under the name ci.yml
    gives it."""
    return [job._replace(name=bare(job.name)) for job in jobs if WATCHED.fullmatch(bare(job.name))]


def failed_watched(jobs: Sequence[Job]) -> tuple[str, ...]:
    """The watched cells in a listing whose conclusion is `failure`."""
    return tuple(sorted(job.name for job in watched_cells(jobs) if job.conclusion == "failure"))


def blocking_cells(jobs: Sequence[Job]) -> list[Job]:
    """The cells of the full matrix in a listing, the advisory ones apart."""
    return [job for job in cells_of(jobs) if job.name not in ADVISORY]


def failed_cells(jobs: Sequence[Job]) -> tuple[str, ...]:
    """The blocking cells in a listing whose conclusion is `failure`."""
    return tuple(sorted(job.name for job in blocking_cells(jobs) if job.conclusion == "failure"))


def judge(jobs: Sequence[Job], size: int) -> Verdict:
    """Whether a listing holds the `size` cells the matrix runs, and every
    blocking one of them concluded `success`."""
    cells = cells_of(jobs)
    blocking = blocking_cells(jobs)
    failed = failed_cells(jobs)
    if not cells:
        return Verdict(False, (
            f"the run's job listing has no cell of the full test matrix, which runs {size}"
        ), failed)
    if len(cells) != size:
        return Verdict(False, (
            f"the run's job listing has {len(cells)} cells of the full test matrix, and"
            f" the matrix runs {size}"
        ), failed)
    short = sorted(
        f"{job.name} {job.conclusion or f'{job.status}, with no conclusion'}"
        for job in blocking if job.conclusion != "success"
    )
    if short:
        return Verdict(False, (
            "the run's job listing has cells of the full test matrix that did not"
            f" pass in this attempt: {', '.join(short)}"
        ), failed)
    if not blocking:
        return Verdict(False, "the run's job listing has no blocking cell of the full test matrix", failed)
    return Verdict(True, (
        "the full test matrix ran and every blocking cell passed in this attempt"
        f" of the run: {len(blocking)} cells, the advisory cell apart"
    ), failed)


def gate(
    plan: str, release: str, matrix: str, size: str, listing: Callable[[], Sequence[Job]],
) -> Verdict:
    """`decide`'s verdict and, wherever the matrix ran, the listing's too:
    the gate passes only when both do.  `size` is the matrix's size as the
    `test` job states it, and it and `listing` are read only there, as are
    the watched cells that failed, which the verdict does not read."""
    passed, why = decide(plan, release, matrix)
    if plan != "success" or matrix not in _RAN:
        return Verdict(passed, why, ())
    try:
        jobs = listing()
    except ListingError as exc:
        if passed:
            why = (
                f"the run's job listing cannot be read, so whether every cell of the"
                f" full test matrix passed is not known: {exc}"
            )
        return Verdict(False, why, ())
    watched = failed_watched(jobs)
    try:
        listed = judge(jobs, matrix_size(size))
    except ListingError as exc:
        listed = Verdict(False, (
            f"whether the run's job listing holds every cell of the full test matrix"
            f" is not known: {exc}"
        ), failed_cells(jobs))
    if not passed:
        return Verdict(False, why, listed.failed, watched)
    return listed._replace(watched=watched)


def main(list_jobs: Callable[[str, str], Sequence[Job]] | None = None) -> int:
    env = os.environ
    read = gh_list_jobs if list_jobs is None else list_jobs
    verdict = gate(
        env.get("PLAN_RESULT", "<unset>"),
        env.get("RELEASE", "<unset>"),
        env.get("TEST_RESULT", "<unset>"),
        env.get("MATRIX_CELLS", ""),
        lambda: read(env.get("GITHUB_RUN_ID", ""), env.get("GITHUB_RUN_ATTEMPT", "")),
    )
    output = env.get("GITHUB_OUTPUT")
    if output and (verdict.failed or verdict.watched):
        with open(output, "a", encoding="utf-8") as handle:
            if verdict.failed:
                handle.write(f"failed={json.dumps(list(verdict.failed))}\n")
            if verdict.watched:
                handle.write(f"watched={json.dumps(list(verdict.watched))}\n")
    print(verdict.why if verdict.passed else f"::error::{verdict.why}")
    if verdict.watched:
        print(f"::warning::watched cells that failed, which block nothing: {', '.join(verdict.watched)}")
    return 0 if verdict.passed else 1


if __name__ == "__main__":
    sys.exit(main())
