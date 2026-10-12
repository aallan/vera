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
"""

from __future__ import annotations

import os
import sys

_RESULTS = frozenset({"success", "failure", "cancelled", "skipped"})
_RELEASES = frozenset({"true", "false", ""})


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


def main() -> int:
    passed, why = decide(
        os.environ.get("PLAN_RESULT", "<unset>"),
        os.environ.get("RELEASE", "<unset>"),
        os.environ.get("TEST_RESULT", "<unset>"),
    )
    print(why if passed else f"::error::{why}")
    return 0 if passed else 1


if __name__ == "__main__":
    sys.exit(main())
