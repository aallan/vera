"""A test runs under the budget its marker names (#1670).

``tests/pipeline.py`` ends the process when a stage call is still running at
the end of its budget, 120 s when the call names none.  A test whose own work
legitimately takes longer names a budget with ``@pytest.mark.budget(seconds)``,
and a ``stress``-marked test that names none runs under 600 s:
``tests/conftest.py`` holds the whole test to it, so every stage call in the
test that passes no ``budget_s=`` runs under the test's budget, and a call
that passes one keeps its own.

Each cell runs one test of ``_CELLS`` in a child pytest, under pytest-xdist
and without it, with the default lowered to 0.5 s and a stage call that takes
1.5 s.  Unmarked, the call is ended at the default, and inside a ``budget(5)``
test the call that passes ``budget_s=0.5`` is ended at its own budget: either
way the run names the test.  Marked ``budget(5)``, or ``stress``, the test
passes.  Each child test first asserts the budget in force when it starts, to
within a second: none, 5 s, or 600 s for the ``stress`` test.  The bound
allows the float rounding of a read in the tick the deadline was set (#1689).
"""

from __future__ import annotations

import os
import re
import subprocess
import sys
import time
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parent.parent

#: The child's tests: one stage call that takes 1.5 s, under a default budget
#: of 0.5 s, in each place a budget can come from.  Each first asserts the
#: budget in force when it starts, within a second: none, 5 s or 600 s.
_CELLS = '''\
import time

import pytest

from tests import pipeline

_SOURCE = (
    "public fn f(@Int -> @Int)\\n  requires(true)\\n  ensures(true)\\n"
    "  effects(pure)\\n{\\n  @Int.0\\n}\\n")

_parse_tree = pipeline._parse_tree


def _slow_parse_tree(*args, **kwargs):
    time.sleep(1.5)
    return _parse_tree(*args, **kwargs)


def _parse_slowly(monkeypatch, in_force, **budget):
    left = (pipeline._deadlines[-1] - time.monotonic()
            if pipeline._deadlines else None)
    if in_force is None:
        assert left is None, left
    else:
        # Read in the tick the deadline was set, left is (t + s) - t, which
        # rounds above s by up to an ulp of the deadline (#1689).
        assert left is not None and in_force - 1 < left <= in_force + 1e-6, left
    monkeypatch.setattr(pipeline, "DEFAULT_BUDGET_S", 0.5)
    monkeypatch.setattr(pipeline, "_parse_tree", _slow_parse_tree)
    assert pipeline.parse(_SOURCE, **budget).ok


def test_unmarked(monkeypatch):
    _parse_slowly(monkeypatch, None)


@pytest.mark.budget(5)
def test_marked_budget(monkeypatch):
    _parse_slowly(monkeypatch, 5)


@pytest.mark.stress
def test_marked_stress(monkeypatch):
    _parse_slowly(monkeypatch, 600)


@pytest.mark.budget(5)
def test_own_budget_inside_a_marked_test(monkeypatch):
    _parse_slowly(monkeypatch, 5, budget_s=0.5)
'''


@pytest.mark.parametrize("runner", [
    ("-n", "1"),
    ("-p", "no:xdist"),
], ids=["xdist", "plain"])
@pytest.mark.parametrize(("test", "ended"), [
    ("test_unmarked", True),
    ("test_marked_budget", False),
    ("test_marked_stress", False),
    ("test_own_budget_inside_a_marked_test", True),
], ids=["unmarked", "budget", "stress", "own-budget"])
def test_a_test_runs_under_the_budget_its_marker_names(
    test: str, ended: bool, runner: tuple[str, ...], tmp_path: Path,
) -> None:
    """The child loads the repository's conftest, as every run of the suite
    does, and reads no ini file, so the default `-m 'not stress'` deselects
    nothing; a test that passes is held to `1 passed`, which a deselected
    one is not.  A call ended at 0.5 s writes the watchdog's header for that
    budget, and its traceback names the test; under pytest-xdist the report
    names it too."""
    test_file = tmp_path / "test_slow_stage.py"
    test_file.write_text(_CELLS, encoding="utf-8")
    env = {name: value for name, value in os.environ.items()
           if not name.startswith(("GIT_", "PYTEST_", "COV_CORE_"))}
    proc = subprocess.run(
        [sys.executable, "-m", "pytest", "-q", "-p", "no:cacheprovider",
         *runner, "-p", "tests.conftest", "--rootdir", str(tmp_path),
         f"{test_file}::{test}"],
        capture_output=True, text=True, encoding="utf-8", errors="replace",
        cwd=ROOT, env=env, timeout=120, check=False,
    )
    output = proc.stdout + proc.stderr
    if not ended:
        assert proc.returncode == 0, output
        assert re.search(r"^1 passed\b", output, re.M), output
        assert "Timeout (" not in output, output
        return
    assert "Timeout (0:00:00.500000)!" in output, output
    assert "in _slow_parse_tree" in output, output
    assert re.search(rf"line \d+ in {re.escape(test)}$", output, re.M), output
    if runner[0] == "-n":
        assert f"crashed while running 'test_slow_stage.py::{test}'" in output, output
    else:
        assert proc.returncode == 1, output


#: A ``time.monotonic()`` sample whose deadline rounds up: ``(t + 5) - t``
#: is ``5.000000000000057``, the value the Windows runner reported (#1689).
#: ``t + 5`` crosses into the next binade there (512), so its last bit of
#: ``t`` is rounded away.
_ROUNDING_SAMPLE = 507.007


def test_the_bound_admits_a_read_in_the_tick_the_deadline_was_set(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """The child's first assertion reads the budget left as
    ``deadline - time.monotonic()``, where the deadline was
    ``time.monotonic() + seconds``.  On a clock that has not advanced
    between the two reads, as Windows' often has not, that is
    ``(t + 5) - t``, which floating point can round above 5; the bound
    allows it.  The child's own assertion runs here, in process, with its
    first clock read being the deadline's sample and its stage at the
    parser's own speed."""
    from tests import pipeline

    assert (_ROUNDING_SAMPLE + 5) - _ROUNDING_SAMPLE > 5
    cells: dict[str, object] = {}
    exec(compile(_CELLS, "test_slow_stage.py", "exec"), cells)
    cells["_slow_parse_tree"] = pipeline._parse_tree
    real = time.monotonic
    first = [True]

    def clock() -> float:
        if first[0]:
            first[0] = False
            return _ROUNDING_SAMPLE
        return real()

    monkeypatch.setattr(pipeline, "_deadlines", [_ROUNDING_SAMPLE + 5])
    monkeypatch.setattr(time, "monotonic", clock)
    parse_slowly = cells["_parse_slowly"]
    assert callable(parse_slowly)
    parse_slowly(monkeypatch, 5)
