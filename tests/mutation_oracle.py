"""Keeps a test that starts a Python or ``vera`` process out of mutmut's oracle.

A pytest plugin ``[tool.mutmut]`` loads (``-p tests.mutation_oracle``), so it
runs inside mutmut's copy of the tree, where each mutated module holds a copy
of each mutated function for each of its mutants: a mutated
``TypeEnv._register_builtins`` makes ``vera/environment.py`` 33.6 MB where it
is 49 KB.  A process a test starts there compiles every such module afresh
(``vera check`` on a one-line program takes 2.3 s against 0.4 s), and what it
runs records nothing in mutmut's stats pass, so the test can never be a
mutant's oracle; it only costs the run time, and on a slow runner its own
timeout.

So the plugin skips a test at the moment it starts a Python or ``vera``
process, where the subprocess census (``tests/subprocess_census.py``) counts
one, and appends the test's node id to the file ``MUTATION_ORACLE_SKIPS``
names, which the mutation lane (``scripts/mutate_diff.py``) reports.  Any
other process, and every process outside a test (mutmut's own), starts as
usual.

The skipped test is out of the oracle entirely.  mutmut's stats pass records,
at each test's teardown and whatever its outcome, the functions the test
reached, and runs a mutant against the tests recorded for its function; a
test skipped after it called a mutated function would be run against that
function's mutants, skip again, and leave each one a survivor.  So when the
test ends, the plugin takes it out of that record (mutmut 3.8's
``state().tests_by_mangled_function_name``), and a function only skipped
tests reach has its mutants ``no tests``.  A mutmut whose record is not
there stops the stats pass rather than leave the test in it.
"""

from __future__ import annotations

import os
import subprocess
import sys
from collections.abc import Generator
from pathlib import Path
from typing import Any

import pytest

#: The variable naming the file each skipped test's node id is appended to.
SKIPS_ENV = "MUTATION_ORACLE_SKIPS"

#: Why the test is skipped, as its skip reason.
REASON = ("starts a Python or vera process, which inside mutmut's copy runs the mutated "
          "modules afresh and records nothing for the stats pass")

_current: str | None = None
_original_init: Any = None
#: The tests this process has skipped, by node id.
_skipped: set[str] = set()


def _starts_the_compiler(args: Any) -> bool:
    """Whether a process's command runs Python or ``vera``."""
    if isinstance(args, (str, bytes, os.PathLike)):
        words = os.fsdecode(args).split()
    else:
        words = [os.fsdecode(a) for a in (args or [])]
    if not words:
        return False
    first = words[0]
    name = Path(first).name.lower()
    return first == sys.executable or name.startswith("python") or name in ("vera", "vera.exe")


def _skipping_init(self: subprocess.Popen[Any], *args: Any, **kwargs: Any) -> None:
    command = args[0] if args else kwargs.get("args")
    if _current is not None and _starts_the_compiler(command):
        pytest.skip(REASON)
    _original_init(self, *args, **kwargs)


def _record(nodeid: str) -> None:
    path = os.environ.get(SKIPS_ENV)
    if path:
        with open(path, "a", encoding="utf-8") as fh:
            fh.write(nodeid + "\n")


def _forget(nodeid: str) -> None:
    """Take a skipped test out of mutmut's record of the tests that reach
    each function, which only its stats pass writes."""
    if os.environ.get("MUTANT_UNDER_TEST") != "stats":
        return
    try:
        from mutmut.state import state
    except ImportError:
        pytest.exit("tests/mutation_oracle.py: mutmut.state is not there (mutmut 3.8 holds the "
                    "record of the tests that reach each function in it), so a skipped test "
                    "cannot be taken out of that record", returncode=3)
    names = {nodeid, nodeid.removeprefix("mutants/")}
    for tests in state().tests_by_mangled_function_name.values():
        tests.difference_update(names)


def pytest_configure(config: pytest.Config) -> None:
    global _original_init
    if _original_init is None:
        _original_init = subprocess.Popen.__init__
        subprocess.Popen.__init__ = _skipping_init  # type: ignore[method-assign]


def pytest_unconfigure(config: pytest.Config) -> None:
    global _original_init
    if _original_init is not None:
        subprocess.Popen.__init__ = _original_init  # type: ignore[method-assign]
        _original_init = None


@pytest.hookimpl(wrapper=True)
def pytest_runtest_makereport(item: pytest.Item, call: pytest.CallInfo[None]) -> Generator[None, Any, Any]:
    """A test is the plugin's when any phase ends in its skip: one that
    started the process itself, or one handed the skip a fixture cached."""
    report = yield
    excinfo = call.excinfo
    if (excinfo is not None and isinstance(excinfo.value, pytest.skip.Exception)
            and excinfo.value.msg == REASON):
        _skipped.add(item.nodeid)
    return report


@pytest.hookimpl(wrapper=True)
def pytest_runtest_protocol(item: pytest.Item, nextitem: pytest.Item | None) -> Generator[None, Any, Any]:
    """A process started from a test's setup, call or teardown is the
    test's; a test skipped for one is recorded, and leaves mutmut's record
    once mutmut's own teardown hook has written it."""
    global _current
    _current = item.nodeid
    try:
        return (yield)
    finally:
        _current = None
        if item.nodeid in _skipped:
            _record(item.nodeid)
            _forget(item.nodeid)
