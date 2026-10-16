"""Keeps a test that starts a Python or ``vera`` process out of mutmut's oracle.

A pytest plugin ``[tool.mutmut]`` loads (``-p tests.mutation_oracle``), so it
runs inside mutmut's copy of the tree, where each mutated module holds a copy
of each mutated function for each of its mutants: a mutated
``TypeEnv._register_builtins`` makes ``vera/environment.py`` 31.7 MB where it
is 49 KB.  A process a test starts there compiles every such module afresh
(``vera check`` on a one-line program takes 2.0 s against 0.5 s), and what it
runs records nothing in mutmut's stats pass, so the test can never be a
mutant's oracle; it only costs the run time, and on a slow runner its own
timeout.

So the plugin skips a test at the moment it starts a Python or ``vera``
process, where the subprocess census (``tests/subprocess_census.py``) counts
one, and appends the test's node id to the file ``MUTATION_ORACLE_SKIPS``
names, which the mutation lane (``scripts/mutate_diff.py``) reports.  Any
other process, and every process outside a test (mutmut's own), starts as
usual.
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
        path = os.environ.get(SKIPS_ENV)
        if path:
            with open(path, "a", encoding="utf-8") as fh:
                fh.write(_current + "\n")
        pytest.skip(REASON)
    _original_init(self, *args, **kwargs)


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
def pytest_runtest_protocol(item: pytest.Item, nextitem: pytest.Item | None) -> Generator[None, Any, Any]:
    """A process started from a test's setup, call or teardown is the test's."""
    global _current
    _current = item.nodeid
    try:
        return (yield)
    finally:
        _current = None
