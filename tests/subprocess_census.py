"""Counts the processes each test starts, for the scorecard's subprocess share.

A pytest plugin, loaded by name on the run whose junit file
``scripts/render_status.py --junit`` reads::

    python -m pytest -n auto -p tests.subprocess_census --junitxml=PATH

``python -m`` puts the repository root on the path, so pytest can import the
plugin before it reads a conftest.  Every test then carries a
``subprocesses`` property in the junit file: the number of processes its
setup, call and teardown started, counted where ``subprocess.Popen`` builds
one, which ``subprocess.run`` and its siblings and asyncio's subprocess
transport all do.  A test whose ``Popen`` is a stand-in starts none.  Every
test carries the property, a zero too, so a file written without the plugin
has none, and the reader refuses it rather than read its share as zero
(``scripts/scorecard.py``, ``junit_values``).

A module-scoped fixture's process is counted in the test that set it up.
Under pytest-xdist each worker counts its own tests, and the controller
writes the properties its workers report.
"""

from __future__ import annotations

import subprocess
from collections.abc import Generator
from typing import Any

import pytest

#: The junit property, as scripts/scorecard.py reads it.
PROPERTY = "subprocesses"

_started = 0
_original_init: Any = None


def _counting_init(self: subprocess.Popen[Any], *args: Any, **kwargs: Any) -> None:
    global _started
    _started += 1
    _original_init(self, *args, **kwargs)


def pytest_configure(config: pytest.Config) -> None:
    global _original_init
    if _original_init is None:
        _original_init = subprocess.Popen.__init__
        subprocess.Popen.__init__ = _counting_init  # type: ignore[method-assign]


def pytest_unconfigure(config: pytest.Config) -> None:
    global _original_init
    if _original_init is not None:
        subprocess.Popen.__init__ = _original_init  # type: ignore[method-assign]
        _original_init = None


@pytest.hookimpl(tryfirst=True)
def pytest_runtest_protocol(item: pytest.Item, nextitem: pytest.Item | None) -> None:
    """A test's count starts at its own setup."""
    global _started
    _started = 0


@pytest.hookimpl(wrapper=True)
def pytest_runtest_makereport(
    item: pytest.Item, call: pytest.CallInfo[None]
) -> Generator[None, Any, Any]:
    """The teardown report is the one the junit file reads properties from,
    so the count goes onto the test before it is made."""
    if call.when == "teardown":
        item.user_properties.append((PROPERTY, _started))
    return (yield)
