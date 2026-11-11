"""The mark every mutation-lane self-test that starts mutmut's engine carries.

``starts_the_engine(seconds)`` skips the test on macOS, where the engine's
forked workers abort under the platform's fork safety (and leave a crash
report), and, where pytest-timeout is installed (the ``mutation`` extra the
lanes install), fails it after ``seconds`` rather than let it hang the job:
the lane's job runs the self-tests under a 55-minute timeout, the nightly
sweep's under 330 minutes, and a test that hung there once cost the job
(#1838).
"""

from __future__ import annotations

import importlib.util
import sys
from collections.abc import Callable
from typing import Any, TypeVar

import pytest

F = TypeVar("F", bound=Callable[..., Any])

#: Why an engine test does not run on macOS.
DARWIN_REASON = ("starts mutmut's engine, whose forked workers abort under macOS fork safety; "
                 "it runs on Linux, in the mutation lanes")


def starts_the_engine(seconds: int) -> Callable[[F], F]:
    """Skip on macOS; fail after ``seconds`` where pytest-timeout is there."""
    marks = [pytest.mark.skipif(sys.platform == "darwin", reason=DARWIN_REASON)]
    if importlib.util.find_spec("pytest_timeout") is not None:
        marks.append(pytest.mark.timeout(seconds))

    def apply(test: F) -> F:
        for mark in marks:
            test = mark(test)
        return test

    return apply
