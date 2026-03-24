"""Shared pytest fixtures.

Provides opt-in JavaScript coverage collection for the browser runtime.
Set ``VERA_JS_COVERAGE=1`` to enable V8 coverage during ``test_browser.py``.
"""

from __future__ import annotations

import os
import subprocess

import pytest


@pytest.fixture(scope="session", autouse=True)
def _js_coverage_dir(tmp_path_factory: pytest.TempPathFactory):  # type: ignore[no-untyped-def]
    """Collect V8 coverage when ``VERA_JS_COVERAGE=1`` is set.

    Every ``node`` subprocess inherits ``NODE_V8_COVERAGE`` and writes
    raw V8 coverage JSON.  At session teardown, ``npx c8 report``
    converts the accumulated data to a human-readable text report.
    """
    if not os.environ.get("VERA_JS_COVERAGE"):
        yield
        return

    cov_dir = tmp_path_factory.mktemp("v8-coverage")
    os.environ["NODE_V8_COVERAGE"] = str(cov_dir)

    yield

    # Generate text report at session end.
    if any(cov_dir.iterdir()):
        subprocess.run(
            [
                "npx",
                "c8",
                "report",
                f"--temp-directory={cov_dir}",
                "--reporter=text",
                "--src=vera/browser/",
            ],
            check=False,
        )
