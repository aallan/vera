"""Shared pytest fixtures.

Scrubs the inherited environment variables that would change what the suite
measures (``VERA_Z3_TIMEOUT_MS``) or which repository its git commands act on
(``GIT_*``), and provides opt-in JavaScript coverage collection for the
browser runtime.  Set ``VERA_JS_COVERAGE=1`` to enable V8 coverage during
``test_browser.py``.
"""

from __future__ import annotations

import os
import subprocess

import pytest


@pytest.fixture(scope="session", autouse=True)
def _default_z3_budget():  # type: ignore[no-untyped-def]
    """Scrub an inherited ``VERA_Z3_TIMEOUT_MS`` from every test (#1350).

    The budget is resolved from the environment only when no caller passes
    one (``vera/smt.py::resolve_timeout_ms``), so a developer who exports the
    variable silently re-measures every tier assertion that does NOT name its
    own budget: at ``VERA_Z3_TIMEOUT_MS=1`` the corpus pin in
    ``test_verifier_adt_decreases.py`` reports 408 statically instead of 411,
    and the eccentricity pin in ``test_examples_ephemeris.py`` fails too.  An
    explicit ``timeout_ms=`` outranks the environment, so the budget-
    parametrised cells in that same file are unaffected either way — which is
    why one test there fails under a hostile value rather than all of them.
    The
    documented premise those tests carry — and that TESTING.md states for the
    published totals — is "the default budget, with the variable unset", so
    the scrub reproduces it rather than approximating it with a hardcoded
    10_000 that would keep passing if the default itself moved.

    Autouse and suite-wide rather than per-test: the exposure is every test
    that asserts a tier, which is not a list worth maintaining.  Tests that
    deliberately exercise the variable set it through their own
    ``monkeypatch`` AFTER this fixture has run, so they are unaffected —
    ``test_verifier_budget.py`` covers both directions.

    SESSION-scoped, which is load-bearing rather than tidy.  A
    function-scoped autouse fixture runs AFTER any module-scoped fixture it
    shares a test with, and ``test_examples_ephemeris.py`` verifies the
    example inside a module-scoped ``obligations`` fixture — so a
    function-scoped scrub let the hostile value through to exactly the tests
    it was written to protect (measured: `tier3_unguarded` binds and a
    `timeout` on `wrap_deg` at ``VERA_Z3_TIMEOUT_MS=1``).  Session scope runs
    before every other fixture, so it needs its own ``MonkeyPatch`` — the
    injected ``monkeypatch`` is function-scoped and cannot be requested here.

    ``_scrub_inherited_git_env`` below clears inherited ``GIT_*`` the same
    way.
    """
    mp = pytest.MonkeyPatch()
    mp.delenv("VERA_Z3_TIMEOUT_MS", raising=False)
    yield
    mp.undo()


@pytest.fixture(scope="session", autouse=True)
def _scrub_inherited_git_env():  # type: ignore[no-untyped-def]
    """Clear every inherited ``GIT_*`` variable, once, for the whole suite.

    Under pre-commit, git exports ``GIT_DIR`` and ``GIT_INDEX_FILE`` for the
    repository being committed (githooks(5)), and git honours them ahead of
    a subprocess's ``cwd`` or ``-C``.  A test that runs git against a
    repository of its own therefore acts on the developer's instead.  A
    ``git init`` re-initialises it, and from a linked worktree, whose gitdir
    does not end in ``.git``, marks the shared repository
    ``core.bare = true``: every worktree of it then fails with "this
    operation must be run in a work tree" until the setting is reset (PR
    #1484).  Clearing the variables here covers every test, including one
    written without knowing this, and ``test_git_hermetic.py`` proves it
    against a decoy repository.

    Session-scoped for the reason ``_default_z3_budget`` gives: it runs
    before every other fixture.  A test that exercises the variables sets
    them through its own ``monkeypatch`` after this has run.
    """
    mp = pytest.MonkeyPatch()
    for name in [k for k in os.environ if k.startswith("GIT_")]:
        mp.delenv(name, raising=False)
    yield
    mp.undo()


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
        try:
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
                timeout=120,
            )
        except subprocess.TimeoutExpired:
            print("WARNING: JS coverage report timed out after 120s")
