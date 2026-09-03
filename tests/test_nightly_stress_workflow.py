"""Contract test for #1328: the nightly stress workflow's marker
selection must actually collect every ``@pytest.mark.stress`` test,
not just whichever file the invocation happens to name.

Regression shape: ``.github/workflows/nightly-stress.yml`` ran
``pytest -v -m stress tests/test_stress.py`` — the ``-m stress``
marker selection was silently narrowed by the trailing file argument,
so ``TestHostHandleReclamation573``'s 10 parametrised instances in
``tests/test_codegen_gc_reclamation.py`` (same ``stress`` marker, same
intended lane per the class's own docstring) were never collected by
any automated lane: not the per-PR suite (deselected by
``addopts = "-m 'not stress'"``), and not the nightly workflow either.

This module replays the WORKFLOW FILE'S OWN command in
``--collect-only`` mode — extracted from the live YAML text, not a
hand-copied belief about it — so a future re-narrowing of the
invocation reds this test instead of silently losing coverage again.

The replay is VERBATIM (``shlex.split`` on the extracted command, with
only display-only verbosity flags stripped), not a reconstruction from
a parsed ``-m``/paths pair.  An earlier version of this module did
reconstruct the argv from parsed pieces, which silently discarded any
OTHER flag on the command line — an ``--ignore=...`` or ``--deselect``
added to the workflow could re-exclude the reclamation battery in a
differently-shaped command while a reconstruction-based comparison
stayed green, because it never looked at those tokens in the first
place.  Replaying the actual argv closes that gap: whatever the
workflow would really pass to pytest is what gets collected here.
"""

from __future__ import annotations

import re
import shlex
import subprocess
import sys
import tomllib
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parent.parent
WORKFLOW = ROOT / ".github" / "workflows" / "nightly-stress.yml"
PYPROJECT = ROOT / "pyproject.toml"

# The 10 parametrised instances #1328 names as the coverage this lane
# must reach.  Listed explicitly (not just a count) so a renamed or
# removed test method reds this assertion by name, not just by count.
_EXPECTED_RECLAMATION_TESTS = [
    "test_map_chain_reclaims_transients",
    "test_json_object_map_bucket_path_at_scale",
    "test_map_value_lookup_after_gc_pressure",
    "test_set_chain_reclaims_transients",
    "test_set_value_correct_after_gc_pressure",
    "test_decimal_chain_reclaims_transients",
    "test_json_only_module_includes_wrap_table",
    "test_html_only_module_includes_wrap_table",
    "test_register_wrapper_has_compaction_slow_path",
    "test_decimal_value_correct_after_gc_pressure",
]

_RUN_STEP = re.compile(
    r"name:\s*Run stress tests\s*\n(?:\s*#.*\n)*\s*run:\s*(.+)"
)

# Flags that only affect DISPLAY, not what gets collected.  Stripped
# before appending our own `--collect-only -q`: leaving a `-v` in
# place makes `--collect-only` print an indented `<Function ...>` tree
# instead of flat `path::Class::test` node IDs, so every membership
# check below would silently compare against an empty set instead of
# failing loudly.
_VERBOSITY_FLAGS = frozenset({"-v", "-vv", "-vvv", "-q", "-qq"})


def _extract_stress_run_command() -> str:
    """The literal ``run:`` command of nightly-stress.yml's "Run stress
    tests" step, pulled from the workflow text itself so this test
    measures what CI actually executes rather than a hand-copied
    string that could drift from it (the exact drift #1328 was)."""
    text = WORKFLOW.read_text(encoding="utf-8")
    match = _RUN_STEP.search(text)
    assert match is not None, (
        "nightly-stress.yml: could not find the 'Run stress tests' "
        "step's `run:` line — reword this test with the workflow"
    )
    return match.group(1).strip()


def _extract_marker(command: str) -> str:
    """Just the ``-m <expr>`` marker value, for asserting the workflow
    still selects on the ``stress`` marker specifically.  Deliberately
    does NOT also characterise "the paths" as a separate value —
    that reconstruction is exactly what silently drops flags like
    ``--ignore``/``--deselect``/``-k``; see ``_workflow_collect_argv``
    for the verbatim replay used for actual collection below."""
    tokens = shlex.split(command)
    assert tokens and tokens[0] == "pytest", (
        f"nightly-stress.yml: not a pytest invocation: {command!r}"
    )
    for i, tok in enumerate(tokens):
        if tok == "-m":
            assert i + 1 < len(tokens), f"'-m' with no argument in: {command!r}"
            return tokens[i + 1]
    raise AssertionError(
        f"nightly-stress.yml: no `-m` marker expression in: {command!r}"
    )


def _workflow_collect_argv(command: str) -> list[str]:
    """The workflow's own argv, VERBATIM apart from verbosity flags —
    every other flag (``--ignore``, ``--deselect``, ``-k``, explicit
    paths or their absence, ...) is preserved exactly as the workflow
    would pass it to pytest."""
    tokens = shlex.split(command)
    assert tokens and tokens[0] == "pytest", (
        f"nightly-stress.yml: not a pytest invocation: {command!r}"
    )
    return [tok for tok in tokens[1:] if tok not in _VERBOSITY_FLAGS]


def _collect_ids(argv_after_pytest: list[str]) -> set[str]:
    """Flat ``path::Class::test[params]`` node IDs a
    ``pytest <argv_after_pytest> --collect-only -q`` run would list.

    No explicit path argument is required: a bare ``-m stress`` with
    no path is a legitimate invocation that falls back to pyproject's
    own ``testpaths`` default, and must be collectable here exactly
    like an explicit ``tests/`` would be.
    """
    result = subprocess.run(
        [
            sys.executable, "-m", "pytest",
            *argv_after_pytest,
            "--collect-only", "-q",
        ],
        cwd=ROOT,
        capture_output=True,
        text=True,
        encoding="utf-8",
        check=False,
    )
    # A nonexistent path or bad flag on the replayed command can make
    # pytest exit non-zero while still printing SOME valid node IDs on
    # stdout (e.g. a bad `--ignore=` target with other paths still
    # resolving) — collecting fewer than intended is silent unless the
    # exit status is checked too, and every assertion below is a set
    # comparison that a too-small collection could still satisfy.
    assert result.returncode == 0, (
        "pytest collection failed while replaying "
        f"{['pytest', *argv_after_pytest, '--collect-only', '-q']!r}:\n"
        f"{result.stderr}"
    )
    return {
        line.strip()
        for line in result.stdout.splitlines()
        if "::" in line
    }


def _canonical_testpaths() -> list[str]:
    """pyproject.toml's ``[tool.pytest.ini_options] testpaths`` — the
    project's own definition of "everywhere tests live", single-
    sourced rather than assumed to be ``tests/``."""
    with PYPROJECT.open("rb") as f:
        config = tomllib.load(f)
    testpaths = config["tool"]["pytest"]["ini_options"]["testpaths"]
    assert testpaths, "pyproject.toml: empty [tool.pytest.ini_options] testpaths"
    return list(testpaths)


# ---------------------------------------------------------------------
# Module-scoped fixtures: each `--collect-only` replay walks the whole
# ~12,000-item test tree, so collecting the workflow's selection (and
# the canonical one) ONCE per test session and sharing the result
# across every cell below keeps this module's cost to two subprocess
# calls total rather than one per test method.
# ---------------------------------------------------------------------


@pytest.fixture(scope="module")
def workflow_command() -> str:
    return _extract_stress_run_command()


@pytest.fixture(scope="module")
def workflow_marker(workflow_command: str) -> str:
    return _extract_marker(workflow_command)


@pytest.fixture(scope="module")
def workflow_collected_ids(workflow_command: str) -> set[str]:
    return _collect_ids(_workflow_collect_argv(workflow_command))


@pytest.fixture(scope="module")
def canonical_collected_ids() -> set[str]:
    return _collect_ids(["-m", "stress", *_canonical_testpaths()])


def test_workflow_collect_argv_preserves_a_non_verbosity_flag() -> None:
    """Pure-unit companion to the class below's verbatim-replay tests:
    re-introducing the old marker+paths RECONSTRUCTION inside this
    helper would silently drop any flag the reconstruction does not
    know about, while every test below stays green on the unmutated
    workflow.  A flag that is not a verbosity flag must survive."""
    argv = _workflow_collect_argv(
        "pytest -v -m stress --deselect=tests/test_x.py::test_y tests/"
    )
    assert "--deselect=tests/test_x.py::test_y" in argv


class TestNightlyStressLaneCollection1328:
    """The nightly stress workflow's marker selection must collect
    every ``@pytest.mark.stress`` instance repo-wide, not just the
    ones in whichever file the invocation happens to name."""

    def test_workflow_marker_is_stress(self, workflow_marker: str) -> None:
        """The workflow must still select on the ``stress`` marker
        specifically.  The canonical comparison below is only
        meaningful against that marker: a silent rename to some OTHER
        marker that coincidentally still selected exactly the
        reclamation battery would otherwise compare that narrower
        selection against itself and pass, without noticing the rest
        of the `stress` domain (`tests/test_stress.py`'s 16 instances)
        fell out."""
        assert workflow_marker == "stress", (
            f"nightly-stress.yml's stress step no longer selects on "
            f"the `stress` marker (found {workflow_marker!r}) — the "
            f"canonical comparison below is only meaningful against "
            f"that literal marker"
        )

    def test_workflow_command_not_narrowed_to_test_stress_py_alone(
        self, workflow_command: str
    ) -> None:
        """The extracted command's own argv must not be exactly the
        #1328 regression shape — ``-m stress tests/test_stress.py``
        and nothing else."""
        argv = _workflow_collect_argv(workflow_command)
        assert argv != ["-m", "stress", "tests/test_stress.py"], (
            f"nightly-stress.yml's stress run command is file-scoped "
            f"to test_stress.py again: {workflow_command!r} — this is "
            f"the #1328 regression shape"
        )

    def test_workflow_selection_matches_canonical_stress_selection(
        self,
        workflow_collected_ids: set[str],
        canonical_collected_ids: set[str],
    ) -> None:
        """The workflow's own command — replayed VERBATIM, not
        reconstructed from a parsed marker+paths pair — must collect
        the same node IDs as the canonical ``-m stress`` selection
        over pyproject's own ``testpaths``.  No file-scoping, and no
        other flag (``--ignore``, ``--deselect``, ``-k``, ...) that
        would silently drop a stress-marked class, wherever it lives
        in the tree."""
        assert canonical_collected_ids, (
            "canonical `-m stress` selection over testpaths collected "
            "nothing — this test is broken, not the workflow"
        )
        missing = canonical_collected_ids - workflow_collected_ids
        assert not missing, (
            "nightly-stress.yml's own command collects fewer tests "
            "than the canonical `-m stress` selection over "
            f"{_canonical_testpaths()!r} — missing: {sorted(missing)}"
        )

    def test_workflow_selection_collects_host_handle_reclamation_battery(
        self,
        workflow_collected_ids: set[str],
        canonical_collected_ids: set[str],
    ) -> None:
        """#1328's own repro, verbatim: replay the workflow's command
        in collect-only mode and assert all 10 named
        ``TestHostHandleReclamation573`` instances are collected
        EXACTLY (full node-ID equality, not "some node ID contains
        this method's name" — a future parametrised variant of one of
        these methods would otherwise still satisfy a substring check
        with only some of its instances present).  Also compares the
        FULL set of collected reclamation node IDs against the
        canonical `-m stress` selection's own reclamation subset, so
        an instance ADDED to the class later is caught too, not just
        one of today's ten going missing."""
        expected_ids = {
            f"tests/test_codegen_gc_reclamation.py::"
            f"TestHostHandleReclamation573::{name}"
            for name in _EXPECTED_RECLAMATION_TESTS
        }
        missing = expected_ids - workflow_collected_ids
        assert not missing, (
            "nightly-stress.yml's stress selection does not collect "
            f"these TestHostHandleReclamation573 instances: {sorted(missing)}"
        )

        class_marker = "::TestHostHandleReclamation573::"
        canonical_class_ids = {
            node_id for node_id in canonical_collected_ids
            if class_marker in node_id
        }
        assert len(canonical_class_ids) == len(_EXPECTED_RECLAMATION_TESTS), (
            "the canonical `-m stress` selection's own "
            "TestHostHandleReclamation573 subset no longer has "
            f"{len(_EXPECTED_RECLAMATION_TESTS)} instances "
            f"({len(canonical_class_ids)} found) — update "
            "_EXPECTED_RECLAMATION_TESTS to match the class"
        )
        workflow_class_ids = {
            node_id for node_id in workflow_collected_ids
            if class_marker in node_id
        }
        assert workflow_class_ids == canonical_class_ids, (
            "nightly-stress.yml's stress selection's "
            "TestHostHandleReclamation573 subset does not match the "
            "canonical `-m stress` selection's — "
            f"missing: {sorted(canonical_class_ids - workflow_class_ids)}, "
            f"extra: {sorted(workflow_class_ids - canonical_class_ids)}"
        )
