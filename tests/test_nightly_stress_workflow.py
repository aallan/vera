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
"""

from __future__ import annotations

import re
import subprocess
import sys
import tomllib
from pathlib import Path

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


def _parse_pytest_selection(command: str) -> tuple[str, list[str]]:
    """Pull the ``-m <expr>`` marker and the positional path arguments
    out of a ``pytest ...`` command line, ignoring display-only flags
    (``-v``, ``-q``, ...) that don't affect what gets collected."""
    tokens = command.split()
    assert tokens and tokens[0] == "pytest", (
        f"nightly-stress.yml: not a pytest invocation: {command!r}"
    )
    marker: str | None = None
    paths: list[str] = []
    i = 1
    while i < len(tokens):
        tok = tokens[i]
        if tok == "-m":
            assert i + 1 < len(tokens), f"'-m' with no argument in: {command!r}"
            marker = tokens[i + 1]
            i += 2
            continue
        if tok.startswith("-"):
            i += 1
            continue
        paths.append(tok)
        i += 1
    assert marker is not None, (
        f"nightly-stress.yml: no `-m` marker expression in: {command!r}"
    )
    assert paths, f"nightly-stress.yml: no path arguments in: {command!r}"
    return marker, paths


def _collect_node_ids(marker: str, paths: list[str]) -> set[str]:
    """Flat ``path::Class::test[params]`` node IDs collect-only would
    run, given a marker expression and path arguments."""
    result = subprocess.run(
        [
            sys.executable, "-m", "pytest",
            "-m", marker, *paths,
            "--collect-only", "-q",
        ],
        cwd=ROOT,
        capture_output=True,
        text=True,
        encoding="utf-8",
        check=False,
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


class TestNightlyStressLaneCollection1328:
    """The nightly stress workflow's marker selection must collect
    every ``@pytest.mark.stress`` instance repo-wide, not just the
    ones in whichever file the invocation happens to name."""

    def test_workflow_command_not_narrowed_to_test_stress_py_alone(self) -> None:
        """The extracted command must not scope collection to
        ``tests/test_stress.py`` alone — that file-scoping is the
        exact #1328 defect (the marker selection was collected, then
        silently re-narrowed by the trailing single-file argument)."""
        command = _extract_stress_run_command()
        _marker, paths = _parse_pytest_selection(command)
        assert paths != ["tests/test_stress.py"], (
            f"nightly-stress.yml's stress run command is file-scoped "
            f"to test_stress.py again: {command!r} — this is the "
            f"#1328 regression shape"
        )

    def test_workflow_selection_matches_canonical_stress_selection(self) -> None:
        """The workflow's own command must collect the same node IDs
        as the canonical ``-m stress`` selection over pyproject's own
        ``testpaths`` — no file-scoping that silently drops a
        stress-marked class living elsewhere in the tree.

        The marker is asserted to literally be ``stress`` (not just
        threaded through from whatever the workflow happens to say)
        and the canonical side is always collected with the literal
        ``"stress"``: a workflow that switched to some OTHER marker
        which coincidentally still selects the reclamation battery
        would otherwise compare that narrower selection against
        itself and pass, without noticing the rest of the `stress`
        domain (e.g. `tests/test_stress.py`'s 16 instances) fell out.
        """
        command = _extract_stress_run_command()
        marker, workflow_paths = _parse_pytest_selection(command)
        assert marker == "stress", (
            f"nightly-stress.yml's stress step no longer selects on the "
            f"`stress` marker (found {marker!r}) — this test's canonical "
            f"comparison is only meaningful against that marker"
        )
        workflow_ids = _collect_node_ids(marker, workflow_paths)

        canonical_ids = _collect_node_ids("stress", _canonical_testpaths())
        assert canonical_ids, (
            "canonical `-m stress` selection over testpaths collected "
            "nothing — this test is broken, not the workflow"
        )

        missing = canonical_ids - workflow_ids
        assert not missing, (
            "nightly-stress.yml's own command collects fewer tests "
            "than the canonical `-m stress` selection over "
            f"{_canonical_testpaths()!r} — missing: {sorted(missing)}"
        )

    def test_workflow_selection_collects_host_handle_reclamation_battery(
        self,
    ) -> None:
        """#1328's own repro, verbatim: replay the workflow's command
        in collect-only mode and assert all 10
        ``TestHostHandleReclamation573`` instances are among the
        collected node IDs.  Also asserts the marker is literally
        ``stress`` — otherwise a marker rename that still happened to
        select this one battery would pass here while silently
        dropping the rest of the `stress` domain."""
        command = _extract_stress_run_command()
        marker, paths = _parse_pytest_selection(command)
        assert marker == "stress", (
            f"nightly-stress.yml's stress step no longer selects on the "
            f"`stress` marker (found {marker!r})"
        )
        collected = _collect_node_ids(marker, paths)

        missing = [
            name
            for name in _EXPECTED_RECLAMATION_TESTS
            if not any(
                f"TestHostHandleReclamation573::{name}" in node_id
                for node_id in collected
            )
        ]
        assert not missing, (
            "nightly-stress.yml's stress selection does not collect "
            f"these TestHostHandleReclamation573 instances: {missing}"
        )
