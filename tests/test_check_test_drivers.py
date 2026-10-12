"""Tests for scripts/check_test_drivers.py, the gate that keeps one pipeline driver.

The gate fails a helper in ``tests/test_*.py`` that drives a compiler stage
itself rather than through ``tests/pipeline.py``.  These tests plant drivers
of every kind the gate names (each stage function under each way a module
imports it, the stage methods, the CLI's entry points, a subprocess naming
``vera``) and the look-alikes it must leave alone, and hold the allowlist to
its two rules: an allowed driver passes, and an entry that names no driver
is an error.  The last test runs the gate over this repository.

The script lives in ``scripts/``, not a package, so it is loaded as a module.
"""

from __future__ import annotations

import importlib.util
import sys
import textwrap
from pathlib import Path
from types import ModuleType

import pytest

ROOT = Path(__file__).resolve().parent.parent
SCRIPT = ROOT / "scripts" / "check_test_drivers.py"


@pytest.fixture(scope="module")
def gate() -> ModuleType:
    spec = importlib.util.spec_from_file_location("check_test_drivers", SCRIPT)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    sys.modules["check_test_drivers"] = module
    spec.loader.exec_module(module)
    return module


def _drivers(gate: ModuleType, source: str) -> dict[str, tuple[str, ...]]:
    found = gate.drivers_in(textwrap.dedent(source), "tests/test_planted.py")
    return {d.helper: d.calls for d in found}


# =====================================================================
# What the gate catches
# =====================================================================


@pytest.mark.parametrize("imports,call,expected", [
    ("from vera.parser import parse_to_ast", "parse_to_ast(s)", "parse_to_ast"),
    ("from vera.parser import parse", "parse(s)", "parse"),
    ("from vera.parser import parse_file", "parse_file(s)", "parse_file"),
    ("from vera.transform import transform", "transform(s)", "transform"),
    ("from vera.checker import typecheck", "typecheck(s)", "typecheck"),
    ("from vera.checker.core import typecheck_with_artifacts",
     "typecheck_with_artifacts(s)", "typecheck_with_artifacts"),
    ("from vera.verifier import verify", "verify(s)", "verify"),
    ("from vera.codegen import compile as codegen_compile",
     "codegen_compile(s)", "compile"),
    ("from vera.codegen.api import execute", "execute(s)", "execute"),
    ("from vera.tester import test as run_test", "run_test(s)", "test"),
    ("from vera.resolver import ModuleResolver", "ModuleResolver(_root=s)",
     "ModuleResolver"),
    ("import vera.parser", "vera.parser.parse_to_ast(s)", "parse_to_ast"),
    ("import vera.parser as P", "P.parse_to_ast(s)", "parse_to_ast"),
    ("from vera import codegen", "codegen.execute(s)", "execute"),
    ("from vera.cli import main", "main()", "vera.cli.main"),
    ("from vera import cli", "cli.cmd_verify(s)", "vera.cli.cmd_verify"),
    ("", "gen.compile_program(s)", "compile_program"),
    ("", "verifier.verify_program(s)", "verify_program"),
    ("", "resolver.resolve_imports(s, p)", "resolve_imports"),
], ids=lambda v: v if isinstance(v, str) and "(" in v else None)
def test_a_helper_that_calls_a_stage_is_a_driver(
    gate: ModuleType, imports: str, call: str, expected: str,
) -> None:
    source = f"{imports}\n\ndef _helper(s, p=None):\n    return {call}\n"
    assert _drivers(gate, source) == {"_helper": (expected,)}


def test_an_import_inside_the_helper_counts(gate: ModuleType) -> None:
    assert _drivers(gate, """
        def _compile(source):
            from vera.codegen import compile
            from vera.parser import parse_to_ast
            return compile(parse_to_ast(source))
    """) == {"_compile": ("compile", "parse_to_ast")}


def test_a_helper_method_of_a_test_class_is_a_driver(gate: ModuleType) -> None:
    found = gate.drivers_in(textwrap.dedent("""
        from vera.parser import parse_to_ast

        class TestThing:
            def _parse(self, s):
                return parse_to_ast(s)

            def test_it(self):
                assert parse_to_ast("x")
    """), "tests/test_planted.py")
    assert [(d.helper, d.calls) for d in found] == [
        ("TestThing._parse", ("parse_to_ast",))]


def test_a_nested_function_counts_toward_its_helper(gate: ModuleType) -> None:
    assert _drivers(gate, """
        from vera.verifier import verify

        def _make():
            def inner(s):
                return verify(s)
            return inner
    """) == {"_make": ("verify",)}


@pytest.mark.parametrize("body", [
    'subprocess.run([sys.executable, "-m", "vera.cli", "check", p])',
    'subprocess.run(["vera", "run", p])',
    'subprocess.check_output("vera check " + p, shell=True)',
    'subprocess.Popen([sys.executable, "-c", "from vera.cli import main"])',
    'subprocess.run(["/opt/homebrew/bin/vera", "check", p])',
    'cmd = [sys.executable, "-m", "vera.cli", p]\n    subprocess.run(cmd)',
    'subprocess.run([*_VERA, "check", p])',
    'run([sys.executable, "-m", "vera.cli", p])',
], ids=["module-argv", "binary", "shell-string", "dash-c-script", "binary-path",
        "local-argv", "module-argv-name", "imported-run"])
def test_a_subprocess_naming_vera_is_a_driver(
    gate: ModuleType, body: str,
) -> None:
    source = (
        "import subprocess\nimport sys\nfrom subprocess import run\n\n"
        '_VERA = [sys.executable, "-m", "vera.cli"]\n\n'
        f"def _cli(p):\n    {body}\n"
    )
    assert list(_drivers(gate, source)) == ["_cli"]


def test_a_runner_handed_a_vera_command_is_a_driver(gate: ModuleType) -> None:
    assert list(_drivers(gate, """
        import subprocess
        import sys

        def _run_json(argv):
            return subprocess.run(argv, capture_output=True, check=False)

        def test_it(p):
            _run_json([sys.executable, "-m", "vera.cli", "check", "--json", p])
    """)) == ["_run_json"]


# =====================================================================
# What the gate leaves alone
# =====================================================================


def test_what_is_not_a_driver_is_left_alone(gate: ModuleType) -> None:
    assert _drivers(gate, """
        import subprocess
        import sys
        from pathlib import Path

        from tests import pipeline
        from tests.pipeline import compile as pipeline_compile
        from vera.parser import parse_to_ast

        ROOT = Path(__file__).parent
        HARNESS = ROOT / "vera" / "browser" / "harness.mjs"

        def test_calls_a_stage_itself():
            assert parse_to_ast("x")

        def _drives_the_pipeline(s):
            return pipeline.verify(s).result, pipeline_compile(s).wat

        def _runs_git(path):
            return subprocess.run(["git", "-C", str(path), "status"], check=False)

        def _runs_node(wasm):
            return subprocess.run(["node", str(HARNESS), wasm], check=False)

        def _runs_its_argv(argv):
            return subprocess.run(argv, check=False)

        def test_hands_it_git(tmp_path):
            _runs_its_argv(["git", "init", str(tmp_path)])

        def _checks_a_program(checker, program):
            return checker.check_program(program)
    """) == {}


# =====================================================================
# The allowlist
# =====================================================================


_PLANTED = """
from vera.parser import parse_to_ast

def _ast(s):
    return parse_to_ast(s)

def _also(s):
    return parse_to_ast(s)
"""


def test_a_driver_the_allowlist_does_not_name_fails(gate: ModuleType) -> None:
    found = gate.drivers_in(_PLANTED, "tests/test_planted.py")
    problems = gate.problems(found, {"tests/test_planted.py::_ast": "a reason"})
    assert problems == [
        "tests/test_planted.py:7: _also drives the pipeline itself "
        "(parse_to_ast); drive it through tests/pipeline.py"]


def test_an_allowed_driver_passes(gate: ModuleType) -> None:
    found = gate.drivers_in(_PLANTED, "tests/test_planted.py")
    assert gate.problems(found, {
        "tests/test_planted.py::_ast": "a reason",
        "tests/test_planted.py::_also": "another",
    }) == []


@pytest.mark.parametrize("key", [
    "tests/test_planted.py::_gone",
    "tests/test_elsewhere.py::_ast",
])
def test_an_entry_that_names_no_driver_is_an_error(
    gate: ModuleType, key: str,
) -> None:
    found = gate.drivers_in(_PLANTED, "tests/test_planted.py")
    allowed = {d.key: "a reason" for d in found} | {key: "stale"}
    assert gate.problems(found, allowed) == [
        f"ALLOWED names {key}, which drives no stage: delete the entry"]


def test_an_entry_whose_helper_stopped_driving_is_an_error(
    gate: ModuleType,
) -> None:
    """The entry outlives the migration it was waiting for."""
    migrated = _PLANTED.replace("return parse_to_ast(s)", "return s", 1)
    found = gate.drivers_in(migrated, "tests/test_planted.py")
    assert gate.problems(found, {
        "tests/test_planted.py::_ast": "a reason",
        "tests/test_planted.py::_also": "another",
    }) == [
        "ALLOWED names tests/test_planted.py::_ast, which drives no stage: "
        "delete the entry"]


def test_an_entry_needs_a_reason(gate: ModuleType) -> None:
    found = gate.drivers_in(_PLANTED, "tests/test_planted.py")
    allowed = {d.key: "a reason" for d in found}
    allowed["tests/test_planted.py::_also"] = "  "
    assert gate.problems(found, allowed) == [
        "ALLOWED gives tests/test_planted.py::_also no reason"]


# =====================================================================
# This repository
# =====================================================================


def test_the_suite_drives_the_pipeline_through_tests_pipeline(
    gate: ModuleType, capsys: pytest.CaptureFixture[str],
) -> None:
    assert gate.main([]) == 0, capsys.readouterr().err


def test_a_driver_planted_in_the_suite_fails_the_gate(
    gate: ModuleType, tmp_path: Path,
) -> None:
    (tmp_path / "tests").mkdir()
    (tmp_path / "tests" / "test_planted.py").write_text(_PLANTED, encoding="utf-8")
    found = gate.scan(tmp_path)
    assert [d.key for d in found] == [
        "tests/test_planted.py::_ast", "tests/test_planted.py::_also"]
    assert len(gate.problems(found, gate.ALLOWED)) == (
        2 + len(gate.ALLOWED))
