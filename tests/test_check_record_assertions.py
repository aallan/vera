"""Tests for scripts/check_record_assertions.py, the gate that keeps the
guard-and-trap assertions on the record.

The gate fails a site in ``tests/*.py`` that reads a check's signal out of the
WAT text, where ``tests/pipeline.py``'s ``checks`` reads the module's record of
its checks.  These tests plant every shape the gate names (the trap
registry's names for a signal, under each way a module imports them; a string
holding a signal's symbol, plain, as a regex and inside an f-string; a
module-level name carrying one to another scope) and the look-alikes it must
leave alone, hold the allowlist to its rules, and run the gate over this
repository.

The script lives in ``scripts/``, not a package, so it is loaded as a module.
This file is the one the gate does not scan: the sites in it are source text.
"""

from __future__ import annotations

import importlib.util
import sys
import textwrap
from pathlib import Path
from types import ModuleType

import pytest

ROOT = Path(__file__).resolve().parent.parent
SCRIPT = ROOT / "scripts" / "check_record_assertions.py"


@pytest.fixture(scope="module")
def gate() -> ModuleType:
    spec = importlib.util.spec_from_file_location("check_record_assertions", SCRIPT)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    sys.modules["check_record_assertions"] = module
    spec.loader.exec_module(module)
    return module


def _sites(gate: ModuleType, source: str) -> set[tuple[str, str]]:
    found = gate.sites_in(textwrap.dedent(source), "tests/test_planted.py")
    return {(s.scope, s.shape) for s in found}


# =====================================================================
# What the gate catches
# =====================================================================


@pytest.mark.parametrize("imports,line,shape", [
    ("from vera.trap_registry import signal_call_pattern",
     'assert signal_call_pattern("nat_guard").search(wat)', "signal_call_pattern"),
    ("from vera.trap_registry import signal_call_pattern as pattern",
     'assert pattern("nat_guard").search(wat)', "signal_call_pattern"),
    ("import vera.trap_registry as registry",
     'assert registry.signal_call_pattern("overflow").findall(wat)',
     "signal_call_pattern"),
    ("from vera.trap_registry import TRAP_SIGNAL",
     'assert f"call $vera.{TRAP_SIGNAL}" in wat', "TRAP_SIGNAL"),
    ("from vera import trap_registry",
     'assert trap_registry.CONTRACT_SIGNAL in wat', "CONTRACT_SIGNAL"),
    ("", 'assert "call $vera.contract_fail" in wat', "contract_fail"),
    ("", 'assert "contract_fail" not in wat', "contract_fail"),
    ("", 'assert wat.count("call $vera.trap") == 2', "vera.trap"),
    ("import re",
     r'assert re.search(r"i32\.const 2\s+i32\.const \d+\s+i32\.const \d+\s+'
     r'call \$vera\.trap", wat)', "vera.trap"),
    ("import re", r'assert re.search(rf"i32\.const {code}\s+call \$vera\.trap", wat)',
     "vera.trap"),
    ("from tests.codegen_helpers import wat_calls",
     'assert wat_calls(wat, "vera.contract_fail")', "contract_fail"),
    ("", 'assert any(line.strip() == "call $vera.contract_fail" '
         "for line in wat.splitlines())", "contract_fail"),
], ids=["the-pattern", "the-pattern-aliased", "the-pattern-by-module",
        "the-trap-symbol", "the-contract-symbol", "a-call-substring",
        "an-absence", "a-count", "a-regex", "an-f-string-regex",
        "a-wat-calls-symbol", "a-line-equality"])
def test_a_test_reading_a_signal_out_of_the_text_is_a_site(
    gate: ModuleType, imports: str, line: str, shape: str,
) -> None:
    source = f"{imports}\n\ndef test_it(wat, code):\n    {line}\n"
    assert _sites(gate, source) == {("test_it", shape)}


def test_a_site_is_named_by_the_function_it_sits_in(gate: ModuleType) -> None:
    assert _sites(gate, """
        class TestThing:
            def test_method(self, wat):
                assert "contract_fail" in wat

            def _helper(self, wat):
                def inner():
                    return wat.count("call $vera.trap")
                return inner()
    """) == {("TestThing.test_method", "contract_fail"),
             ("TestThing._helper.inner", "vera.trap")}


def test_a_name_bound_to_a_site_carries_it_to_each_use(gate: ModuleType) -> None:
    """A module-level pattern, a table holding it and a helper reading it are
    each a site wherever another scope uses them."""
    assert _sites(gate, """
        import re
        from vera.trap_registry import signal_call_pattern

        _PATTERN = signal_call_pattern("nat_guard")
        _TABLE = {"nat": _PATTERN}

        def _count(wat):
            return len(re.findall(r"call \\$vera\\.trap", wat))

        def test_pattern(wat):
            assert _PATTERN.search(wat)

        def test_table(wat):
            assert _TABLE["nat"].search(wat)

        def test_count(wat):
            assert _count(wat) == 1
    """) == {("_PATTERN", "signal_call_pattern"), ("_TABLE", "_PATTERN"),
             ("_count", "vera.trap"), ("test_pattern", "_PATTERN"),
             ("test_table", "_TABLE"), ("test_count", "_count")}


def test_a_test_holding_a_site_carries_nothing(gate: ModuleType) -> None:
    """A test named elsewhere, or a test class subclassed, is not a pattern
    another scope reads."""
    assert _sites(gate, """
        def test_a(wat):
            assert "contract_fail" in wat

        def test_b(wat):
            test_a(wat)

        class TestBase:
            def test_it(self, wat):
                assert "contract_fail" in wat

        class TestSub(TestBase):
            pass
    """) == {("test_a", "contract_fail"), ("TestBase.test_it", "contract_fail")}


# =====================================================================
# What the gate leaves alone
# =====================================================================


def test_what_reads_no_signal_is_left_alone(gate: ModuleType) -> None:
    assert _sites(gate, '''
        """The module calls `$vera.trap` and `$vera.contract_fail`."""

        import wasmtime

        from tests import pipeline
        from vera.trap_registry import TRAP_KINDS

        _NOTE = 1
        """`contract_fail` is the contract channel's import."""

        def test_the_record(result):
            """Each check calls `$vera.trap` once."""
            # A comment naming call $vera.trap is not a site.
            assert pipeline.checks(result, kind="contract_violation")
            assert TRAP_KINDS["overflow"].code == 1

        def test_the_rendering(wat):
            assert '(import "vera" "trap"' in wat
            assert "trap_kind" not in wat

        def _link(linker, store):
            linker.define_func("vera", "trap", None, lambda *a: None)
    ''') == set()


# =====================================================================
# The allowlist
# =====================================================================


_PLANTED = """
def test_kept(wat):
    assert "contract_fail" in wat

def test_new(wat):
    assert wat.count("call $vera.trap") == 1
"""


def test_a_site_the_allowlist_does_not_name_fails(gate: ModuleType) -> None:
    found = gate.sites_in(_PLANTED, "tests/test_planted.py")
    problems = gate.problems(
        found, {"tests/test_planted.py::test_kept::contract_fail": "a reason"})
    assert problems == [
        "tests/test_planted.py:6: test_new reads a check's signal out of the "
        "WAT text (vera.trap); ask the record through tests/pipeline.py's "
        "checks(), or keep the site with its reason"]


def test_a_kept_site_passes(gate: ModuleType) -> None:
    found = gate.sites_in(_PLANTED, "tests/test_planted.py")
    assert gate.problems(found, {
        "tests/test_planted.py::test_kept::contract_fail": "a reason",
        "tests/test_planted.py::test_new::vera.trap": "another",
    }) == []


@pytest.mark.parametrize("key", [
    "tests/test_planted.py::test_gone::contract_fail",
    "tests/test_planted.py::test_kept::vera.trap",
    "tests/test_elsewhere.py::test_kept::contract_fail",
])
def test_an_entry_that_names_no_site_is_an_error(
    gate: ModuleType, key: str,
) -> None:
    found = gate.sites_in(_PLANTED, "tests/test_planted.py")
    kept = {s.key: "a reason" for s in found} | {key: "stale"}
    assert gate.problems(found, kept) == [
        f"KEPT names {key}, which names no site: delete the entry"]


def test_an_entry_whose_site_moved_to_the_record_is_an_error(
    gate: ModuleType,
) -> None:
    """The entry outlives the migration it stood for."""
    moved = _PLANTED.replace(
        'assert "contract_fail" in wat',
        'assert pipeline.checks(result, kind="contract_violation")')
    found = gate.sites_in(moved, "tests/test_planted.py")
    assert gate.problems(found, {
        "tests/test_planted.py::test_kept::contract_fail": "a reason",
        "tests/test_planted.py::test_new::vera.trap": "another",
    }) == [
        "KEPT names tests/test_planted.py::test_kept::contract_fail, which "
        "names no site: delete the entry"]


def test_an_entry_needs_a_reason(gate: ModuleType) -> None:
    found = gate.sites_in(_PLANTED, "tests/test_planted.py")
    kept = {s.key: "a reason" for s in found}
    kept["tests/test_planted.py::test_new::vera.trap"] = "  "
    assert gate.problems(found, kept) == [
        "KEPT gives tests/test_planted.py::test_new::vera.trap no reason"]


# =====================================================================
# This repository
# =====================================================================


def test_the_suite_asks_the_record_whether_a_module_holds_a_check(
    gate: ModuleType, capsys: pytest.CaptureFixture[str],
) -> None:
    assert gate.main([]) == 0, capsys.readouterr().err


def test_a_name_imported_from_the_module_it_carries_a_site_in_is_a_site(
    gate: ModuleType, tmp_path: Path,
) -> None:
    """A pattern kept in one test module is not read from another unseen."""
    (tmp_path / "tests").mkdir()
    (tmp_path / "tests" / "test_kept.py").write_text(
        "import re\n\n_CALL = re.compile(r'call \\$vera\\.contract_fail')\n"
        "_UNRELATED = 3\n", encoding="utf-8")
    (tmp_path / "tests" / "test_reader.py").write_text(
        "from tests.test_kept import _CALL, _UNRELATED\n\n"
        "def test_it(wat):\n    assert _CALL.search(wat)\n", encoding="utf-8")
    (tmp_path / "tests" / "test_relative.py").write_text(
        "from .test_kept import _CALL\n", encoding="utf-8")
    assert [s.key for s in gate.scan(tmp_path)] == [
        "tests/test_kept.py::_CALL::contract_fail",
        "tests/test_reader.py::<module>::_CALL",
        "tests/test_relative.py::<module>::_CALL"]


def test_a_site_planted_in_the_suite_fails_the_gate(
    gate: ModuleType, tmp_path: Path,
) -> None:
    (tmp_path / "tests").mkdir()
    (tmp_path / "tests" / "test_planted.py").write_text(_PLANTED, encoding="utf-8")
    (tmp_path / "tests" / "test_check_record_assertions.py").write_text(
        _PLANTED, encoding="utf-8")
    found = gate.scan(tmp_path)
    assert [s.key for s in found] == [
        "tests/test_planted.py::test_kept::contract_fail",
        "tests/test_planted.py::test_new::vera.trap"]
    assert len(gate.problems(found, gate.KEPT)) == 2 + len(gate.KEPT)
