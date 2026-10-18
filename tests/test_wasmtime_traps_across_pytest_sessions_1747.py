"""wasmtime's trap handlers survive a second in-process pytest session (#1747).

pytest's faulthandler plugin calls ``faulthandler.enable()`` when a session
starts, which records the process's signal handlers, and
``faulthandler.disable()`` when it ends, which puts them back.  wasmtime
installs its handlers for SIGILL, SIGSEGV, SIGBUS and SIGFPE once per
process, at the first ``Engine``, and never again.  A process that creates
its first ``Engine`` inside one pytest session and then runs another has no
wasmtime handler in the second: the session that ended restored the
handlers it recorded, which predate the ``Engine``.  The second session's
first WebAssembly trap (``unreachable`` compiles to ``ud2``) then reaches
faulthandler, which prints its dump and re-raises, and the process dies
with SIGILL.

mutmut's fork runner is such a process: it runs the stats pass and the
clean pass as two sessions, and forks the mutant runs from the result.  The
nightly sweep lost every slice of its first two nights this way (#1745,
#1747).  The lanes therefore run pytest with ``-p no:faulthandler``
(``[tool.mutmut]``'s ``pytest_add_cli_args``): with the plugin out nothing
records or restores handlers, and wasmtime's stay from the first ``Engine``
on.

Traps are signals on Linux alone: macOS delivers them through Mach
exception ports and Windows through a vectored exception handler, and
faulthandler touches neither, so the two subprocess tests run on Linux.
"""
from __future__ import annotations

import os
import subprocess
import sys
import tomllib
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]
LINUX_ONLY = pytest.mark.skipif(sys.platform != "linux", reason="wasm traps are signals on Linux alone")

TRAPPING_TEST = '''\
import pytest
import wasmtime


def test_a_trap_is_an_exception():
    engine = wasmtime.Engine()
    store = wasmtime.Store(engine)
    module = wasmtime.Module(engine, '(module (func (export "f") unreachable))')
    f = wasmtime.Instance(store, module, []).exports(store)["f"]
    with pytest.raises(wasmtime.Trap):
        f(store)
'''

DRIVER = '''\
import sys

import pytest

codes = [int(pytest.main(["-q", "-p", "no:cacheprovider", *sys.argv[1:], "test_trap_1747.py"]))
         for _ in range(2)]
print("CODES", codes, flush=True)
sys.exit(0 if codes == [0, 0] else 1)
'''


def _two_sessions(tmp_path: Path, *pytest_args: str) -> subprocess.CompletedProcess[str]:
    """A Python process that holds two in-process pytest sessions, each over
    one test that traps a wasm module and expects the ``Trap``."""
    (tmp_path / "test_trap_1747.py").write_text(TRAPPING_TEST, encoding="utf-8")
    (tmp_path / "driver.py").write_text(DRIVER, encoding="utf-8")
    env = {k: v for k, v in os.environ.items() if k != "PYTEST_ADDOPTS"}
    env["PYTHONDONTWRITEBYTECODE"] = "1"
    return subprocess.run([sys.executable, "-u", "driver.py", *pytest_args], cwd=tmp_path, env=env,
                          capture_output=True, text=True, encoding="utf-8", timeout=300, check=False)


@LINUX_ONLY
def test_repro_the_second_session_has_no_trap_handler_under_faulthandler(tmp_path: Path) -> None:
    run = _two_sessions(tmp_path)
    assert "1 passed" in run.stdout, run.stdout + run.stderr      # the first session handled its trap
    assert run.returncode < 0, (run.returncode, run.stdout, run.stderr)   # the second died by signal
    assert "CODES" not in run.stdout


@LINUX_ONLY
def test_no_faulthandler_keeps_the_trap_handlers_across_sessions(tmp_path: Path) -> None:
    run = _two_sessions(tmp_path, "-p", "no:faulthandler")
    assert run.returncode == 0 and "CODES [0, 0]" in run.stdout, (run.returncode, run.stdout, run.stderr)


def test_the_lanes_run_pytest_without_the_faulthandler_plugin() -> None:
    """``[tool.mutmut]``'s pytest arguments, which both lanes' ``rewrite_config`` keep, hold the flag as an adjacent pair."""
    args = tomllib.loads((ROOT / "pyproject.toml").read_text(encoding="utf-8"))["tool"]["mutmut"]["pytest_add_cli_args"]
    assert ("-p", "no:faulthandler") in zip(args, args[1:]), args
