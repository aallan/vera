"""Keeps a test that starts a Python or ``vera`` process, or reads the
compiler's source, out of mutmut's oracle.

A pytest plugin ``[tool.mutmut]`` loads (``-p tests.mutation_oracle``), so it
runs inside mutmut's copy of the tree, where each mutated module holds a copy
of each mutated function for each of its mutants: a mutated
``TypeEnv._register_builtins`` makes ``vera/environment.py`` 33.6 MB where it
is 49 KB.  Two kinds of test can be no mutant's oracle there:

- One that starts a Python or ``vera`` process.  The process compiles every
  such module afresh (``vera check`` on a one-line program takes 2.3 s
  against 0.4 s), and what it runs records nothing in mutmut's stats pass,
  so the test only costs the run time, and on a slow runner its own timeout.
- One that reads a ``.py`` file of the mutated source (``[tool.mutmut]``'s
  ``source_paths``), as text or through ``inspect.getsource``.  What it reads
  in the copy is mutmut's generated file, every mutant of the bin's units
  inlined, and a scan of it for a property the mutants break ("every site
  names a code", "every reader consults the gate") fails there with no
  mutant active, which under ``-x`` ends mutmut's stats pass with nothing
  saved (the four tests of #1827, each at the price of a stats pass).

So the plugin skips a test at the moment it starts such a process, where the
subprocess census (``tests/subprocess_census.py``) counts one, or opens such
a file (``open``, which ``pathlib`` reads through, and ``inspect.getsource``),
and appends the test's node id to the file ``MUTATION_ORACLE_SKIPS`` or
``MUTATION_ORACLE_SOURCE_SKIPS`` names, which the mutation lanes report.  Any
other process or file, and everything outside a test (a collection, mutmut's
own reads), goes as usual: a ``.lark`` grammar or a ``.wat`` runtime under
``vera/`` is read as before, since only ``.py`` files are mutated, and
pytest's own reads of a traceback's source go through ``tokenize.open``,
which holds its own reference to the original ``open``.

The skipped test is out of the oracle entirely.  mutmut's stats pass records,
at each test's teardown and whatever its outcome, the functions the test
reached, and runs a mutant against the tests recorded for its function; a
test skipped after it called a mutated function would be run against that
function's mutants, skip again, and leave each one a survivor.  So when the
test ends, the plugin takes it out of that record (mutmut 3.8's
``state().tests_by_mangled_function_name``), and a function only skipped
tests reach has its mutants ``no tests``.  A mutmut whose record is not
there stops the stats pass rather than leave the test in it.
"""

from __future__ import annotations

import builtins
import inspect
import io
import os
import subprocess
import sys
import tomllib
from collections.abc import Generator
from pathlib import Path
from typing import Any

import pytest

#: The variable naming the file each test skipped for a process is appended to.
SKIPS_ENV = "MUTATION_ORACLE_SKIPS"

#: The variable naming the file each test skipped for a source read is appended to.
SOURCE_SKIPS_ENV = "MUTATION_ORACLE_SOURCE_SKIPS"

#: Why a test is skipped, as its skip reason.
REASON = ("starts a Python or vera process, which inside mutmut's copy runs the mutated "
          "modules afresh and records nothing for the stats pass")
SOURCE_REASON = ("reads the compiler's source, which inside mutmut's copy holds every mutant of "
                 "the mutated functions inlined, so it fails there with no mutant active")

_ENV_BY_REASON = {REASON: SKIPS_ENV, SOURCE_REASON: SOURCE_SKIPS_ENV}

_current: str | None = None
_original_init: Any = None
_original_open: Any = None
_original_getsource: Any = None
_original_getsourcelines: Any = None
#: The mutated source paths, resolved: ``[tool.mutmut]``'s ``source_paths``
#: in the ``pyproject.toml`` beside this plugin's ``tests/`` (the copy's).
_source_roots: tuple[Path, ...] = ()
#: The tests this process has skipped, by node id, and why.
_skipped: dict[str, str] = {}


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
        pytest.skip(REASON)
    _original_init(self, *args, **kwargs)


def source_roots(root: Path) -> tuple[Path, ...]:
    """The mutated source paths under ``root``, from its ``pyproject.toml``'s
    ``[tool.mutmut]`` ``source_paths``; none without a configuration."""
    try:
        data = tomllib.loads((root / "pyproject.toml").read_text(encoding="utf-8"))
    except (OSError, tomllib.TOMLDecodeError):
        return ()
    paths = data.get("tool", {}).get("mutmut", {}).get("source_paths", [])
    return tuple((root / p).resolve() for p in paths if isinstance(p, str))


def _reads_a_source(file: Any) -> bool:
    """Whether ``file`` names a ``.py`` file under a mutated source path."""
    if not _source_roots or isinstance(file, int):
        return False
    try:
        path = Path(os.fsdecode(file))
    except TypeError:
        return False
    if path.suffix != ".py":
        return False
    try:
        resolved = path.resolve()
    except (OSError, RuntimeError):
        return False
    return any(resolved.is_relative_to(root) for root in _source_roots)


def _skipping_open(*args: Any, **kwargs: Any) -> Any:
    file = args[0] if args else kwargs.get("file")
    if _current is not None and _reads_a_source(file):
        pytest.skip(SOURCE_REASON)
    return _original_open(*args, **kwargs)


def _source_file_of(obj: Any) -> str | None:
    """The file ``inspect`` would read ``obj``'s source from, or None."""
    try:
        return inspect.getsourcefile(obj) or inspect.getfile(obj)
    except (TypeError, OSError):
        return None


def _skipping_getsource(obj: Any) -> Any:
    if _current is not None and _reads_a_source(_source_file_of(obj)):
        pytest.skip(SOURCE_REASON)
    return _original_getsource(obj)


def _skipping_getsourcelines(obj: Any) -> Any:
    if _current is not None and _reads_a_source(_source_file_of(obj)):
        pytest.skip(SOURCE_REASON)
    return _original_getsourcelines(obj)


def _record(nodeid: str, reason: str) -> None:
    path = os.environ.get(_ENV_BY_REASON[reason])
    if path:
        with open(path, "a", encoding="utf-8") as fh:
            fh.write(nodeid + "\n")


def _forget(nodeid: str) -> None:
    """Take a skipped test out of mutmut's record of the tests that reach
    each function, which only its stats pass writes."""
    if os.environ.get("MUTANT_UNDER_TEST") != "stats":
        return
    try:
        from mutmut.state import state
    except ImportError:
        pytest.exit("tests/mutation_oracle.py: mutmut.state is not there (mutmut 3.8 holds the "
                    "record of the tests that reach each function in it), so a skipped test "
                    "cannot be taken out of that record", returncode=3)
    names = {nodeid, nodeid.removeprefix("mutants/")}
    for tests in state().tests_by_mangled_function_name.values():
        tests.difference_update(names)


def pytest_configure(config: pytest.Config) -> None:
    global _original_init, _original_open, _original_getsource, _original_getsourcelines, _source_roots
    if _original_init is None:
        _original_init = subprocess.Popen.__init__
        subprocess.Popen.__init__ = _skipping_init  # type: ignore[method-assign]
    if _original_open is None:
        _source_roots = source_roots(Path(__file__).resolve().parent.parent)
        _original_open = builtins.open
        builtins.open = _skipping_open  # type: ignore[assignment]
        io.open = _skipping_open  # type: ignore[assignment]
        _original_getsource = inspect.getsource
        _original_getsourcelines = inspect.getsourcelines
        inspect.getsource = _skipping_getsource  # type: ignore[assignment]
        inspect.getsourcelines = _skipping_getsourcelines  # type: ignore[assignment]


def pytest_unconfigure(config: pytest.Config) -> None:
    global _original_init, _original_open, _original_getsource, _original_getsourcelines, _source_roots
    if _original_init is not None:
        subprocess.Popen.__init__ = _original_init  # type: ignore[method-assign]
        _original_init = None
    if _original_open is not None:
        builtins.open = _original_open
        io.open = _original_open
        inspect.getsource = _original_getsource
        inspect.getsourcelines = _original_getsourcelines
        _original_open = _original_getsource = _original_getsourcelines = None
        _source_roots = ()


@pytest.hookimpl(wrapper=True)
def pytest_runtest_makereport(item: pytest.Item, call: pytest.CallInfo[None]) -> Generator[None, Any, Any]:
    """A test is the plugin's when any phase ends in one of its skips: one
    that started the process or read the file itself, or one handed the
    skip a fixture cached."""
    report = yield
    excinfo = call.excinfo
    if (excinfo is not None and isinstance(excinfo.value, pytest.skip.Exception)
            and excinfo.value.msg in _ENV_BY_REASON):
        _skipped[item.nodeid] = excinfo.value.msg
    return report


@pytest.hookimpl(wrapper=True)
def pytest_runtest_protocol(item: pytest.Item, nextitem: pytest.Item | None) -> Generator[None, Any, Any]:
    """A process started, or a source file read, from a test's setup, call
    or teardown is the test's; a test skipped for one is recorded, and leaves
    mutmut's record once mutmut's own teardown hook has written it."""
    global _current
    _current = item.nodeid
    try:
        return (yield)
    finally:
        _current = None
        reason = _skipped.get(item.nodeid)
        if reason is not None:
            _record(item.nodeid, reason)
            _forget(item.nodeid)
