"""No test module constructs a wasmtime object at import time (#1745).

mutmut's fork server imports every selected test module once, in a
``pytest --collect-only`` session, and forks each test run from that
process.  wasmtime installs its trap handlers when a process creates its
first ``Engine`` and never again, and pytest's faulthandler plugin restores
the signal handlers it found when that session ends.  An ``Engine`` built
at import therefore leaves every forked run without a trap handler, and the
first WebAssembly trap ends the process (SIGILL, exit -4): the nightly
sweep's first night lost all seven slices this way.  A test module builds
its wasmtime objects inside a test, a fixture or a cached helper.
"""
from __future__ import annotations

import ast
from pathlib import Path

TESTS = Path(__file__).resolve().parent
FACTORIES = {"Engine", "Linker", "Store", "Component", "Module", "Instance"}


def _wasmtime_names(tree: ast.Module) -> set[str]:
    """The names this module imports from ``wasmtime`` or a submodule of it."""
    names: set[str] = set()
    for node in tree.body:
        if isinstance(node, ast.ImportFrom) and node.module and node.module.split(".")[0] == "wasmtime":
            names.update(alias.asname or alias.name for alias in node.names)
    return names


def _is_wasmtime_call(call: ast.Call, imported: set[str]) -> bool:
    func = call.func
    if isinstance(func, ast.Attribute):
        base = func.value
        while isinstance(base, ast.Attribute):
            base = base.value
        return isinstance(base, ast.Name) and base.id == "wasmtime" and func.attr in FACTORIES
    return isinstance(func, ast.Name) and func.id in imported and func.id in FACTORIES


def module_level_wasmtime_calls(path: Path) -> list[str]:
    """``name:line`` for every wasmtime factory call a module runs at import."""
    tree = ast.parse(path.read_text(encoding="utf-8"), filename=str(path))
    imported = _wasmtime_names(tree)
    found: list[str] = []
    for node in tree.body:
        if isinstance(node, (ast.Assign, ast.AnnAssign)) and node.value is not None:
            value: ast.AST = node.value
        elif isinstance(node, ast.Expr):
            value = node.value
        else:
            continue
        for sub in ast.walk(value):
            if isinstance(sub, ast.Call) and _is_wasmtime_call(sub, imported):
                found.append(f"{path.name}:{sub.lineno}")
    return found


def test_repro_no_test_module_builds_a_wasmtime_object_at_import() -> None:
    offenders = [hit for path in sorted(TESTS.glob("*.py")) for hit in module_level_wasmtime_calls(path)]
    assert offenders == [], "built at import, so mutmut's fork server loses wasmtime's trap handlers: " + ", ".join(offenders)


def test_the_gate_sees_a_module_level_engine(tmp_path: Path) -> None:
    sample = tmp_path / "test_sample.py"
    sample.write_text(
        "import wasmtime\nfrom wasmtime.component import Linker\n"
        "_ENGINE = wasmtime.Engine()\n_LINKER = Linker(_ENGINE)\n_LINKER.add_wasip2()\n"
        "def test_x():\n    engine = wasmtime.Engine()\n",
        encoding="utf-8")
    assert module_level_wasmtime_calls(sample) == ["test_sample.py:3", "test_sample.py:4"]
