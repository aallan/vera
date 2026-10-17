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

Import time is everything a module runs when it is imported: its top-level
statements, the bodies of its classes and of its ``if``, ``try``, ``for``
and ``with`` blocks, its decorators and its default arguments.  Function
bodies run later, so they are not read.
"""
from __future__ import annotations

import ast
from collections.abc import Iterator
from pathlib import Path

TESTS = Path(__file__).resolve().parent
FACTORIES = {"Engine", "Linker", "Store", "Component", "Module", "Instance"}
_DEFERRED = (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)


def _imports(tree: ast.Module) -> tuple[set[str], dict[str, str]]:
    """The names bound to the ``wasmtime`` package or a submodule of it, and
    the names bound by ``from wasmtime... import X [as Y]``, each mapped to
    the wasmtime name it stands for."""
    modules: set[str] = set()
    names: dict[str, str] = {}
    for node in ast.walk(tree):
        if isinstance(node, ast.Import):
            for alias in node.names:
                if alias.name.split(".")[0] == "wasmtime":
                    modules.add(alias.asname or alias.name.split(".")[0])
        elif isinstance(node, ast.ImportFrom) and node.module and node.module.split(".")[0] == "wasmtime":
            for alias in node.names:
                names[alias.asname or alias.name] = alias.name
    return modules, names


def _is_wasmtime_call(call: ast.Call, modules: set[str], names: dict[str, str]) -> bool:
    func = call.func
    if isinstance(func, ast.Attribute):
        base = func.value
        while isinstance(base, ast.Attribute):
            base = base.value
        return isinstance(base, ast.Name) and base.id in modules and func.attr in FACTORIES
    return isinstance(func, ast.Name) and names.get(func.id) in FACTORIES


def _import_time_calls(node: ast.AST) -> Iterator[ast.Call]:
    """Every call ``node`` runs at import: function bodies are deferred, their
    decorators and default arguments are not."""
    if isinstance(node, _DEFERRED):
        parts: list[ast.AST] = list(getattr(node, "decorator_list", []))
        parts += node.args.defaults + [d for d in node.args.kw_defaults if d is not None]
        for part in parts:
            yield from _import_time_calls(part)
        return
    if isinstance(node, ast.Call):
        yield node
    for child in ast.iter_child_nodes(node):
        yield from _import_time_calls(child)


def module_level_wasmtime_calls(path: Path) -> list[str]:
    """``file:line`` for every wasmtime factory call a module runs at import."""
    tree = ast.parse(path.read_text(encoding="utf-8"), filename=str(path))
    modules, names = _imports(tree)
    return [f"{path.name}:{call.lineno}" for call in _import_time_calls(tree) if _is_wasmtime_call(call, modules, names)]


def test_repro_no_test_module_builds_a_wasmtime_object_at_import() -> None:
    offenders = [hit for path in sorted(TESTS.rglob("*.py")) for hit in module_level_wasmtime_calls(path)]
    assert offenders == [], "built at import, so mutmut's fork server loses wasmtime's trap handlers: " + ", ".join(offenders)


def test_the_gate_sees_every_import_time_form(tmp_path: Path) -> None:
    sample = tmp_path / "test_sample.py"
    sample.write_text(
        "import sys\n"
        "import wasmtime\n"
        "import wasmtime as wt\n"
        "from wasmtime import Engine as WasmEngine\n"
        "from wasmtime.component import Linker\n"
        "_ENGINE = wasmtime.Engine()\n"                      # 6: the package name
        "_LINKER = Linker(_ENGINE)\n"                        # 7: a name imported from a submodule
        "_LINKER.add_wasip2()\n"
        "if sys.platform:\n"
        "    _ALT = wt.Engine()\n"                           # 10: a module alias, in a conditional
        "class Fixtures:\n"
        "    engine = WasmEngine()\n"                        # 12: an import alias, in a class body
        "def test_x(engine=wasmtime.Store(_ENGINE)):\n"     # 13: a default argument
        "    inner = wasmtime.Engine()\n"                    # deferred: a function body
        "    return inner\n"
        "@pytest_mark(wasmtime.Module(_ENGINE, b''))\n"      # 16: a decorator
        "def test_y():\n"
        "    return wasmtime.Engine()\n",                    # deferred
        encoding="utf-8")
    hits = module_level_wasmtime_calls(sample)
    assert hits == [f"test_sample.py:{n}" for n in (6, 7, 10, 12, 13, 16)]
