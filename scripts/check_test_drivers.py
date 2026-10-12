#!/usr/bin/env python3
"""Every test drives the compiler pipeline through ``tests/pipeline.py``.

``tests/pipeline.py`` is the suite's one driver.  A test that parses, checks,
verifies, compiles, runs or contract-tests a program calls its stage
functions, or the ``tests/*_helpers.py`` layers over them, so every test
exercises the pipeline the CLI runs, wired one way.  This gate fails a helper
in ``tests/test_*.py`` that drives a stage itself.

A helper is a function at a test module's top level, or in the body of one of
its top-level classes, whose name does not start with ``test``: a test calls
the stage it is about, and a driver is the function tests share to do it.  A
helper drives a stage when it calls, under whatever name its module imports
it as:

- a stage function of the compiler (``STAGE_FUNCTIONS``);
- a stage method (``STAGE_METHODS``): ``TypeChecker.check_program``,
  ``CodeGenerator.compile_program``, ``ContractVerifier.verify_program``,
  ``ModuleResolver.resolve_imports``;
- ``vera.cli.main`` or a ``vera.cli.cmd_*`` command;
- a subprocess (``subprocess.run``, ``Popen``, ``check_output``, ``call``,
  ``check_call``) whose command names ``vera``: a string in it, or in a value
  a name in it was assigned, is ``vera`` or ``vera.cli``, starts with the
  word ``vera``, holds ``-m vera`` or ``vera.cli`` (a ``python -c`` script
  that imports the CLI), or is a path ending in ``/vera``.  A path built with
  ``/`` names nothing by its parts.  A helper that runs a command it is
  handed drives a stage when a call to it in the same module hands it one.

A stage function or a CLI entry point counts however the call reaches it:
by its name, or through a value (#1662).  The call's target is followed
through the names it is assigned, the ``for`` loops that bind it, the
containers it is read out of (a dict's values, a list's, tuple's or set's
elements), the operands of a conditional or an ``or``, a parameter's default,
and ``getattr`` on a module that holds stage entry points.  A helper that
calls a value it is handed drives a stage when a call to it in the same
module hands it one.

``ALLOWED`` names each driver that stays, by file and helper, with the
reason.  An entry that names no driver, because its helper is gone or drives
no stage, is an error, so the list only shrinks.

Usage:
    python scripts/check_test_drivers.py           # scan tests/test_*.py
    python scripts/check_test_drivers.py --list    # print every driver found
"""

from __future__ import annotations

import ast
import sys
from collections.abc import Iterable, Iterator, Mapping
from dataclasses import dataclass, field
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

#: The compiler's stage functions, by the module that defines or exports them.
STAGE_FUNCTIONS: Mapping[str, frozenset[str]] = {
    "vera.parser": frozenset({
        "parse", "parse_file", "parse_to_ast", "verify_file", "typecheck_file",
    }),
    "vera.transform": frozenset({"transform"}),
    "vera.resolver": frozenset({"ModuleResolver"}),
    "vera.checker": frozenset({"typecheck", "typecheck_with_artifacts"}),
    "vera.checker.core": frozenset({"typecheck", "typecheck_with_artifacts"}),
    "vera.verifier": frozenset({"verify"}),
    "vera.codegen": frozenset({"compile", "execute"}),
    "vera.codegen.api": frozenset({"compile", "execute"}),
    "vera.tester": frozenset({"test"}),
}

#: Stage methods, matched by name on any receiver.
STAGE_METHODS = frozenset({
    "check_program", "compile_program", "verify_program", "resolve_imports",
})

SUBPROCESS_CALLS = frozenset({"run", "Popen", "check_output", "call", "check_call"})

_CLI_SUITE = (
    "tests/test_cli.py, the CLI's own suite, drives the commands and the code "
    "beneath them itself"
)
_CLI_SMOKE = (
    "the CLI smoke: runs the corpus programs CLI_SMOKE names, and a program for "
    "each exit the corpus lacks (CLI_EXIT_SHAPES), through `python -m vera.cli` "
    "as a process, and holds each command's exit status and output to the "
    "in-process CLI's, byte for byte"
)
_HASH_SEED = (
    "sweeps PYTHONHASHSEED, which an interpreter fixes when it starts, so each "
    "seed needs a fresh interpreter"
)
_HOST_FAULT = (
    "runs programs whose unrooted wrapper faults the host interpreter, and a "
    "child process turns the fault into an exit status an assertion reads"
)
_DEADLINE = (
    "the deadline is the assertion: the check must answer within it, and only "
    "a child process can be stopped when it does not"
)
_ANOTHER_TREE = (
    "runs the CLI of a scratch copy of the compiler, which only another "
    "interpreter can import"
)
_NEVER_STOPS = (
    "runs programs that never stop unless the guard under test stops them, "
    "and their red is the child process's timeout"
)
_LARK_TREE = (
    "copies the doc gate's parse stage, the Lark parse alone (vera.parser.parse, "
    "no transform); pipeline.parse transforms too, so a block that parses but "
    "does not transform would change verdict"
)
_SUBSTITUTED_TABLE = (
    "hands the verifier or code generation a semantic-type table other than "
    "the checker's, on purpose; no stage takes one"
)
_MODULE_TABLES_WITHHELD = (
    "compiles without the imported modules' own tables on purpose "
    "(thread_modules=False); every stage that compiles threads them"
)
_RESOLVER_UNIT = (
    "a unit test of ModuleResolver itself, over programs that need not "
    "type-check; the pipeline resolves only inside a check"
)
_VERIFY_ALONE = (
    "verifies a program the test has checked already, so that a recursion "
    "budget wraps the verification alone; every stage that verifies checks "
    "first"
)
_CHECKER_ITSELF = (
    "reads the TypeChecker itself after its check, or its TypeEnv; "
    "pipeline.check hands back the checker's tables and naming environment, "
    "not the checker"
)
_SPY = (
    "spies on the compile `vera test` runs: it replaces vera.codegen.compile "
    "with a wrapper that calls the real one and keeps the WAT, so the compile "
    "it calls is the tester's own, measured where the tester makes it"
)

#: The drivers that stay, ``"tests/<file>::<helper>"`` (a method as
#: ``Class.method``) to the reason.
ALLOWED: Mapping[str, str] = {
    "tests/test_adt_eq_reject_928.py::_checker_env": _CHECKER_ITSELF,
    "tests/test_ambiguous_import_refusal_1304.py::_run_check_json": _HASH_SEED,
    "tests/test_ambiguous_import_refusal_1304.py::TestTheRefusedDataNamesBindToNothing._env": _CHECKER_ITSELF,
    "tests/test_cli.py::TestTypedArgParsingDirect._compile": _CLI_SUITE,
    "tests/test_codegen_decreases_guard.py::_run_cli": _NEVER_STOPS,
    "tests/test_codegen_root_lifetime_1371.py::_run_in_subprocess": _HOST_FAULT,
    "tests/test_conformance.py::_vera": _CLI_SMOKE,
    "tests/test_doc_annotations.py::_try_parse": _LARK_TREE,
    "tests/test_duplicate_names_1433.py::_checker_after_a_check": _CHECKER_ITSELF,
    "tests/test_effect_op_determinism.py::_run_seeded": _HASH_SEED,
    "tests/test_field_layout_one_source_1466.py::_run": _ANOTHER_TREE,
    "tests/test_html.py::_try_parse": _LARK_TREE,
    "tests/test_nonregular_data_rejected_1429.py::_cli": _DEADLINE,
    "tests/test_one_classifier_1503.py::_pipeline": _SUBSTITUTED_TABLE,
    "tests/test_overflow_fails_closed_1417.py::_compiled": _SUBSTITUTED_TABLE,
    "tests/test_readme.py::_try_parse": _LARK_TREE,
    "tests/test_resolver.py::_resolve_ok": _RESOLVER_UNIT,
    "tests/test_resolver.py::_resolve_err": _RESOLVER_UNIT,
    "tests/test_resolver.py::TestResolverErrorCodes._errors": _RESOLVER_UNIT,
    "tests/test_tester_artifacts.py::_cmd_test_capturing_wat": _SPY,
    "tests/test_verifier_cross_module_disclosure.py::_verify_checked": _VERIFY_ALONE,
    "tests/test_xmod_span_collision.py::_compile_main": _MODULE_TABLES_WITHHELD,
}


@dataclass(frozen=True)
class Driver:
    """One helper that drives a stage itself."""

    file: str
    helper: str
    line: int
    calls: tuple[str, ...]

    @property
    def key(self) -> str:
        return f"{self.file}::{self.helper}"


def _import_targets(nodes: Iterable[ast.AST]) -> dict[str, str]:
    """Each name an import binds, to the dotted path it binds it to."""
    names: dict[str, str] = {}
    for node in nodes:
        for sub in ast.walk(node):
            if isinstance(sub, ast.ImportFrom) and sub.module and not sub.level:
                for alias in sub.names:
                    names[alias.asname or alias.name] = f"{sub.module}.{alias.name}"
            elif isinstance(sub, ast.Import):
                for alias in sub.names:
                    if alias.asname:
                        names[alias.asname] = alias.name
                    else:
                        head = alias.name.split(".")[0]
                        names[head] = head
    return names


def _dotted(expr: ast.AST, names: Mapping[str, str]) -> str | None:
    """The imported path *expr* names, or ``None`` for anything else."""
    if isinstance(expr, ast.Name):
        return names.get(expr.id)
    if isinstance(expr, ast.Attribute):
        base = _dotted(expr.value, names)
        return f"{base}.{expr.attr}" if base is not None else None
    return None


def _names_vera(value: str) -> bool:
    """Whether a string in a command line names the ``vera`` CLI."""
    words = value.split()
    return (
        value in ("vera", "vera.cli")
        or (bool(words) and words[0] == "vera")
        or "-m vera" in value
        or "vera.cli" in value
        or value.replace("\\", "/").endswith("/vera")
    )


def _strings(node: ast.AST) -> Iterator[str]:
    """The strings in *node*, bar those a ``/`` joins into a path."""
    parts: set[int] = set()
    for sub in ast.walk(node):
        if isinstance(sub, ast.BinOp) and isinstance(sub.op, ast.Div):
            parts.update({id(sub.left), id(sub.right)})
    for sub in ast.walk(node):
        if (isinstance(sub, ast.Constant) and isinstance(sub.value, str)
                and id(sub) not in parts):
            yield sub.value


def _assigned(scope: Iterable[ast.AST]) -> dict[str, list[ast.AST]]:
    """Each name bound by an assignment in *scope*, to the values bound."""
    out: dict[str, list[ast.AST]] = {}
    for node in scope:
        for sub in ast.walk(node):
            if isinstance(sub, ast.Assign):
                for target in sub.targets:
                    if isinstance(target, ast.Name):
                        out.setdefault(target.id, []).append(sub.value)
            elif isinstance(sub, ast.AnnAssign) and sub.value is not None:
                if isinstance(sub.target, ast.Name):
                    out.setdefault(sub.target.id, []).append(sub.value)
    return out


def _names_used(nodes: Iterable[ast.AST]) -> set[str]:
    return {sub.id for node in nodes for sub in ast.walk(node)
            if isinstance(sub, ast.Name)}


def _command_names_vera(
    nodes: Iterable[ast.AST], local: Mapping[str, list[ast.AST]],
    module: Mapping[str, list[ast.AST]],
) -> bool:
    """Whether *nodes* name ``vera``: a string in them does, or one in a
    value a name in them was assigned (followed through assignments)."""
    seen: set[str] = set()
    pending: list[ast.AST] = list(nodes)
    while pending:
        node = pending.pop()
        if any(_names_vera(s) for s in _strings(node)):
            return True
        for name in _names_used([node]) - seen:
            seen.add(name)
            pending.extend(local.get(name, module.get(name, [])))
    return False


def _call_arguments(call: ast.Call) -> list[ast.AST]:
    return [*call.args, *(k.value for k in call.keywords)]


def _parameters(helper: ast.FunctionDef | ast.AsyncFunctionDef) -> set[str]:
    a = helper.args
    names = {x.arg for x in [*a.posonlyargs, *a.args, *a.kwonlyargs]}
    names.update(x.arg for x in (a.vararg, a.kwarg) if x is not None)
    return names


def _defaults(
    helper: ast.FunctionDef | ast.AsyncFunctionDef,
) -> dict[str, list[ast.AST]]:
    """Each parameter of *helper* that has a default, to that default."""
    a = helper.args
    positional = [*a.posonlyargs, *a.args]
    out: dict[str, list[ast.AST]] = {}
    for arg, default in zip(positional[len(positional) - len(a.defaults):],
                            a.defaults):
        out[arg.arg] = [default]
    for arg, kw_default in zip(a.kwonlyargs, a.kw_defaults):
        if kw_default is not None:
            out[arg.arg] = [kw_default]
    return out


def _iterated(scope: Iterable[ast.AST]) -> dict[str, list[ast.AST]]:
    """Each name a ``for`` loop or a comprehension binds in *scope*, to the
    iterables it is bound out of."""
    out: dict[str, list[ast.AST]] = {}
    for node in scope:
        for sub in ast.walk(node):
            if (isinstance(sub, (ast.For, ast.AsyncFor, ast.comprehension))
                    and isinstance(sub.target, ast.Name)):
                out.setdefault(sub.target.id, []).append(sub.iter)
    return out


def _entry_point(target: str | None) -> str | None:
    """The stage entry point the imported path *target* names: a stage
    function (its name), ``vera.cli.main`` or a ``vera.cli.cmd_*`` command;
    ``None`` for anything else."""
    if target is None:
        return None
    owner, _, name = target.rpartition(".")
    if name in STAGE_FUNCTIONS.get(owner, ()):
        return name
    if owner == "vera.cli" and (name == "main" or name.startswith("cmd_")):
        return f"vera.cli.{name}"
    return None


#: The methods that read a container's values: a lookup, or the values.
_CONTAINER_READS = frozenset({"get", "pop", "setdefault", "values"})


@dataclass(frozen=True)
class _Scope:
    """What a name means where a value is read: the paths its imports bind,
    the values assigned to it, the iterables a loop binds it out of, and,
    for the helper's own scope, its parameters and their defaults."""

    names: Mapping[str, str]
    local: Mapping[str, list[ast.AST]]
    iterated: Mapping[str, list[ast.AST]]
    module: Mapping[str, list[ast.AST]]
    params: frozenset[str] = frozenset()
    defaults: Mapping[str, list[ast.AST]] = field(default_factory=dict)


def _values(
    expr: ast.AST, scope: _Scope, seen: set[object],
) -> Iterator[ast.AST | None]:
    """Each expression *expr* can evaluate to, followed through the names
    it is bound to, the containers it is read out of and the operands it
    chooses between; ``None`` stands for a value a caller hands the helper."""
    if ("node", id(expr)) in seen:
        return
    seen.add(("node", id(expr)))
    if isinstance(expr, ast.Name):
        yield from _name_values(expr.id, scope, seen)
    elif isinstance(expr, ast.Subscript):
        yield from _elements(expr.value, scope, seen)
    elif (isinstance(expr, ast.Call) and isinstance(expr.func, ast.Attribute)
          and expr.func.attr in _CONTAINER_READS):
        yield from _elements(expr.func.value, scope, seen)
    elif isinstance(expr, ast.IfExp):
        yield from _values(expr.body, scope, seen)
        yield from _values(expr.orelse, scope, seen)
    elif isinstance(expr, ast.BoolOp):
        for operand in expr.values:
            yield from _values(operand, scope, seen)
    elif isinstance(expr, ast.NamedExpr):
        yield from _values(expr.value, scope, seen)
    else:
        yield expr


def _name_values(
    name: str, scope: _Scope, seen: set[object],
) -> Iterator[ast.AST | None]:
    if ("name", name) in seen:
        return
    seen.add(("name", name))
    local = scope.local.get(name, [])
    iterated = scope.iterated.get(name, [])
    if local or iterated or name in scope.params:
        for value in local:
            yield from _values(value, scope, seen)
        for iterable in iterated:
            yield from _elements(iterable, scope, seen)
        if name in scope.params:
            yield None
            for default in scope.defaults.get(name, []):
                yield from _values(default, scope, seen)
        return
    module = scope.module.get(name, [])
    for value in module:
        yield from _values(value, scope, seen)
    if not module:
        yield ast.Name(id=name, ctx=ast.Load())


def _elements(
    expr: ast.AST, scope: _Scope, seen: set[object],
) -> Iterator[ast.AST | None]:
    """The values held by each container *expr* can evaluate to."""
    for container in _values(expr, scope, seen):
        if container is None:
            yield None
        elif isinstance(container, ast.Dict):
            for value in container.values:
                yield from _values(value, scope, seen)
        elif isinstance(container, (ast.List, ast.Tuple, ast.Set)):
            for element in container.elts:
                if isinstance(element, ast.Starred):
                    yield from _elements(element.value, scope, seen)
                else:
                    yield from _values(element, scope, seen)


def _getattr_entry(value: ast.AST, names: Mapping[str, str]) -> str | None:
    """The entry point ``getattr(<module>, <name>)`` reads, for a module that
    holds stage entry points: the one it names, or ``getattr(<module>)``
    when the name is computed."""
    if not (isinstance(value, ast.Call) and isinstance(value.func, ast.Name)
            and value.func.id == "getattr" and len(value.args) >= 2):
        return None
    owner = _dotted(value.args[0], names)
    if owner != "vera.cli" and owner not in STAGE_FUNCTIONS:
        return None
    attribute = value.args[1]
    if isinstance(attribute, ast.Constant) and isinstance(attribute.value, str):
        return _entry_point(f"{owner}.{attribute.value}")
    return f"getattr({owner})"


def _reached(expr: ast.AST, scope: _Scope) -> tuple[set[str], bool]:
    """The stage entry points *expr* can evaluate to, and whether it can be
    a value a caller hands the helper."""
    found: set[str] = set()
    handed = False
    for value in _values(expr, scope, set()):
        if value is None:
            handed = True
            continue
        entry = (_entry_point(_dotted(value, scope.names))
                 or _getattr_entry(value, scope.names))
        if entry is not None:
            found.add(entry)
    return found, handed


def _stage_calls(
    helper: ast.FunctionDef | ast.AsyncFunctionDef, outer: Iterable[ast.AST],
    module: Mapping[str, list[ast.AST]],
) -> tuple[list[str], list[str], bool]:
    """The stage entry points *helper* calls, by name or through a value;
    the subprocess calls whose command reaches it through its parameters;
    and whether it calls a value a caller hands it."""
    names = _import_targets([*outer, helper])
    local = _assigned([helper])
    params = _parameters(helper)
    scope = _Scope(names, local, _iterated([helper]), module,
                   frozenset(params), _defaults(helper))
    found: list[str] = []
    handed: list[str] = []
    calls_a_handed_value = False
    for node in ast.walk(helper):
        if not isinstance(node, ast.Call):
            continue
        func = node.func
        if isinstance(func, ast.Attribute) and func.attr in STAGE_METHODS:
            found.append(func.attr)
            continue
        target = _dotted(func, names)
        entry = _entry_point(target)
        if entry is not None:
            found.append(entry)
            continue
        if target is not None:
            owner, _, name = target.rpartition(".")
            if owner == "subprocess" and name in SUBPROCESS_CALLS:
                arguments = _call_arguments(node)
                if _command_names_vera(arguments, local, module):
                    found.append(f"subprocess.{name} vera")
                elif _reaches(arguments, params, local):
                    handed.append(f"subprocess.{name} vera")
            continue
        reached, from_a_caller = _reached(func, scope)
        found.extend(reached)
        calls_a_handed_value = calls_a_handed_value or from_a_caller
    return sorted(set(found)), sorted(set(handed)), calls_a_handed_value


def _reaches(
    nodes: Iterable[ast.AST], params: set[str],
    local: Mapping[str, list[ast.AST]],
) -> bool:
    """Whether a parameter flows into *nodes*, through local assignments."""
    seen: set[str] = set()
    pending = _names_used(nodes)
    while pending:
        name = pending.pop()
        if name in params:
            return True
        if name in seen:
            continue
        seen.add(name)
        pending |= _names_used(local.get(name, []))
    return False


def _helpers(tree: ast.Module) -> Iterator[tuple[
    str, ast.FunctionDef | ast.AsyncFunctionDef, list[ast.AST],
]]:
    """``(name, function, enclosing scope)`` for each helper of a module."""
    top_imports: list[ast.AST] = [
        n for n in tree.body if isinstance(n, (ast.Import, ast.ImportFrom))]
    for node in tree.body:
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            if not node.name.startswith("test"):
                yield node.name, node, top_imports
        elif isinstance(node, ast.ClassDef):
            class_imports: list[ast.AST] = [
                n for n in node.body if isinstance(n, (ast.Import, ast.ImportFrom))]
            for member in node.body:
                if (isinstance(member, (ast.FunctionDef, ast.AsyncFunctionDef))
                        and not member.name.startswith("test")):
                    yield (f"{node.name}.{member.name}", member,
                           top_imports + class_imports)


def drivers_in(source: str, file: str) -> list[Driver]:
    """Every helper of the test module *source* that drives a stage itself."""
    tree = ast.parse(source, filename=file)
    module = _assigned([n for n in tree.body
                        if isinstance(n, (ast.Assign, ast.AnnAssign))])
    out: list[Driver] = []
    runners: dict[str, tuple[
        ast.FunctionDef | ast.AsyncFunctionDef, list[str], bool]] = {}
    for name, helper, outer in _helpers(tree):
        calls, handed, calls_a_handed_value = _stage_calls(helper, outer, module)
        if calls:
            out.append(Driver(file, name, helper.lineno, tuple(calls)))
        elif handed or calls_a_handed_value:
            runners[name] = (helper, handed, calls_a_handed_value)
    for name, (helper, handed, calls_a_handed_value) in runners.items():
        reached: set[str] = set()
        if handed and _handed_vera(tree, name, module):
            reached.update(handed)
        if calls_a_handed_value:
            reached |= _handed_entry_points(tree, name, module)
        if reached:
            out.append(Driver(file, name, helper.lineno, tuple(sorted(reached))))
    return sorted(out, key=lambda d: d.line)


class _Classes:
    """The module's top-level classes: the bases each names and the methods
    each defines, to place the method an attribute call reaches."""

    def __init__(self, tree: ast.Module) -> None:
        self.bases: dict[str, tuple[str, ...]] = {}
        self.methods: dict[str, frozenset[str]] = {}
        for node in tree.body:
            if isinstance(node, ast.ClassDef):
                self.bases[node.name] = tuple(
                    b.id for b in node.bases if isinstance(b, ast.Name))
                self.methods[node.name] = frozenset(
                    m.name for m in node.body
                    if isinstance(m, (ast.FunctionDef, ast.AsyncFunctionDef)))

    def reached(self, start: str, method: str) -> str | None:
        """The class whose *method* a lookup from *start* reaches, searching
        its module-local bases depth first, left to right."""
        seen: set[str] = set()

        def walk(name: str) -> str | None:
            if name in seen:
                return None
            seen.add(name)
            if method in self.methods.get(name, ()):
                return name
            for base in self.bases.get(name, ()):
                found = walk(base)
                if found is not None:
                    return found
            return None

        return walk(start)

    def definers(self, method: str) -> set[str]:
        return {name for name, methods in self.methods.items() if method in methods}


#: A receiver whose class the module does not show.
_UNPLACED = "<unplaced>"


def _receiver_class(
    receiver: ast.expr, method: str, owner: ast.ClassDef | None,
    local: Mapping[str, list[ast.AST]], module: Mapping[str, list[ast.AST]],
    classes: _Classes,
) -> str | None:
    """The class whose *method* ``receiver.method`` reaches; ``None`` when the
    receiver is placed and reaches none; ``_UNPLACED`` when the module does
    not show what the receiver is (a parameter, a fixture's value, an
    attribute)."""
    def made_by(value: ast.AST) -> str | None:
        if (isinstance(value, ast.Call) and isinstance(value.func, ast.Name)
                and value.func.id in classes.bases):
            return value.func.id
        return None

    if isinstance(receiver, ast.Name):
        if receiver.id in classes.bases:
            return classes.reached(receiver.id, method)
        if receiver.id in ("self", "cls") and owner is not None:
            return classes.reached(owner.name, method)
        makers = {made_by(v) for v in local.get(receiver.id, module.get(receiver.id, []))}
        makers.discard(None)
        if len(makers) == 1:
            return classes.reached(makers.pop() or "", method)
        return _UNPLACED
    if isinstance(receiver, ast.Call):
        if (isinstance(receiver.func, ast.Name) and receiver.func.id == "super"
                and owner is not None):
            for base in classes.bases.get(owner.name, ()):
                found = classes.reached(base, method)
                if found is not None:
                    return found
            return None
        maker = made_by(receiver)
        if maker is not None:
            return classes.reached(maker, method)
    return _UNPLACED


def _calls_the_runner(
    call: ast.Call, name: str, owner: ast.ClassDef | None,
    local: Mapping[str, list[ast.AST]], module: Mapping[str, list[ast.AST]],
    classes: _Classes,
) -> bool:
    """Whether *call* calls the runner *name* (``fn`` or ``Class.method``).

    A function is called by its bare name.  A method is called through any
    receiver whose lookup reaches it: its class or a subclass, ``self`` or
    ``cls`` in one, ``super()`` below one, or an instance one builds.  A
    receiver the module does not place, such as a fixture's value, reaches it
    when no other class in the module defines a method of that name; a
    same-named method of another class is a different method.
    """
    func = call.func
    if "." not in name:
        return isinstance(func, ast.Name) and func.id == name
    cls, method = name.split(".", 1)
    if not (isinstance(func, ast.Attribute) and func.attr == method):
        return False
    reached = _receiver_class(func.value, method, owner, local, module, classes)
    if reached == _UNPLACED:
        return classes.definers(method) == {cls}
    return reached == cls


def _handed_vera(
    tree: ast.Module, name: str, module: Mapping[str, list[ast.AST]],
) -> bool:
    """Whether a call to the runner *name* anywhere in *tree*, in a function,
    a class body or the module itself, hands it a command naming ``vera``.

    A name in the call is followed through the assignments of the scope the
    call is in: a function's, a class body's own (not its methods'), else the
    module's.
    """
    return any(
        _command_names_vera(_call_arguments(call), local, module)
        for call, _scope, local in _runner_calls(tree, name, module))


def _handed_entry_points(
    tree: ast.Module, name: str, module: Mapping[str, list[ast.AST]],
) -> set[str]:
    """The stage entry points the calls to the helper *name* in *tree* hand
    it: each argument, followed through the scope the call is in as a
    helper's own values are (its imports, its assignments and its loops)."""
    top = [n for n in tree.body if isinstance(n, (ast.Import, ast.ImportFrom))]
    out: set[str] = set()
    for call, scope_node, local in _runner_calls(tree, name, module):
        within = [scope_node] if scope_node is not None else []
        scope = _Scope(_import_targets([*top, *within]), local,
                       _iterated(within), module)
        for argument in _call_arguments(call):
            out |= _reached(argument, scope)[0]
    return out


def _runner_calls(
    tree: ast.Module, name: str, module: Mapping[str, list[ast.AST]],
) -> Iterator[tuple[ast.Call, ast.AST | None, Mapping[str, list[ast.AST]]]]:
    """Each call to the runner *name* anywhere in *tree*, in a function, a
    class body or the module itself, with the scope it is in and that
    scope's assignments: a function's, a class body's own (not its
    methods'), else none, so a name falls back to the module's."""
    calls: list[tuple[ast.Call, ast.AST | None, ast.ClassDef | None]] = []

    def visit(node: ast.AST, scope: ast.AST | None, owner: ast.ClassDef | None) -> None:
        for child in ast.iter_child_nodes(node):
            if isinstance(child, ast.Call):
                calls.append((child, scope, owner))
            if isinstance(child, (ast.FunctionDef, ast.AsyncFunctionDef)):
                visit(child, child, owner)
            elif isinstance(child, ast.ClassDef):
                visit(child, child, child)
            else:
                visit(child, scope, owner)

    visit(tree, None, None)
    classes = _Classes(tree)
    locals_of: dict[int, dict[str, list[ast.AST]]] = {}
    for call, scope, owner in calls:
        local: Mapping[str, list[ast.AST]] = {}
        if isinstance(scope, ast.ClassDef):
            local = locals_of.setdefault(id(scope), _assigned(
                [stmt for stmt in scope.body
                 if isinstance(stmt, (ast.Assign, ast.AnnAssign))]))
        elif scope is not None:
            local = locals_of.setdefault(id(scope), _assigned([scope]))
        if _calls_the_runner(call, name, owner, local, module, classes):
            yield call, scope, local


def scan(root: Path = ROOT) -> list[Driver]:
    """Every driver in ``tests/test_*.py`` under *root*."""
    out: list[Driver] = []
    for path in sorted((root / "tests").glob("test_*.py")):
        rel = path.relative_to(root).as_posix()
        out.extend(drivers_in(path.read_text(encoding="utf-8"), rel))
    return out


def problems(
    drivers: Iterable[Driver], allowed: Mapping[str, str],
) -> list[str]:
    """The drivers ``allowed`` does not name, then the entries that name no
    driver; empty when the suite drives the pipeline through
    ``tests/pipeline.py`` alone."""
    found = {d.key: d for d in drivers}
    out = [
        f"{d.file}:{d.line}: {d.helper} drives the pipeline itself "
        f"({', '.join(d.calls)}); drive it through tests/pipeline.py"
        for key, d in sorted(found.items()) if key not in allowed
    ]
    out += [
        f"ALLOWED names {key}, which drives no stage: delete the entry"
        for key in sorted(allowed) if key not in found
    ]
    out += [
        f"ALLOWED gives {key} no reason"
        for key, reason in sorted(allowed.items()) if not reason.strip()
    ]
    return out


def main(argv: list[str]) -> int:
    drivers = scan()
    if argv == ["--list"]:
        for d in drivers:
            print(f"{d.key}  ({', '.join(d.calls)})")
        return 0
    if argv:
        print("usage: check_test_drivers.py [--list]", file=sys.stderr)
        return 2
    found = problems(drivers, ALLOWED)
    if not found:
        print(f"check_test_drivers: OK — {len(drivers)} test helpers drive a "
              f"stage themselves, each allowed with its reason; every other "
              f"test drives the pipeline through tests/pipeline.py.")
        return 0
    print(f"check_test_drivers: {len(found)} problem(s).\n", file=sys.stderr)
    for line in found:
        print(f"  {line}", file=sys.stderr)
    return 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
