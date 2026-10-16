#!/usr/bin/env python3
"""Every test that asks whether a module holds a runtime check reads the record.

``CompileResult.emitted_checks`` is the record of the runtime checks a compiled
module holds, and ``tests/pipeline.py``'s ``checks`` reads it: whether a
module, or one of its functions, holds a check of a trap kind, from an
emitter, for an obligation, at a path, and how many.  The WAT text answers
only how a check is rendered.  The record is read back from the assembled
module, and ``tests/test_emitted_checks_1479.py`` and
``tests/test_named_traps_1479.py`` hold it to the signals the text calls.

This gate fails a site in ``tests/*.py`` that reads a check's signal out of
the text instead:

- a reference to ``signal_call_pattern``, ``TRAP_SIGNAL`` or
  ``CONTRACT_SIGNAL`` (``vera.trap_registry``'s pattern for a signal, and its
  two symbols), under whatever name a module imports it as;
- a string, other than a docstring or a string standing alone as a
  statement, that holds ``vera.trap`` or ``contract_fail`` once regex escapes
  are dropped: ``"call $vera.contract_fail" in wat``, ``wat.count("call
  $vera.trap")``, ``r"i32\\.const 2\\s+...call \\$vera\\.trap"``;
- a use, in another scope, of a name the module binds at its top level to
  one of these (a pattern, a table holding one, a helper building or reading
  one), or an import of such a name from the test module that binds it, so a
  pattern kept for one reason is not read for another unseen.

The gate's own tests (``SELF_TEST``) are not scanned: the sites in them are
source text planted for the gate to find.

``KEPT`` names each site that stays on the text, as
``"tests/<file>::<scope>::<shape>"``, with the reason it stays.  ``<scope>``
is the function the site is in (``Class.method``, ``outer.inner`` for a
nested one), the name a module-level assignment binds, or ``<module>``;
``<shape>`` is the name referred to, or the string's needle.  An entry that
names no site is an error, so the list only shrinks.

Usage:
    python scripts/check_record_assertions.py           # scan tests/*.py
    python scripts/check_record_assertions.py --list    # print every site found
"""

from __future__ import annotations

import ast
import sys
from collections.abc import Iterable, Iterator, Mapping
from dataclasses import dataclass
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

#: The trap registry's names for a signal's rendering.
NAMES = frozenset({"signal_call_pattern", "TRAP_SIGNAL", "CONTRACT_SIGNAL"})

#: What a string naming a signal holds, regex escapes dropped.
NEEDLES = ("vera.trap", "contract_fail")

_RECORD_ORACLE = (
    "the oracle that holds the record to the module: it counts the signals "
    "the text calls, per function and kind, against the record's entries, "
    "which is what lets every other test read the record"
)
_RENDERING = (
    "asserts how a check is rendered, which the record does not describe: "
    "the instructions around its signal and their order, or the import "
    "the signal is declared by"
)
_CLI_OUTPUT = (
    "reads the module `vera compile --wat` prints, which carries no record: "
    "the command, and the checker's tables it threads, are the subject"
)
_HOST_NAMES = (
    "names a function a host reads a trap's cause from, as a frame, a "
    "source-map key or a planted program function, not text in a module"
)
_OTHER_COLUMNS = (
    "reads the program and value columns of a table whose signal column "
    "names the import, and asks the text nothing"
)

#: The gate's own tests, which the scan skips: every site in them is source
#: text planted for the gate to find.
SELF_TEST = "tests/test_check_record_assertions.py"

_1479 = "tests/test_emitted_checks_1479.py::"
_NAMED = "tests/test_named_traps_1479.py::"
_EXN = "tests/test_exn_throw_payload_1268.py::"
_REGISTRY = "tests/test_builtin_registry.py::"

#: The sites that stay on the text, ``"tests/<file>::<scope>::<shape>"`` to
#: the reason.
KEPT: Mapping[str, str] = {
    "tests/test_cli.py::TestNatNarrowingCliThreading820."
    "test_compile_wat_array_elem_emits_narrowing_guard::signal_call_pattern":
        _CLI_OUTPUT,
    "tests/test_codegen_collections.py::TestWrapperHandleTagging578."
    "test_alloc_emits_heap_ceiling_guard::vera.trap": _RENDERING,
    _1479 + "_record_mismatches::signal_call_pattern": _RECORD_ORACLE,
    _1479 + "test_a_failed_closure_worklist_takes_its_records_with_it"
    "::_record_mismatches": _RECORD_ORACLE,
    _1479 + "test_a_program_string_that_spells_a_marker_is_left_alone"
    "::_record_mismatches": _RECORD_ORACLE,
    _1479 + "test_an_abandoned_measure_translation_leaves_no_record"
    "::_record_mismatches": _RECORD_ORACLE,
    _1479 + "test_the_record_matches_the_signals_in_the_module"
    "::signal_call_pattern": _RECORD_ORACLE,
    _1479 + "test_the_self_tail_prefix_records_its_measure_per_splice"
    "::_record_mismatches": _RECORD_ORACLE,
    _NAMED + "FAN_IN_CELLS::contract_fail": _RENDERING,
    _NAMED + "test_a_check_only_in_one_scope_still_links::FAN_IN_CELLS":
        _RENDERING,
    _NAMED + "test_a_check_only_in_one_scope_links_in_the_browser::FAN_IN_CELLS":
        _OTHER_COLUMNS,
    _NAMED + "test_a_check_only_in_one_scope_links_under_wasi::FAN_IN_CELLS":
        _OTHER_COLUMNS,
    _NAMED + "_HOST_READ_NAMES::contract_fail": _HOST_NAMES,
    _NAMED + "_FORGED_CELLS::_HOST_READ_NAMES": _HOST_NAMES,
    _NAMED + "test_a_function_named_like_a_host_read_frame_cannot_forge_the_kind"
    "::_FORGED_CELLS": _HOST_NAMES,
    _NAMED + "_SIGNAL_CALL::vera.trap": _RECORD_ORACLE,
    _NAMED + "_CONTRACT_CALL::contract_fail": _RECORD_ORACLE,
    _NAMED + "_signals_by_function::_SIGNAL_CALL": _RECORD_ORACLE,
    _NAMED + "_signals_by_function::_CONTRACT_CALL": _RECORD_ORACLE,
    _NAMED + "test_the_record_matches_every_signal_the_corpus_emits"
    "::_signals_by_function": _RECORD_ORACLE,
    "tests/test_runtime_traps.py::TestResolveTrapFrames516."
    "test_builtin_helpers_tagged_as_builtin::contract_fail": _HOST_NAMES,
    "tests/test_runtime_traps.py::TestSourceMapPopulation516."
    "test_no_spurious_entries_for_builtins::contract_fail": _HOST_NAMES,
    # The order of a module's import declarations, the signals' among them.
    _REGISTRY + "_EVERY_BUILTIN_IMPORTS::contract_fail": _RENDERING,
    _REGISTRY + "_EVERY_EFFECT_IMPORTS::contract_fail": _RENDERING,
    _REGISTRY + "test_the_declaration_order_is_the_bases::_EVERY_BUILTIN_IMPORTS":
        _RENDERING,
    _REGISTRY + "test_the_declaration_order_is_the_bases::_EVERY_EFFECT_IMPORTS":
        _RENDERING,
}


@dataclass(frozen=True)
class Site:
    """One place a test reads a check's signal out of the text."""

    file: str
    scope: str
    shape: str
    line: int

    @property
    def key(self) -> str:
        return f"{self.file}::{self.scope}::{self.shape}"


def _statement_strings(tree: ast.AST) -> set[int]:
    """The strings standing alone as statements: docstrings, and the
    attribute docstrings some modules write after an assignment."""
    return {
        id(node.value) for node in ast.walk(tree)
        if isinstance(node, ast.Expr) and isinstance(node.value, ast.Constant)
        and isinstance(node.value.value, str)
    }


def _watched(tree: ast.Module) -> dict[str, str]:
    """Each name a reference to the registry's signal names goes by in this
    module, to the registry's name: the names themselves, and the alias an
    import binds one to."""
    out = {name: name for name in NAMES}
    for node in ast.walk(tree):
        if isinstance(node, ast.ImportFrom):
            for alias in node.names:
                if alias.name in NAMES and alias.asname:
                    out[alias.asname] = alias.name
    return out


def _scoped(tree: ast.Module) -> Iterator[tuple[ast.AST, str]]:
    """Each node of *tree* with the scope it sits in."""
    def visit(node: ast.AST, scope: str) -> Iterator[tuple[ast.AST, str]]:
        for child in ast.iter_child_nodes(node):
            if isinstance(child, (ast.FunctionDef, ast.AsyncFunctionDef,
                                  ast.ClassDef)):
                inner = child.name if scope == "<module>" else f"{scope}.{child.name}"
                yield child, inner
                yield from visit(child, inner)
            elif scope == "<module>" and isinstance(child, (ast.Assign,
                                                            ast.AnnAssign)):
                targets = (child.targets if isinstance(child, ast.Assign)
                           else [child.target])
                names = [t.id for t in targets if isinstance(t, ast.Name)]
                bound = names[0] if names else scope
                yield child, bound
                yield from visit(child, bound)
            else:
                yield child, scope
                yield from visit(child, scope)

    return visit(tree, "<module>")


def _carrier_names(tree: ast.Module) -> set[str]:
    """The names at the module's top level that can carry a site to another
    scope: its assignments' targets, and its functions and classes other
    than the tests (``test*`` functions, ``Test*`` classes)."""
    out: set[str] = set()
    for node in tree.body:
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            if not node.name.startswith("test"):
                out.add(node.name)
        elif isinstance(node, ast.ClassDef):
            if not node.name.startswith("Test"):
                out.add(node.name)
        elif isinstance(node, (ast.Assign, ast.AnnAssign)):
            targets = node.targets if isinstance(node, ast.Assign) else [node.target]
            out.update(t.id for t in targets if isinstance(t, ast.Name))
    return out


def sites_in(source: str, file: str) -> list[Site]:
    """Every site in the test module *source* that reads a check's signal out
    of the text, one per scope, shape and line.

    A name the module binds at its top level to a site (a pattern, a table
    of patterns, a function that builds or reads one) carries it: each use
    of that name in another scope is a site too, its shape the name, so a
    pattern kept for one reason is not read for another unseen.
    """
    return _analysed(source, file)[0]


def _analysed(
    source: str, file: str,
) -> tuple[list[Site], set[str], list[tuple[ast.AST, str]]]:
    """:func:`sites_in`'s sites, the names that carry one, and the
    module's nodes with their scopes."""
    tree = ast.parse(source, filename=file)
    alone = _statement_strings(tree)
    watched = _watched(tree)
    nodes = list(_scoped(tree))
    found: dict[tuple[str, str, int], Site] = {}

    def add(node: ast.AST, scope: str, shape: str) -> None:
        line = getattr(node, "lineno", 0)
        found.setdefault((scope, shape, line), Site(file, scope, shape, line))

    for node, scope in nodes:
        shape: str | None = None
        if isinstance(node, ast.Name) and node.id in watched:
            shape = watched[node.id]
        elif isinstance(node, ast.Attribute) and node.attr in NAMES:
            shape = node.attr
        elif (isinstance(node, ast.Constant) and isinstance(node.value, str)
              and id(node) not in alone):
            text = node.value.replace("\\", "")
            shape = next((n for n in NEEDLES if n in text), None)
        if shape is not None:
            add(node, scope, shape)
    eligible = _carrier_names(tree)
    carriers: set[str] = set()
    while True:
        holding = {scope.split(".")[0] for scope, _shape, _line in found}
        new = (holding & eligible) - carriers
        if not new:
            break
        carriers |= new
        for node, scope in nodes:
            if (isinstance(node, ast.Name) and node.id in new
                    and scope.split(".")[0] != node.id):
                add(node, scope, node.id)
    return (sorted(found.values(), key=lambda s: (s.line, s.shape)),
            carriers, nodes)


def _imported_from(node: ast.ImportFrom) -> str | None:
    """The test module an import names, as ``tests.<name>``."""
    if node.level == 0 and node.module and node.module.startswith("tests."):
        return node.module
    if node.level == 1 and node.module:
        return f"tests.{node.module}"
    return None


def scan(root: Path = ROOT) -> list[Site]:
    """Every site in ``tests/*.py`` under *root*, bar the gate's own tests.

    An import of a name that carries a site in the test module it comes
    from is a site where it is imported, its shape the name.
    """
    analysed: dict[str, tuple[list[Site], set[str], list[tuple[ast.AST, str]]]] = {}
    for path in sorted((root / "tests").glob("*.py")):
        rel = path.relative_to(root).as_posix()
        if rel != SELF_TEST:
            analysed[rel] = _analysed(path.read_text(encoding="utf-8"), rel)
    carried = {rel.removesuffix(".py").replace("/", "."): carriers
               for rel, (_sites, carriers, _nodes) in analysed.items()}
    out: list[Site] = []
    for rel, (sites, _carriers, nodes) in analysed.items():
        imported = [
            Site(rel, scope, alias.name, node.lineno)
            for node, scope in nodes if isinstance(node, ast.ImportFrom)
            for alias in node.names
            if alias.name in carried.get(_imported_from(node) or "", set())]
        out.extend(sorted([*sites, *imported], key=lambda s: (s.line, s.shape)))
    return out


def problems(sites: Iterable[Site], kept: Mapping[str, str]) -> list[str]:
    """The sites ``kept`` does not name, then the entries that name no site;
    empty when every test asks the record what it answers."""
    by_key: dict[str, Site] = {}
    for site in sites:
        by_key.setdefault(site.key, site)
    out = [
        f"{s.file}:{s.line}: {s.scope} reads a check's signal out of the WAT "
        f"text ({s.shape}); ask the record through tests/pipeline.py's "
        f"checks(), or keep the site with its reason"
        for key, s in sorted(by_key.items()) if key not in kept
    ]
    out += [
        f"KEPT names {key}, which names no site: delete the entry"
        for key in sorted(kept) if key not in by_key
    ]
    out += [
        f"KEPT gives {key} no reason"
        for key, reason in sorted(kept.items()) if not reason.strip()
    ]
    return out


def main(argv: list[str]) -> int:
    sites = scan()
    if argv == ["--list"]:
        for s in sites:
            print(f"{s.file}:{s.line}  {s.key}")
        return 0
    if argv:
        print("usage: check_record_assertions.py [--list]", file=sys.stderr)
        return 2
    found = problems(sites, KEPT)
    if not found:
        kept = len({s.key for s in sites})
        print(f"check_record_assertions: OK — {kept} sites read a check's "
              f"signal out of the WAT text, each kept with its reason; every "
              f"other test asks the record.")
        return 0
    print(f"check_record_assertions: {len(found)} problem(s).\n", file=sys.stderr)
    for line in found:
        print(f"  {line}", file=sys.stderr)
    return 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
