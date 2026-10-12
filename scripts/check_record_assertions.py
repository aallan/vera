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
  one), so a pattern kept for one reason is not read for another unseen.

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

_MIGRATING = "moves to the record in the pull request that adds this gate"

#: The gate's own tests, which the scan skips: every site in them is source
#: text planted for the gate to find.
SELF_TEST = "tests/test_check_record_assertions.py"

_1479 = "tests/test_emitted_checks_1479.py::"
_NAMED = "tests/test_named_traps_1479.py::"
_EXN = "tests/test_exn_throw_payload_1268.py::"

#: The sites that stay on the text, ``"tests/<file>::<scope>::<shape>"`` to
#: the reason.
KEPT: Mapping[str, str] = {
    "tests/test_cli.py::TestNatIntWideningCliThreading820."
    "test_compile_wat_array_elem_emits_widen_guard::signal_call_pattern":
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
    _EXN + "TestARefinementDoesNotDisableTheWideningGuard."
    "test_both_guards_are_emitted::signal_call_pattern": _RENDERING,
    _EXN + "TestTheQualifiedArmObligatesAllThreeArms."
    "test_the_guard_the_obligation_promises_is_emitted::signal_call_pattern":
        _RENDERING,
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
    # MIGRATING: each file's sites leave as the file moves to the record.
    'tests/test_boundary_guard_correctness_1466.py::test_1439_a_state_write_over_a_handle_base_carries_its_guard::contract_fail':
        _MIGRATING,
    'tests/test_boundary_guard_correctness_1466.py::test_a_state_write_claims_exactly_the_guard_it_emits::contract_fail':
        _MIGRATING,
    'tests/test_boundary_guard_correctness_1466.py::test_the_record_and_registration_agree_about_a_state_cell::contract_fail':
        _MIGRATING,
    'tests/test_clause_binder_guard_1445.py::test_the_site_table_moves_both_halves_together::contract_fail':
        _MIGRATING,
    'tests/test_construction_guards_1426.py::TestAStoreAfterADestructureIsStillRecorded.test_the_store_is_recorded_wherever_it_is_guarded::contract_fail':
        _MIGRATING,
    'tests/test_construction_guards_1426.py::test_the_guard_is_in_the_module_not_only_in_the_run::contract_fail':
        _MIGRATING,
    'tests/test_exn_throw_payload_1268.py::TestARefinementDoesNotDisableTheWideningGuard.test_both_guards_are_emitted::contract_fail':
        _MIGRATING,
    'tests/test_family_naming.py::test_refined_nat_cell_emits_the_same_write_guards_as_its_base::contract_fail':
        _MIGRATING,
    'tests/test_family_naming.py::test_refined_nat_cell_emits_the_same_write_guards_as_its_base::signal_call_pattern':
        _MIGRATING,
    'tests/test_guard_completeness.py::TestARefinedIntElementCountsItsWideningGuardToo.test_and_the_module_really_does_guard_it.traps::signal_call_pattern':
        _MIGRATING,
    'tests/test_guard_completeness.py::TestNonPlainTypeArgBasesAreGuarded1036.test_a_function_typed_argument_base_is_guarded_too::contract_fail':
        _MIGRATING,
    'tests/test_guard_completeness.py::TestTheNarrowingGuardNamesItself754.test_the_signal_declares_its_own_import::signal_call_pattern':
        _MIGRATING,
    'tests/test_guard_completeness.py::TestTupleComponentSitesAreGuarded1416.test_the_construction_narrowing_is_guarded_at_the_store::signal_call_pattern':
        _MIGRATING,
    'tests/test_hetero_widen_tailcall.py::TestFix1DeadGuardUnderTailCall.test_match_tailcall_arm_wat_plain_call_then_live_guard::signal_call_pattern':
        _MIGRATING,
    'tests/test_nat_narrowing_return_differential.py::TestClosureNarrowingBoundary984.test_refined_return_single_guard_no_double::contract_fail':
        _MIGRATING,
    'tests/test_nat_narrowing_return_differential.py::TestRefinedNonPlainBaseParity1036.test_the_return_position_carries_the_guard_too::contract_fail':
        _MIGRATING,
    'tests/test_nested_container_guards.py::_ALL_CELLS::_cells':
        _MIGRATING,
    'tests/test_nested_container_guards.py::_CELLS::_ALL_CELLS':
        _MIGRATING,
    'tests/test_nested_container_guards.py::_GAP_CELLS::_ALL_CELLS':
        _MIGRATING,
    'tests/test_nested_container_guards.py::_LEAVES::_trap_kind':
        _MIGRATING,
    'tests/test_nested_container_guards.py::_LEAVES::contract_fail':
        _MIGRATING,
    'tests/test_nested_container_guards.py::_cells::_LEAVES':
        _MIGRATING,
    'tests/test_nested_container_guards.py::_trap_kind::vera.trap':
        _MIGRATING,
    'tests/test_nested_container_guards.py::test_a_map_value_outside_a_let_is_guarded_but_not_yet_recorded::_GAP_CELLS':
        _MIGRATING,
    'tests/test_nested_container_guards.py::test_a_map_value_outside_a_let_is_guarded_but_not_yet_recorded::_LEAVES':
        _MIGRATING,
    'tests/test_nested_container_guards.py::test_every_recorded_guard_is_emitted_and_every_emitted_guard_recorded::_ALL_CELLS':
        _MIGRATING,
    'tests/test_nested_container_guards.py::test_every_recorded_guard_is_emitted_and_every_emitted_guard_recorded::_LEAVES':
        _MIGRATING,
    'tests/test_nested_container_guards.py::test_the_matrix_covers_every_position_and_depth::_ALL_CELLS':
        _MIGRATING,
    'tests/test_nested_container_guards.py::test_the_matrix_covers_every_position_and_depth::_CELLS':
        _MIGRATING,
    'tests/test_nested_container_guards.py::test_the_matrix_covers_every_position_and_depth::_LEAVES':
        _MIGRATING,
    'tests/test_overflow_fails_closed_1417.py::test_an_unnameable_width_is_guarded_as_int::signal_call_pattern':
        _MIGRATING,
    'tests/test_overflow_fails_closed_1417.py::test_the_table_less_fallback_still_names_a_width::signal_call_pattern':
        _MIGRATING,
    'tests/test_verifier_truth_consult_status.py::test_1362_the_claim_and_the_module_agree::signal_call_pattern':
        _MIGRATING,
    'tests/test_widen_trap_kind_1438.py::TestTheWideningGuardNamesItself.test_a_widening_inside_a_closure_body_still_links::signal_call_pattern':
        _MIGRATING,
    'tests/test_widen_trap_kind_1438.py::TestTheWideningGuardNamesItself.test_the_wasi_component_wires_the_shim_and_still_instantiates::signal_call_pattern':
        _MIGRATING,
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
    return sorted(found.values(), key=lambda s: (s.line, s.shape))


def scan(root: Path = ROOT) -> list[Site]:
    """Every site in ``tests/*.py`` under *root*, bar the gate's own tests."""
    out: list[Site] = []
    for path in sorted((root / "tests").glob("*.py")):
        rel = path.relative_to(root).as_posix()
        if rel != SELF_TEST:
            out.extend(sites_in(path.read_text(encoding="utf-8"), rel))
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
