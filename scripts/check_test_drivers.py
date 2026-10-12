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
- a stage method (``STAGE_METHODS``): ``CodeGenerator.compile_program``,
  ``ContractVerifier.verify_program``, ``ModuleResolver.resolve_imports``;
- ``vera.cli.main`` or a ``vera.cli.cmd_*`` command;
- a subprocess (``subprocess.run``, ``Popen``, ``check_output``, ``call``,
  ``check_call``) whose command names ``vera``: a string in it, or in a value
  a name in it was assigned, is ``vera`` or ``vera.cli``, starts with the
  word ``vera``, holds ``-m vera`` or ``vera.cli`` (a ``python -c`` script
  that imports the CLI), or is a path ending in ``/vera``.  A path built with
  ``/`` names nothing by its parts.  A helper that runs a command it is
  handed drives a stage when a call to it in the same module hands it one.

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
from dataclasses import dataclass
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
STAGE_METHODS = frozenset({"compile_program", "verify_program", "resolve_imports"})

SUBPROCESS_CALLS = frozenset({"run", "Popen", "check_output", "call", "check_call"})

_PART_B = (
    "runs the CLI as a process; the subprocess migration moves it in process "
    "through pipeline.cli"
)
_PART_A2 = "migrates to tests/pipeline.py in the second half of the driver migration"
_OTHER_CHANGE = (
    "in a file another change in this release holds (tests/test_cli.py, "
    "tests/test_check_*.py); it migrates with the second half of the driver "
    "migration"
)

#: The drivers that stay, ``"tests/<file>::<helper>"`` (a method as
#: ``Class.method``) to the reason.
ALLOWED: Mapping[str, str] = {
    "tests/test_adt_eq_reject_928.py::_codegen_gen": _PART_A2,
    "tests/test_adt_membership_scope_1253.py::_slot_tables": _PART_A2,
    "tests/test_adt_ord_reject_921.py::_error_descs": _PART_A2,
    "tests/test_alias_application_refinement_base_1237.py::_verify": _PART_A2,
    "tests/test_alias_application_refinement_base_1237.py::_run": _PART_A2,
    "tests/test_ambiguous_import_refusal_1304.py::_run_check_json": _PART_B,
    "tests/test_binder_position_generator.py::_cli": _PART_B,
    "tests/test_boundary_guard_correctness_1466.py::_cli": _PART_B,
    "tests/test_browser.py::_compile_vera": _PART_A2,
    "tests/test_browser.py::_compile_state_default": _PART_A2,
    "tests/test_browser.py::_compile_file": _PART_A2,
    "tests/test_callee_contract_scope_1220_1225_1226.py::_verify_mod": _PART_A2,
    "tests/test_callee_contract_scope_1220_1225_1226.py::_run_mod": _PART_A2,
    "tests/test_callee_contract_scope_1220_1225_1226.py::TestObligationsCarryTheirDeclaringFile._verified": _PART_A2,
    "tests/test_check_implies_compile.py::build": _OTHER_CHANGE,
    "tests/test_check_implies_compile.py::run_main": _OTHER_CHANGE,
    "tests/test_check_implies_compile.py::prelude_generics": _OTHER_CHANGE,
    "tests/test_check_implies_compile.py::_emitted_and_discovered": _OTHER_CHANGE,
    "tests/test_check_implies_compile.py::_verify_file": _OTHER_CHANGE,
    "tests/test_checker_apply_fn.py::_compile_and_run": _PART_A2,
    "tests/test_checker_int_nat.py::_synth_type": _PART_A2,
    "tests/test_checker_modules.py::TestReservedTypePrefix._codes": _PART_A2,
    "tests/test_checker_modules.py::TestReservedTypePrefix._diag": _PART_A2,
    "tests/test_clause_binder_guard_1445.py::_cli": _PART_B,
    "tests/test_cli.py::TestTypedArgParsingDirect._compile": _OTHER_CHANGE,
    "tests/test_clone_body_declaring_module_1241_1243.py::_cli": _PART_B,
    "tests/test_clone_decreases_1569.py::_verify": _PART_A2,
    "tests/test_closure_boundary_widths_1255_1256_1269.py::_compile_xmod": _PART_A2,
    "tests/test_codegen_decreases_guard.py::_run_cli": _PART_B,
    "tests/test_codegen_invariant_e699.py::_compile_source": _PART_A2,
    "tests/test_codegen_modules.py::TestCrossModuleCodegen._compile_mod": _PART_A2,
    "tests/test_codegen_modules.py::TestTransitiveModuleImport890._compile_run_chain": _PART_A2,
    "tests/test_codegen_monomorphize.py::_transform_program": _PART_A2,
    "tests/test_codegen_nested_nullary_ctor_994.py::_check_compile_run": _PART_A2,
    "tests/test_codegen_root_lifetime_1371.py::_run_in_subprocess": _PART_B,
    "tests/test_codegen_typeparam_unit_wildcard_1060.py::_compile_with_module": _PART_A2,
    "tests/test_codegen_where_helper_mangling_991.py::_compile": _PART_A2,
    "tests/test_conformance.py::_vera": _PART_B,
    "tests/test_construction_guards_1426.py::_cli": _PART_B,
    "tests/test_cross_namespace_ctor_1436.py::_emitted_and_discovered": _PART_A2,
    "tests/test_db_marshalling.py::_gc_caller": _PART_A2,
    "tests/test_disclosure_taint_follows_value_1406.py::_cli": _PART_B,
    "tests/test_disclosure_taint_follows_value_1406.py::_cli_unpatched": _PART_B,
    "tests/test_distrust_corpus.py::_tested": _PART_A2,
    "tests/test_doc_annotations.py::_try_parse": _PART_A2,
    "tests/test_duplicate_names_1433.py::_checker_after_a_check": _PART_A2,
    "tests/test_duplicate_names_1433.py::_check": _PART_A2,
    "tests/test_effect_op_determinism.py::_run_seeded": _PART_B,
    "tests/test_element_facts_statable_1430.py::_cli": _PART_B,
    "tests/test_emitted_checks_1479.py::_compile": _PART_A2,
    "tests/test_evaluated_position_obligations_1480.py::_verify": _PART_A2,
    "tests/test_evaluated_position_obligations_1480.py::_run": _PART_A2,
    "tests/test_evaluated_position_obligations_1480.py::_cli_json": _PART_B,
    "tests/test_evaluated_position_obligations_1480.py::_e529_rationale": _PART_A2,
    "tests/test_examples_ephemeris.py::obligations": _PART_A2,
    "tests/test_examples_ephemeris.py::_obligations_at_budget": _PART_A2,
    "tests/test_execute_characterization.py::_compile": _PART_A2,
    "tests/test_family_naming.py::_compile_path": _PART_A2,
    "tests/test_field_layout_one_source_1466.py::_run": _PART_B,
    "tests/test_float64_builtins_807.py::_run_float_expr": _PART_A2,
    "tests/test_float64_builtins_807.py::_run_int_expr": _PART_A2,
    "tests/test_generic_under_generic_callees_1223.py::_registered_and_resolved": _PART_A2,
    "tests/test_generic_where_helper_990.py::_compile": _PART_A2,
    "tests/test_guard_completeness.py::_cli": _PART_B,
    "tests/test_guard_completeness.py::_observe_in_process": _PART_A2,
    "tests/test_handle_exn_divergent_result_1276.py::_compile": _PART_A2,
    "tests/test_html.py::_try_parse": _PART_A2,
    "tests/test_html.py::_run_cli": _PART_B,
    "tests/test_import_visibility_entry_point_1244.py::_cli": _PART_B,
    "tests/test_infer_vera_type_join_1286.py::_compile": _PART_A2,
    "tests/test_int_overflow_codegen.py::_compile_multifile": _PART_A2,
    "tests/test_int_overflow_differential.py::_assert_in_lockstep": _PART_A2,
    "tests/test_int_widening_differential.py::_run": _PART_A2,
    "tests/test_literal_typing_from_context_1541_1565.py::_codes": _PART_A2,
    "tests/test_literal_typing_from_context_1541_1565.py::_run": _PART_A2,
    "tests/test_literal_typing_from_context_1541_1565.py::_compile": _PART_A2,
    "tests/test_literal_typing_from_context_1541_1565.py::_widening_sites": _PART_A2,
    "tests/test_module_environment_1493.py::_generator": _PART_A2,
    "tests/test_module_environment_1493.py::_multi_module_corpus": _PART_A2,
    "tests/test_module_environment_1493.py::_constructions": _PART_A2,
    "tests/test_module_generic_collision_1281.py::TestQualifiedOnlyGenericsAreKeyedPerOwner._diamond_registries": _PART_A2,
    "tests/test_module_generic_namespace_1274.py::_build": _PART_A2,
    "tests/test_module_generic_namespace_1274.py::TestTransitiveVisibility._resolve": _PART_A2,
    "tests/test_module_shadowed_generic_effect_op_1310.py::_discovered_sets": _PART_A2,
    "tests/test_monomorphize_differential.py::_codegen_emitted": _PART_A2,
    "tests/test_monomorphize_differential.py::_discovery_scopes": _PART_A2,
    "tests/test_monomorphize_differential.py::_cross_module_sets": _PART_A2,
    "tests/test_monomorphize_differential.py::_call_rewrite_desync": _PART_A2,
    "tests/test_named_traps_1479.py::_compile": _PART_A2,
    "tests/test_naming_env_provenance_1208.py::_verify_mod": _PART_A2,
    "tests/test_naming_env_provenance_1208.py::_compile_mod": _PART_A2,
    "tests/test_naming_env_provenance_1208.py::TestVerifierScopeIsTheSlotTableScope._declared_slots": _PART_A2,
    "tests/test_naming_env_provenance_1208.py::_codegen_alias_env": _PART_A2,
    "tests/test_naming_env_provenance_1208.py::_codegen_env": _PART_A2,
    "tests/test_nat_bind_construction_soundness_1332.py::_cli": _PART_B,
    "tests/test_nat_narrowing_return_differential.py::_resolved_pipeline": _PART_A2,
    "tests/test_nat_narrowing_return_differential.py::_return_nat_bind_statuses": _PART_A2,
    "tests/test_nat_narrowing_return_differential.py::_statuses_and_wat": _PART_A2,
    "tests/test_nat_narrowing_return_differential.py::_run": _PART_A2,
    "tests/test_nat_narrowing_return_differential.py::_trap_kind": _PART_A2,
    "tests/test_nat_narrowing_return_differential.py::_refine_bind_statuses": _PART_A2,
    "tests/test_nat_narrowing_return_differential.py::_trap_message": _PART_A2,
    "tests/test_nat_narrowing_return_differential.py::_obligation_kinds_statuses": _PART_A2,
    "tests/test_nat_narrowing_return_differential.py::TestClauseClassCollisionBothDirections._compile_msgs": _PART_A2,
    "tests/test_nested_container_guards.py::_measure": _PART_A2,
    "tests/test_nested_ctor_sort_1360.py::_cli": _PART_B,
    "tests/test_nested_ctor_sort_1360.py::_envelope_for_raising_translator": _PART_A2,
    "tests/test_nonregular_data_rejected_1429.py::_cli": _PART_B,
    "tests/test_obligations.py::_cold_verify": _PART_A2,
    "tests/test_obligations.py::TestObligationKinds._verify_source": _PART_A2,
    "tests/test_obligations.py::TestIncrementalInvalidation._cold": _PART_A2,
    "tests/test_one_classifier_1503.py::_artifacts": _PART_A2,
    "tests/test_one_classifier_1503.py::_observe": _PART_A2,
    "tests/test_one_classifier_1503.py::TestEveryNatResultIsDeclared._assert_widens": _PART_A2,
    "tests/test_one_classifier_1503.py::_verify_only": _PART_A2,
    "tests/test_one_classifier_1503.py::_compile_checked": _PART_A2,
    "tests/test_one_classifier_1503.py::_observe_modules": _PART_A2,
    "tests/test_one_classifier_1503.py::_pipeline": _PART_A2,
    "tests/test_overflow_fails_closed_1417.py::_compiled": _PART_A2,
    "tests/test_parser.py::TestVerifyFile._vera_verify_errors": _PART_A2,
    "tests/test_per_owner_adt_identity_1317.py::_generator": _PART_A2,
    "tests/test_phantom_generic_instances_1271.py::_compile_spied": _PART_A2,
    "tests/test_prelude.py::_make_program": _PART_A2,
    "tests/test_prelude_adt_namespace_1277.py::_compile": _PART_A2,
    "tests/test_prelude_adt_namespace_1277.py::_checker_data_types": _PART_A2,
    "tests/test_prelude_decl_stamp_1287.py::_compiled": _PART_A2,
    "tests/test_readme.py::_try_parse": _PART_A2,
    "tests/test_reconciliation.py::_cli_json": _PART_A2,
    "tests/test_refinement_binder_convergence_1208.py::_compile_mod": _PART_A2,
    "tests/test_refinement_binder_convergence_1208.py::_generator": _PART_A2,
    "tests/test_refinement_chain_convergence.py::_both_oracles": _PART_A2,
    "tests/test_refinement_chain_convergence.py::_records_at_the_bind": _PART_B,
    "tests/test_refinement_chain_convergence.py::_clause_binder_records": _PART_B,
    "tests/test_resolver.py::_resolve_ok": _PART_A2,
    "tests/test_resolver.py::_resolve_err": _PART_A2,
    "tests/test_resolver.py::TestResolverErrorCodes._errors": _PART_A2,
    "tests/test_runtime_traps.py::TestSourceMapPopulation516._compile": _PART_A2,
    "tests/test_runtime_traps.py::TestHostErrorDebugKnob1302._compile": _PART_A2,
    "tests/test_runtime_traps.py::TestHostCallbackBaseExceptionBoundary1302._compile": _PART_A2,
    "tests/test_self_qualified_calls_1558.py::_emitted_and_discovered": _PART_A2,
    "tests/test_self_qualified_calls_1558.py::_wat": _PART_A2,
    "tests/test_single_source_type_names.py::_check": _PART_A2,
    "tests/test_single_source_type_names.py::_compile_checked": _PART_A2,
    "tests/test_single_source_type_names.py::_discovery_differential": _PART_A2,
    "tests/test_single_source_type_names.py::_discovery_differential_modules": _PART_A2,
    "tests/test_slot_naming_blast_radius.py::_compile_file": _PART_A2,
    "tests/test_slot_naming_blast_radius.py::_run_files": _PART_A2,
    "tests/test_stress.py::_run": _PART_A2,
    "tests/test_string_length_soundness.py::_verify": _PART_A2,
    "tests/test_termination_rule.py::_check": _PART_A2,
    "tests/test_termination_rule.py::_compile": _PART_A2,
    "tests/test_termination_rule.py::_decreases_status": _PART_A2,
    "tests/test_termination_rule.py::_refine_verdict": _PART_A2,
    "tests/test_tester.py::_test": _PART_A2,
    "tests/test_tester_artifacts.py::_cmd_test_capturing_wat": _PART_A2,
    "tests/test_tester_coverage.py::TestUntranslatableRequiresSkips._json": _PART_A2,
    "tests/test_tester_distrust.py::_run": _PART_A2,
    "tests/test_tester_distrust.py::_checks": _PART_A2,
    "tests/test_tester_distrust.py::_index": _PART_A2,
    "tests/test_tester_distrust.py::_cli_json": _PART_A2,
    "tests/test_tester_distrust.py::_main": _PART_A2,
    "tests/test_uninferred_type_arg_e622.py::_compile_checked": _PART_A2,
    "tests/test_verifier_adt_decreases.py::TestWalkerBlindSpots1179._decreases_statuses": _PART_A2,
    "tests/test_verifier_assert_subpattern_facts.py::_cli": _PART_B,
    "tests/test_verifier_budget.py::TestCliFlag._run": _PART_B,
    "tests/test_verifier_budget.py::TestBudgetReachesTheSolver._cold": _PART_A2,
    "tests/test_verifier_call_arg_payload_1410.py::_cli": _PART_B,
    "tests/test_verifier_calls_modules.py::TestCrossModuleVerification._verify_mod": _PART_A2,
    "tests/test_verifier_coverage.py::_verify": _PART_A2,
    "tests/test_verifier_cross_module_disclosure.py::_cli": _PART_B,
    "tests/test_verifier_cross_module_disclosure.py::_checked": _PART_A2,
    "tests/test_verifier_cross_module_disclosure.py::_verify_checked": _PART_A2,
    "tests/test_verifier_premise_consistency_1451.py::_cli": _PART_B,
    "tests/test_verifier_premise_consistency_1451.py::_verify_in_process": _PART_A2,
    "tests/test_verifier_refined_sort_derivation.py::_cli": _PART_B,
    "tests/test_verifier_refinement_chain_1434.py::_cli": _PART_B,
    "tests/test_verifier_truth_consult_status.py::_cli": _PART_B,
    "tests/test_verifier_where_helper_scope_991.py::_run": _PART_A2,
    "tests/test_warning_severity_1513.py::_registry_codes": _PART_A2,
    "tests/test_wasi_target.py::_compile_path": _PART_A2,
    "tests/test_where_helper_call_boundary_1455.py::_cli": _PART_B,
    "tests/test_where_helper_call_boundary_1455.py::_oracle_readings": _PART_A2,
    "tests/test_xmod_artifact_collection.py::_resolve": _PART_A2,
    "tests/test_xmod_generic_widen_gap.py::_lib_tier3_count": _PART_A2,
    "tests/test_xmod_span_collision.py::_compile_main": _PART_A2,
    "tests/test_xmod_where_helper_import_991.py::_compile_main": _PART_A2,
    "tests/test_xmod_widening_differential.py::_lib_tier3_count": _PART_A2,
    "tests/test_xmod_widening_differential.py::_compile_main": _PART_A2,
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


def _dotted(expr: ast.expr, names: Mapping[str, str]) -> str | None:
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


def _stage_calls(
    helper: ast.FunctionDef | ast.AsyncFunctionDef, outer: Iterable[ast.AST],
    module: Mapping[str, list[ast.AST]],
) -> tuple[list[str], list[str]]:
    """The stage entry points *helper* calls, by name, and the subprocess
    calls whose command reaches it through its parameters."""
    names = _import_targets([*outer, helper])
    local = _assigned([helper])
    params = _parameters(helper)
    found: list[str] = []
    handed: list[str] = []
    for node in ast.walk(helper):
        if not isinstance(node, ast.Call):
            continue
        func = node.func
        if isinstance(func, ast.Attribute) and func.attr in STAGE_METHODS:
            found.append(func.attr)
            continue
        target = _dotted(func, names)
        if target is None:
            continue
        owner, _, name = target.rpartition(".")
        if name in STAGE_FUNCTIONS.get(owner, ()):
            found.append(name)
        elif owner == "vera.cli" and (name == "main" or name.startswith("cmd_")):
            found.append(f"vera.cli.{name}")
        elif owner == "subprocess" and name in SUBPROCESS_CALLS:
            arguments = _call_arguments(node)
            if _command_names_vera(arguments, local, module):
                found.append(f"subprocess.{name} vera")
            elif _reaches(arguments, params, local):
                handed.append(f"subprocess.{name} vera")
    return sorted(set(found)), sorted(set(handed))


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
    runners: dict[str, tuple[ast.FunctionDef | ast.AsyncFunctionDef, list[str]]] = {}
    for name, helper, outer in _helpers(tree):
        calls, handed = _stage_calls(helper, outer, module)
        if calls:
            out.append(Driver(file, name, helper.lineno, tuple(calls)))
        elif handed:
            runners[name] = (helper, handed)
    for name, (helper, handed) in runners.items():
        if _handed_vera(tree, name, module):
            out.append(Driver(file, name, helper.lineno, tuple(handed)))
    return sorted(out, key=lambda d: d.line)


def _handed_vera(
    tree: ast.Module, name: str, module: Mapping[str, list[ast.AST]],
) -> bool:
    """Whether a call to the helper *name* anywhere in *tree* hands it a
    command naming ``vera``."""
    bare = name.rsplit(".", 1)[-1]
    for scope in ast.walk(tree):
        if not isinstance(scope, (ast.FunctionDef, ast.AsyncFunctionDef)):
            continue
        local = _assigned([scope])
        for node in ast.walk(scope):
            if not isinstance(node, ast.Call):
                continue
            func = node.func
            called = (func.id if isinstance(func, ast.Name)
                      else func.attr if isinstance(func, ast.Attribute) else None)
            if called == bare and _command_names_vera(
                    _call_arguments(node), local, module):
                return True
    return False


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
