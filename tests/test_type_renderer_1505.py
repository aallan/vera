"""One type renderer: a type argument has no `@` (#1505; ROADMAP Stage 26).

`ast.format_type_expr` rendered a type as `@Name` and each of its arguments
by calling itself, so every argument took an `@` of its own: diagnostics,
obligation descriptions and runtime contract messages showed
`@Array<@Int>.0`, which does not parse.  It also elided a refinement's
predicate, so a signature whose parameters differ only in a refinement read
as one type.  The renderer gives the head its `@` and an argument none, and
renders a type whole, so what a message shows parses back to what the source
wrote.

The ``repro`` cells are the issue's outputs; the round-trip cell renders every
type expression and slot reference of the corpus and parses each back.
"""

from __future__ import annotations

import json
from pathlib import Path

import pytest

from tests import pipeline
from vera import ast as vast
from dataclasses import fields

pytestmark = pytest.mark.matrix(decides=["vera/ast.py", "vera/lsp/workflows.py"])

_ROOT = Path(__file__).resolve().parents[1]

#: Red at 94cef528, each as the issue describes: the seven named cells, and
#: the 122 corpus programs (of 323) whose round trip fails.  Strict, so the
#: renderer's commit, which deletes the marks, is forced to flip every one.
_RED = pytest.mark.xfail(strict=True, reason="#1505: red at 94cef528")
_RED_AT_BASE = frozenset({
    "examples/array_utilities.vera",
    "examples/async_futures.vera",
    "examples/async_http_fanout.vera",
    "examples/closures.vera",
    "examples/collections.vera",
    "examples/copy_bytes.vera",
    "examples/database.vera",
    "examples/ephemeris.vera",
    "examples/generics.vera",
    "examples/http.vera",
    "examples/http_server.vera",
    "examples/inference.vera",
    "examples/inference_json.vera",
    "examples/json.vera",
    "examples/life.vera",
    "examples/list_ops.vera",
    "examples/markdown.vera",
    "examples/maximum_syntax.vera",
    "examples/nested_closures.vera",
    "examples/pattern_matching.vera",
    "examples/quantifiers.vera",
    "examples/refinement_types.vera",
    "examples/regex.vera",
    "examples/scoreboard.vera",
    "examples/sqlitedb.vera",
    "examples/vera/collections.vera",
    "tests/conformance/ch02_adt_recursive.vera",
    "tests/conformance/ch02_adt_tuple_recursive.vera",
    "tests/conformance/ch02_byte_refinement.vera",
    "tests/conformance/ch02_generic_arg_branch_join.vera",
    "tests/conformance/ch02_generics.vera",
    "tests/conformance/ch02_map_unit_value_rejected.vera",
    "tests/conformance/ch02_nonregular_data_rejected.vera",
    "tests/conformance/ch02_option_result.vera",
    "tests/conformance/ch02_refinement_base_param_alias.vera",
    "tests/conformance/ch02_refinement_types.vera",
    "tests/conformance/ch02_tuple_basic.vera",
    "tests/conformance/ch02_tuple_unit_component.vera",
    "tests/conformance/ch02_type_alias_array.vera",
    "tests/conformance/ch03_mono_collapse_reindex.vera",
    "tests/conformance/ch03_slot_alias_type_argument.vera",
    "tests/conformance/ch03_slot_let_chains.vera",
    "tests/conformance/ch04_array_construction.vera",
    "tests/conformance/ch04_array_ops.vera",
    "tests/conformance/ch04_match_nested.vera",
    "tests/conformance/ch04_match_nested_missing.vera",
    "tests/conformance/ch04_match_pair_scrutinee.vera",
    "tests/conformance/ch04_nat_binding.vera",
    "tests/conformance/ch04_nested_option_ctor.vera",
    "tests/conformance/ch04_primitive_obligations.vera",
    "tests/conformance/ch04_short_circuit.vera",
    "tests/conformance/ch05_apply_fn_arity.vera",
    "tests/conformance/ch05_apply_fn_typing.vera",
    "tests/conformance/ch05_capture_array_index.vera",
    "tests/conformance/ch05_closure_nat_return.vera",
    "tests/conformance/ch05_closures.vera",
    "tests/conformance/ch05_generic_pipe_monomorph.vera",
    "tests/conformance/ch05_nested_closures.vera",
    "tests/conformance/ch05_nested_fn_type_alias.vera",
    "tests/conformance/ch05_unit_arg_closure.vera",
    "tests/conformance/ch06_adt_sort_disambiguation.vera",
    "tests/conformance/ch06_composite_postcondition_eq.vera",
    "tests/conformance/ch06_decreases.vera",
    "tests/conformance/ch06_quantifier_array_domain_rejected.vera",
    "tests/conformance/ch06_quantifiers.vera",
    "tests/conformance/ch07_exn_composite.vera",
    "tests/conformance/ch07_exn_param_alias.vera",
    "tests/conformance/ch07_exn_payload_guard.vera",
    "tests/conformance/ch07_handler_effect_unlowerable.vera",
    "tests/conformance/ch07_state_alias_chain.vera",
    "tests/conformance/ch07_state_alias_op_result_positions.vera",
    "tests/conformance/ch07_state_clause_alias_slots.vera",
    "tests/conformance/ch07_state_composite.vera",
    "tests/conformance/ch07_state_composite_alias.vera",
    "tests/conformance/ch07_state_composite_alias_cross_spelling.vera",
    "tests/conformance/ch07_state_fn_type_alias_cross_spelling.vera",
    "tests/conformance/ch07_state_nested_param_alias.vera",
    "tests/conformance/ch07_state_old_composite.vera",
    "tests/conformance/ch07_state_op_array_element.vera",
    "tests/conformance/ch07_state_op_generic_instantiation.vera",
    "tests/conformance/ch07_state_refined_cell_family.vera",
    "tests/conformance/ch08_ctor_field_module_call.vera",
    "tests/conformance/ch08_prelude_adt_name_alias.vera",
    "tests/conformance/ch08_reserved_vera_prefix_reference_rejected.vera",
    "tests/conformance/ch08_state_alias_per_module.vera",
    "tests/conformance/ch08_state_alias_per_module_lib.vera",
    "tests/conformance/ch08_xmod_widen_lib.vera",
    "tests/conformance/ch09_array_utilities.vera",
    "tests/conformance/ch09_async.vera",
    "tests/conformance/ch09_base64_bytes.vera",
    "tests/conformance/ch09_db.vera",
    "tests/conformance/ch09_decimal_generics.vera",
    "tests/conformance/ch09_eq_non_derivable_rejected.vera",
    "tests/conformance/ch09_generic_builtin_typevar.vera",
    "tests/conformance/ch09_generic_infer_builtin_return.vera",
    "tests/conformance/ch09_generic_none_nested.vera",
    "tests/conformance/ch09_generic_none_return.vera",
    "tests/conformance/ch09_generic_under_generic_prelude_callee.vera",
    "tests/conformance/ch09_host_store_gc_reachability.vera",
    "tests/conformance/ch09_http.vera",
    "tests/conformance/ch09_http_server.vera",
    "tests/conformance/ch09_inference.vera",
    "tests/conformance/ch09_json_accessors.vera",
    "tests/conformance/ch09_map_future_values.vera",
    "tests/conformance/ch09_markdown.vera",
    "tests/conformance/ch09_multiparam_ctor_eq.vera",
    "tests/conformance/ch09_nested_builtin_index.vera",
    "tests/conformance/ch09_nested_generic_call_eq.vera",
    "tests/conformance/ch09_nested_generic_ctor_eq.vera",
    "tests/conformance/ch09_option_result_combinators.vera",
    "tests/conformance/ch09_prelude.vera",
    "tests/conformance/ch09_recursive_show_hash.vera",
    "tests/conformance/ch09_regex.vera",
    "tests/conformance/ch09_show_hash_composites.vera",
    "tests/conformance/ch09_sql_injection_rejected.vera",
    "tests/conformance/ch09_sql_numbered_placeholder_rejected.vera",
    "tests/conformance/ch09_sql_placeholder_let_mismatch_rejected.vera",
    "tests/conformance/ch09_sql_placeholder_mismatch_rejected.vera",
    "tests/conformance/ch09_string_char_utilities.vera",
    "tests/conformance/ch09_structural_eq.vera",
    "tests/conformance/ch09_user_show_hash_field.vera",
    "tests/conformance/ch09_utf8_bytes.vera",
})

_HEAD = """\
private fn head(@Array<Int> -> @Int)
  requires(array_length(@Array<Int>.0) > 0)
  ensures(true)
  effects(pure)
{
  @Array<Int>.0[0]
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  head([])
}
"""

_REFINED = """\
public fn f(@Array<{ @Int | @Int.0 > 0 }>, @Array<{ @Int | @Int.0 < 0 }> -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  nat_to_int(array_length(@Array<{ @Int | @Int.0 > 0 }>.0)) + nat_to_int(array_length(@Array<{ @Int | @Int.0 < 0 }>.0))
}
"""


def _descriptions(kind: str) -> list[str]:
    verified = pipeline.verify(_HEAD, file="head.vera", past_check=True)
    return [o.expr_text for o in verified.obligations if o.kind.value == kind]


@_RED
def test_repro_obligation_descriptions_requires_and_call_pre() -> None:
    assert "array_length(@Array<Int>.0) > 0" in _descriptions("requires")
    assert "array_length(@Array<Int>.0) > 0" in _descriptions("call_pre")


@_RED
def test_repro_obligation_description_index_bounds() -> None:
    assert any("@Array<Int>.0[0]" in text
               for text in _descriptions("index_bounds")), _descriptions(
                   "index_bounds")


@_RED
def test_repro_runtime_contract_message() -> None:
    ran = pipeline.run(_HEAD, "main", file="head.vera")
    assert not ran.ok
    message = ran.trap.args[0] if ran.trap is not None else ran.stderr
    assert "head(@Array<Int> -> @Int)" in str(message), message
    assert "requires(array_length(@Array<Int>.0) > 0) failed" in str(message), message


@_RED
def test_repro_explain_slots_header(tmp_path: Path) -> None:
    path = tmp_path / "head.vera"
    path.write_text(_HEAD, encoding="utf-8")
    result = pipeline.cli("check", "--explain-slots", str(path))
    assert "fn head(@Array<Int> -> @Int)" in result.stdout, result.stdout


@_RED
def test_repro_explain_slots_header_keeps_refinements(tmp_path: Path) -> None:
    path = tmp_path / "f.vera"
    path.write_text(_REFINED, encoding="utf-8")
    result = pipeline.cli("check", "--explain-slots", str(path))
    assert ("fn f(@Array<{ @Int | @Int.0 > 0 }>, @Array<{ @Int | @Int.0 < 0 }> "
            "-> @Int)") in result.stdout, result.stdout


def _corpus() -> list[Path]:
    paths: list[Path] = []
    for root in ("examples", "tests/conformance"):
        paths.extend(sorted((_ROOT / root).rglob("*.vera")))
    return paths


def _round_trip_source(rendered_type: str) -> str:
    return (f"private fn rt({rendered_type} -> @Unit)\n  requires(true)\n"
            "  ensures(true)\n  effects(pure)\n{\n  ()\n}\n")


def _parsed_param(text: str) -> vast.TypeExpr:
    program = pipeline.parse(_round_trip_source(text)).program
    decl = program.declarations[0].decl
    assert isinstance(decl, vast.FnDecl)
    return decl.params[0]


def _parsed_expr(text: str) -> vast.Expr:
    program = pipeline.parse(
        "private fn rt(@Unit -> @Unit)\n  requires(true)\n  ensures(true)\n"
        f"  effects(pure)\n{{\n  {text}\n}}\n").program
    decl = program.declarations[0].decl
    assert isinstance(decl, vast.FnDecl)
    return decl.body.expr


def _nodes(node: object) -> list[vast.Node]:
    """Every node under *node*, types and nested declarations included."""
    found: list[vast.Node] = []
    stack: list[object] = [node]
    while stack:
        item = stack.pop()
        if isinstance(item, tuple):
            stack.extend(item)
        elif isinstance(item, vast.Node):
            found.append(item)
            stack.extend(getattr(item, f.name) for f in fields(item))
    return found


@pytest.mark.parametrize("path", [
    pytest.param(p, marks=_RED)
    if p.relative_to(_ROOT).as_posix() in _RED_AT_BASE else p
    for p in _corpus()
], ids=lambda p: p.relative_to(_ROOT).as_posix())
def test_every_type_and_slot_reference_renders_back(path: Path) -> None:
    """Every type expression and slot reference of *path*, rendered, parses
    back to the node it was rendered from.  Every corpus program parses,
    the conformance suite's negative fixtures included, so one that stops
    parsing fails here rather than leaving the sweep."""
    program = pipeline.parse(path).program
    seen = 0
    for node in _nodes(program):
        if isinstance(node, (vast.NamedType, vast.RefinementType, vast.FnType)):
            rendered = vast.format_type_expr(node)
            assert _parsed_param(rendered) == node, (rendered, node)
            seen += 1
        elif isinstance(node, vast.SlotRef):
            rendered = vast.format_expr(node)
            assert _parsed_expr(rendered) == node, (rendered, node)
            seen += 1
    assert seen, "the program holds no type expression or slot reference"


@_RED
def test_the_lsp_strip_is_gone() -> None:
    """`vera/lsp/workflows.py` compares the rendering as it stands."""
    text = (_ROOT / "vera" / "lsp" / "workflows.py").read_text(encoding="utf-8")
    assert '.replace("@", "")' not in text


@_RED
def test_obligation_json_descriptions_parse(tmp_path: Path) -> None:
    path = tmp_path / "head.vera"
    path.write_text(_HEAD, encoding="utf-8")
    result = pipeline.cli("verify", "--json", str(path))
    payload = json.loads(result.stdout)
    for obligation in payload["obligations"]:
        assert "<@" not in obligation["description"], obligation["description"]
