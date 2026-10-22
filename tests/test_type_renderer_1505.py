"""One type renderer: a type argument has no `@` (#1505; ROADMAP Stage 26).

`ast.format_type_expr` rendered a type as `@Name` and each of its arguments
by calling itself, so every argument took an `@` of its own: diagnostics,
obligation descriptions and runtime contract messages showed
`@Array<@Int>.0`, which does not parse.  It also elided a refinement's
predicate, so a signature whose parameters differ only in a refinement read
as one type, and it rendered a function type `@?`.  Four consumers worked
around it: three stripped every `@` from its output, and the verifier
rendered a refinement itself.  The renderer gives the head its `@` and an
argument none, and renders a type whole, so what a message shows parses back
to what the source wrote.

The ``repro`` cells are the issue's outputs and each consumer's.  The matrix
renders every shape a type takes at every position a consumer renders one
in; the round-trip cell renders every type expression, slot and result
reference, `old`/`new` argument and signature of the corpus, and parses each
back."""

from __future__ import annotations

import json
from collections.abc import Callable
from dataclasses import fields
from pathlib import Path

import pytest

from tests import pipeline
from vera import ast as vast
from vera.lsp.workflows import transitive_callers

pytestmark = pytest.mark.matrix(decides=[
    "vera/ast.py", "vera/formatter.py", "vera/lsp/workflows.py",
    "vera/checker/resolution.py", "vera/codegen/functions.py",
    "vera/verifier.py",
])

_ROOT = Path(__file__).resolve().parents[1]

#: Red at 94cef528, each as the issue describes: the named cells, the matrix
#: bar three cells, and the 125 corpus programs (of 323) whose round trip
#: fails.  Strict, so the renderer's commit, which deletes the marks, is
#: forced to flip every one.
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
    "examples/increment.vera",
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
    "tests/conformance/ch07_old_outside_ensures_rejected.vera",
    "tests/conformance/ch07_state_alias_chain.vera",
    "tests/conformance/ch07_state_alias_op_result_positions.vera",
    "tests/conformance/ch07_state_clause_alias_slots.vera",
    "tests/conformance/ch07_state_composite.vera",
    "tests/conformance/ch07_state_composite_alias.vera",
    "tests/conformance/ch07_state_composite_alias_cross_spelling.vera",
    "tests/conformance/ch07_state_fn_type_alias_cross_spelling.vera",
    "tests/conformance/ch07_state_nested_param_alias.vera",
    "tests/conformance/ch07_state_new_family.vera",
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
    return [o.expr_text for o in verified.obligations if o.kind == kind]


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


def _decl(signature: str, body: str = "()") -> vast.FnDecl:
    """The one function `private fn <signature> ... { <body> }` declares."""
    program = pipeline.parse(
        f"private fn {signature}\n  requires(true)\n  ensures(true)\n"
        f"  effects(pure)\n{{\n  {body}\n}}\n").program
    decl = program.declarations[0].decl
    assert isinstance(decl, vast.FnDecl)
    return decl


def _parsed_param(text: str) -> vast.TypeExpr:
    """*text*, a type in a slot's position, parsed as a parameter."""
    return _decl(f"rt({text} -> @Unit)").params[0]


def _parsed_expr(text: str) -> vast.Expr:
    """*text*, an expression, parsed as a function's body."""
    return _decl("rt(@Unit -> @Unit)", text).body.expr


def _parsed_signature(text: str) -> tuple[object, ...]:
    """*text*, ``name(@P, ... -> @R)``, parsed as a declaration's signature."""
    decl = _decl(text)
    return (decl.name, decl.params, decl.return_type)


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
    """Every type expression, slot and result reference, `old` and `new`
    argument and function signature of *path*, rendered, parses back to the
    node it was rendered from.  Every corpus program parses, the conformance
    suite's negative fixtures included, so one that stops parsing fails here
    rather than leaving the sweep."""
    program = pipeline.parse(path).program
    seen = 0
    for node in _nodes(program):
        if isinstance(node, (vast.NamedType, vast.RefinementType, vast.FnType)):
            rendered = vast.format_type_expr(node)
            assert _parsed_param(rendered) == node, (rendered, node)
        elif isinstance(node, (vast.SlotRef, vast.ResultRef, vast.OldExpr,
                               vast.NewExpr)):
            rendered = vast.format_expr(node)
            assert _parsed_expr(rendered) == node, (rendered, node)
        elif isinstance(node, vast.FnDecl):
            rendered = vast.format_fn_signature(node)
            assert _parsed_signature(rendered) == (
                node.name, node.params, node.return_type), rendered
        else:
            continue
        seen += 1
    assert seen, "the program holds no type expression or slot reference"


# =====================================================================
# The class: every shape of type at every position a consumer renders it
# =====================================================================

#: Each shape a type takes, in canonical form, as Vera writes it where it is
#: a type argument.  The predicates hold what a renderer that is not a left
#: inverse of parsing gets wrong: a parenthesised operand, an `if`, a
#: constructor call, a string literal holding a quote, a float.
_SHAPES: dict[str, str] = {
    "named": "Int",
    "argument": "Array<Int>",
    "nested_arguments": "Map<String, Option<Int>>",
    "refinement": "{ @Int | @Int.0 > 0 }",
    "refinement_parenthesised": "{ @Int | (@Int.0 + 1) * 2 > 0 }",
    "refinement_if": "{ @Int | if @Int.0 > 0 then { true } else { false } }",
    "refinement_constructor": "{ @Option<Int> | @Option<Int>.0 == Some(1) }",
    "refinement_string": '{ @String | @String.0 != "a \\"b\\"" }',
    "refinement_float": "{ @Float64 | @Float64.0 > 1.5 }",
    "refinement_in_argument": "Array<{ @Int | @Int.0 > 0 }>",
    "fn_pure": "fn(Int -> Int) effects(pure)",
    "fn_row": "fn(Int, Array<Int> -> Option<Int>) effects(<State<Int>, IO>)",
    "fn_no_params": "fn(-> Int) effects(<Exn<String>>)",
    "fn_in_argument": "Option<fn(Int -> Int) effects(pure)>",
    "fn_refined_param": "fn({ @Int | @Int.0 > 0 } -> Int) effects(pure)",
}

#: What one position yields for a shape *t*: the consumer's rendering, what
#: Vera writes there, the parse that reads the rendering back, and the node
#: it rendered.
_Rendered = tuple[str, str, Callable[[str], object], object]


def _slot_head(t: str) -> _Rendered:
    node = _decl(f"p(@{t} -> @Unit)").params[0]
    return vast.format_type_expr(node), f"@{t}", _parsed_param, node


def _type_argument(t: str) -> _Rendered:
    node = _decl(f"p(@Array<{t}> -> @Unit)").params[0]
    return vast.format_type_expr(node), f"@Array<{t}>", _parsed_param, node


def _slot_reference(t: str) -> _Rendered:
    node = _decl(f"p(@Array<{t}> -> @Unit)", f"@Array<{t}>.0").body.expr
    return vast.format_expr(node), f"@Array<{t}>.0", _parsed_expr, node


def _result_reference(t: str) -> _Rendered:
    node = _decl(f"p(@Unit -> @Array<{t}>)", f"@Array<{t}>.result").body.expr
    return vast.format_expr(node), f"@Array<{t}>.result", _parsed_expr, node


def _old(t: str) -> _Rendered:
    node = _decl("p(@Unit -> @Unit)", f"old(State<{t}>)").body.expr
    return vast.format_expr(node), f"old(State<{t}>)", _parsed_expr, node


def _new(t: str) -> _Rendered:
    node = _decl("p(@Unit -> @Unit)", f"new(State<{t}>)").body.expr
    return vast.format_expr(node), f"new(State<{t}>)", _parsed_expr, node


def _binding_of(rendered: str) -> vast.TypeExpr:
    """A quantifier's rendering, ``forall(<binding>, 3, ...)``: `format_expr`
    writes the predicate ``...``, so its binding is what parses back."""
    return _parsed_param(
        rendered.removeprefix("forall(").removesuffix(", 3, ...)"))


def _quantifier_binding(t: str) -> _Rendered:
    node = _decl("p(@Unit -> @Bool)",
                 f"forall(@{t}, 3, fn(@Nat -> @Bool) effects(pure) {{ true }})"
                 ).body.expr
    assert isinstance(node, vast.ForallExpr)
    return (vast.format_expr(node), f"forall(@{t}, 3, ...)", _binding_of,
            node.binding_type)


def _signature(t: str) -> _Rendered:
    decl = _decl(f"p(@{t} -> @{t})")
    return (vast.format_fn_signature(decl), f"p(@{t} -> @{t})",
            _parsed_signature, (decl.name, decl.params, decl.return_type))


_POSITIONS: dict[str, Callable[[str], _Rendered]] = {
    "slot_head": _slot_head,
    "type_argument": _type_argument,
    "slot_reference": _slot_reference,
    "result_reference": _result_reference,
    "old": _old,
    "new": _new,
    "quantifier_binding": _quantifier_binding,
    "signature": _signature,
}

#: The cells green at 94cef528: a type with no argument, refinement or
#: function type, where nothing puts it in an argument.  Every other cell
#: was red there, each as the issue describes.
_MATRIX_GREEN_AT_BASE = frozenset({
    ("named", "slot_head"), ("named", "quantifier_binding"),
    ("named", "signature"),
})


@pytest.mark.parametrize(("shape", "position"), [
    pytest.param(shape, position, id=f"{shape}-{position}",
                 marks=() if (shape, position) in _MATRIX_GREEN_AT_BASE
                 else _RED)
    for shape in _SHAPES for position in _POSITIONS
])
def test_every_shape_renders_as_vera_at_every_position(
    shape: str, position: str,
) -> None:
    """The consumer writes the shape as the source does, and what it writes
    parses back to the node it rendered."""
    rendered, expected, parse, node = _POSITIONS[position](_SHAPES[shape])
    assert rendered == expected
    assert parse(rendered) == node


# =====================================================================
# The consumers that worked around the renderer
# =====================================================================

@_RED
def test_no_consumer_strips_the_renderers_at() -> None:
    """No module re-derives the bare form by deleting every `@` from the
    slot form: a refinement's own `@`s are part of the type
    (`{ @Int | @Int.0 > 0 }`).  At 94cef528 three did: `vera/lsp/workflows.py`
    (the `vera/addEffect` handler key), `vera/checker/resolution.py` (E340's
    operation signature) and `vera/codegen/functions.py` (the `Exn` boundary
    message)."""
    stripping = [
        path.relative_to(_ROOT).as_posix()
        for path in sorted((_ROOT / "vera").rglob("*.py"))
        if '.replace("@", "")' in path.read_text(encoding="utf-8")
    ]
    assert stripping == []


_FN_ARGUMENT_HANDLER = """\
private fn target(@Nat -> @Nat)
  requires(true)
  ensures(true)
  effects(<Exn<Option<fn(Int -> Int) effects(pure)>>>)
{
  @Nat.0
}

private fn handled(@Nat -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[Exn<Option<fn(Int -> Int) effects(pure)>>] {
    throw(@Option<fn(Int -> Int) effects(pure)>) -> { 0 }
  } in {
    target(@Nat.0)
  }
}
"""


@_RED
def test_repro_add_effect_bounds_a_function_type_argument() -> None:
    """`vera/addEffect` keys a handler's head by the renderer's bare form.
    The program checks, so `handle[Exn<Option<fn(Int -> Int) effects(pure)>>]`
    discharges that instance around `handled`'s call, and a request spelled
    the same is bounded there.  The `@`-stripped rendering wrote the function
    type `?`, a key no request equals, so the caller kept an edge it does not
    need."""
    checked = pipeline.check(_FN_ARGUMENT_HANDLER)
    assert checked.ok, checked.diagnostics
    assert transitive_callers(
        checked.program, "target",
        "Exn<Option<fn(Int -> Int) effects(pure)>>") == ["target"]


_FORWARD_EFFECT = """\
private fn f(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(<Ping>)
{
  @Int.0
}

effect Ping {
  op ping({ @Int | @Int.0 > 0 }, Array<Int> -> Option<Int>);
}
"""


@_RED
def test_repro_forward_effect_operation_signature() -> None:
    """E340's fix writes an operation declared further down the file as the
    declaration does, its refined parameter whole: the `@`-stripped
    rendering read it `Int`, the refinement's base."""
    [error] = pipeline.check(_FORWARD_EFFECT).errors
    assert error.error_code == "E340"
    assert ("with the operation's signature ({ @Int | @Int.0 > 0 }, "
            "Array<Int> -> Option<Int>)") in error.fix, error.fix


_EXN_BOUNDARY = """\
public fn boom(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(<Exn<Array<{ @Int | @Int.0 >= 0 }>>>)
{
  throw([1])
}
"""


@_RED
def test_repro_exn_boundary_names_the_rows_type() -> None:
    """The message for an exception escaping an entry point names the type as
    the row spells it, so the `handle[Exn<T>]` it asks for catches the
    exception: the `@`-stripped rendering named `Exn<Array<Int>>`, an
    instance no handler of the thrown one is."""
    ran = pipeline.run(_EXN_BOUNDARY, "boom")
    assert ran.trap is not None
    message = str(ran.trap.args[0])
    assert ("An `Exn<Array<{ @Int | @Int.0 >= 0 }>>` escaped `boom`: no "
            "`handle[Exn<Array<{ @Int | @Int.0 >= 0 }>>]` caught it"
            ) in message, message


_PREDICATE_DECLARATION = """\
private fn f(@Array<{ @Array<Nat> | 10 / array_length(@Array<Nat>.0) > 0 }> -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  7
}
"""


@_RED
def test_repro_refinement_predicate_names_its_type() -> None:
    """The verifier's text for an operation in a refinement's predicate names
    the refinement as written.  It rendered the refinement itself, its base
    through `format_type_expr`, so the base's argument took an `@`."""
    verified = pipeline.verify(_PREDICATE_DECLARATION)
    [error] = [d for d in verified.errors if d.error_code == "E526"]
    assert ("In the refinement predicate of `{ @Array<Nat> | "
            "10 / array_length(@Array<Nat>.0) > 0 }`") in error.description, (
                error.description)


@_RED
def test_obligation_json_descriptions_parse(tmp_path: Path) -> None:
    path = tmp_path / "head.vera"
    path.write_text(_HEAD, encoding="utf-8")
    result = pipeline.cli("verify", "--json", str(path))
    payload = json.loads(result.stdout)
    for obligation in payload["obligations"]:
        assert "<@" not in obligation["description"], obligation["description"]
