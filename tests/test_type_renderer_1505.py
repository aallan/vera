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
    "vera/checker/calls.py", "vera/checker/resolution.py",
    "vera/codegen/functions.py", "vera/verifier.py",
])

_ROOT = Path(__file__).resolve().parents[1]

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
    verified = pipeline.verify(_HEAD, file="head.vera")
    return [o.expr_text for o in verified.obligations if o.kind == kind]


def test_repro_obligation_descriptions_requires_and_call_pre() -> None:
    assert "array_length(@Array<Int>.0) > 0" in _descriptions("requires")
    assert "array_length(@Array<Int>.0) > 0" in _descriptions("call_pre")


def test_repro_obligation_description_index_bounds() -> None:
    assert any("@Array<Int>.0[0]" in text
               for text in _descriptions("index_bounds")), _descriptions(
                   "index_bounds")


def test_repro_runtime_contract_message() -> None:
    ran = pipeline.run(_HEAD, "main", file="head.vera")
    assert not ran.ok
    message = ran.trap.args[0] if ran.trap is not None else ran.stderr
    assert "head(@Array<Int> -> @Int)" in str(message), message
    assert "requires(array_length(@Array<Int>.0) > 0) failed" in str(message), message


def test_repro_explain_slots_header(tmp_path: Path) -> None:
    path = tmp_path / "head.vera"
    path.write_text(_HEAD, encoding="utf-8")
    result = pipeline.cli("check", "--explain-slots", str(path))
    assert "fn head(@Array<Int> -> @Int)" in result.stdout, result.stdout


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


@pytest.mark.parametrize("path", _corpus(),
                         ids=lambda p: p.relative_to(_ROOT).as_posix())
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

@pytest.mark.parametrize(("shape", "position"), [
    pytest.param(shape, position, id=f"{shape}-{position}")
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


_STRING_REFINED_HANDLER = """\
private fn target(@Nat -> @Nat)
  requires(true)
  ensures(true)
  effects(<Exn<Array<{ @String | @String.0 == "a b" }>>>)
{
  @Nat.0
}

private fn handled(@Nat -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[Exn<Array<{ @String | @String.0 == "a b" }>>] {
    throw(@Array<{ @String | @String.0 == "a b" }>) -> { 0 }
  } in {
    target(@Nat.0)
  }
}
"""


def test_a_refinement_argument_keys_no_handler() -> None:
    """A handler whose argument holds a refinement bounds no request, a
    request spelled the same included.  The key drops whitespace, and a
    predicate's spaces can be its meaning: keyed by its rendering, the
    handler over `"a b"` would bound a request over `"ab"`, an instance
    the checker keeps apart, and the caller would lose a row it needs."""
    program = pipeline.parse(_STRING_REFINED_HANDLER).program
    for request in ('Exn<Array<{ @String | @String.0 == "ab" }>>',
                    'Exn<Array<{ @String | @String.0 == "a b" }>>'):
        assert transitive_callers(program, "target", request) == [
            "target", "handled"], request


def test_a_handler_key_joins_its_arguments() -> None:
    """Each argument of a handler's head in the key, in order, comma-joined
    as a request string is: `Pair<Int, Option<String>>` keys
    `Pair<Int,Option<String>>`."""
    from vera.lsp.workflows import _handled_effect_key
    ref = vast.EffectRef(name="Pair", type_args=(
        vast.NamedType(name="Int", type_args=None),
        vast.NamedType(name="Option", type_args=(
            vast.NamedType(name="String", type_args=None),)),
    ))
    assert _handled_effect_key(ref) == "Pair<Int,Option<String>>"


_PING_EFFECT = """\
effect Ping {
  op ping({ @Int | @Int.0 > 0 }, Array<Int> -> Option<Int>);
}
"""

_PING_ROW = """\
private fn f(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(<Ping>)
{
  @Int.0
}
"""

#: The effect declared below the row that names it, and above it.
_FORWARD_EFFECT = _PING_ROW + "\n" + _PING_EFFECT
_REGISTERED_EFFECT = _PING_EFFECT + "\n" + _PING_ROW

#: `Ping.ping`'s signature as its declaration writes it.
_PING_SIGNATURE = "({ @Int | @Int.0 > 0 }, Array<Int> -> Option<Int>)"


def _top_level_split(text: str, sep: str) -> list[str]:
    """*text* split at each *sep* outside every bracket.  A refinement's
    predicate is opaque (its `<`, `>` and `,` are an expression's, and a
    string literal in it is one token), and `->` is an arrow, not a
    bracket."""
    parts: list[str] = []
    angle = brace = paren = 0
    start = i = 0
    while i < len(text):
        if not (angle or brace or paren) and text.startswith(sep, i):
            parts.append(text[start:i])
            i += len(sep)
            start = i
            continue
        if text.startswith("->", i):
            i += 2
            continue
        ch = text[i]
        if brace:
            if ch == '"':
                i += 1
                while i < len(text) and text[i] != '"':
                    i += 2 if text[i] == "\\" else 1
            brace += {"{": 1, "}": -1}.get(ch, 0)
        else:
            brace += ch == "{"
            paren += {"(": 1, ")": -1}.get(ch, 0)
            angle += {"<": 1, ">": -1}.get(ch, 0)
        i += 1
    parts.append(text[start:])
    return parts


def _check_operation_signature_fix(source: str) -> None:
    """E340's fix for *source*'s row names `Ping.ping`'s signature as its
    declaration writes it, and the function the fix asks for, written with
    that signature (each parameter and the result in a slot's position),
    passes `vera check`."""
    [error] = pipeline.check(source).errors
    assert error.error_code == "E340"
    assert f"with the operation's signature {_PING_SIGNATURE}" in error.fix, (
        error.fix)
    signature = error.fix.split("with the operation's signature (", 1)[1]
    signature = signature.split("), called ", 1)[0]
    params, result = _top_level_split(signature, " -> ")
    pasted = (
        "private fn ping_of("
        + ", ".join(f"@{p}" for p in _top_level_split(params, ", "))
        + f" -> @{result})\n  requires(true)\n  ensures(true)\n"
        "  effects(pure)\n{\n  None\n}\n")
    checked = pipeline.check(pasted)
    assert checked.ok, (pasted, checked.diagnostics)


def test_repro_forward_effect_operation_signature() -> None:
    """E340's fix writes an operation declared further down the file as the
    declaration does, its refined parameter whole: the `@`-stripped
    rendering read it `Int`, the refinement's base."""
    _check_operation_signature_fix(_FORWARD_EFFECT)


def test_repro_registered_effect_operation_signature() -> None:
    """Declared above the row, the same operation reads the same: the fix
    rendered a registered effect's operation through `pretty_type`, which
    writes the refinement `{@Int | ...}`, a signature that does not parse
    (E005) when the function is written with it."""
    _check_operation_signature_fix(_REGISTERED_EFFECT)


_PING_CALL = """\
public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(<IO>)
{
  match Ping.ping(1, [2]) {
    Some(@Int) -> @Int.0,
    None -> 0
  }
}
"""


def test_repro_operation_call_signature() -> None:
    """E340's fix for an operation called under a row without its effect
    (rule 6) writes the signature from the declaration, declared above the
    call or below it: it rendered the registered operation through
    `pretty_type`, `({@Int | ...}, Array<Int> -> Option<Int>)`."""
    for source in (_PING_EFFECT + "\n" + _PING_CALL,
                   _PING_CALL + "\n" + _PING_EFFECT):
        _check_operation_signature_fix(source)


_WEIGH_ABILITY = """\
ability Weigh<T> {
  op weigh({ @Int | @Int.0 > 0 }, T -> Int);
}
"""

_WEIGH_CONSTRAINT = """\
private forall<T where Weigh<T>> fn f(@T -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  7
}
"""

_WEIGH_CALL = """\
private fn f(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  weigh(1, @Int.0)
}
"""

#: The function type E340's fix for a user-declared ability declares, its
#: operation's signature as the ability writes it.
_WEIGH_OP = "type WeighOp<T> = fn({ @Int | @Int.0 > 0 }, T -> Int) effects(pure);"


def _check_function_value_fix(use: str) -> None:
    """E340's fix for *use* of `Weigh`, declared above it or below it,
    declares `_WEIGH_OP`, and that declaration, pasted as written, passes
    `vera check`."""
    for source in (_WEIGH_ABILITY + "\n" + use, use + "\n" + _WEIGH_ABILITY):
        [error] = pipeline.check(source).errors
        assert error.error_code == "E340"
        assert _WEIGH_OP in error.fix, error.fix
        pasted = "type " + error.fix.split("type ", 1)[1].split("; then", 1)[0]
        checked = pipeline.check(pasted + ";\n")
        assert checked.ok, (pasted, checked.diagnostics)


def test_repro_ability_constraint_signature() -> None:
    """A `where` constraint naming a user-declared ability: the fix's
    function type wrote the operation through `pretty_type`,
    `fn({@Int | ...}, T -> Int)`."""
    _check_function_value_fix(_WEIGH_CONSTRAINT)


def test_repro_ability_call_signature() -> None:
    """A call to a user-declared ability's operation, the same."""
    _check_function_value_fix(_WEIGH_CALL)


_EXN_BOUNDARY = """\
public fn boom(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(<Exn<Array<{ @Int | @Int.0 >= 0 }>>>)
{
  throw([1])
}
"""


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
private fn f(@Array<{ @Array<Nat> | 10 / (array_length(@Array<Nat>.0) * 2) > 0 }> -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  7
}
"""


def test_repro_refinement_predicate_names_its_type() -> None:
    """The verifier's text for an operation in a refinement's predicate names
    the refinement as written.  It rendered the refinement itself: its base
    through `format_type_expr`, so the base's argument took an `@`, and its
    predicate through `format_expr`, which drops the parentheses."""
    verified = pipeline.verify(_PREDICATE_DECLARATION)
    [error] = [d for d in verified.errors if d.error_code == "E526"]
    assert ("In the refinement predicate of `{ @Array<Nat> | "
            "10 / (array_length(@Array<Nat>.0) * 2) > 0 }`") in error.description, (
                error.description)


def test_obligation_json_descriptions_parse(tmp_path: Path) -> None:
    path = tmp_path / "head.vera"
    path.write_text(_HEAD, encoding="utf-8")
    result = pipeline.cli("verify", "--json", str(path))
    payload = json.loads(result.stdout)
    for obligation in payload["obligations"]:
        assert "<@" not in obligation["description"], obligation["description"]
