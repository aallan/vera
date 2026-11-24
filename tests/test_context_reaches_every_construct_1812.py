"""The type a context names reaches every construct it types (#1812).

A construct whose value leaves a type variable open (`None`, `[]`,
`Ok(1)`, a generic call no argument of which fixes its variable, an index
over an empty literal) took the type its position names only where a
per-site gate listed the kind of value it repaired.  An `Exn` handler's
body and clauses, an array literal's element, a generic call's argument, an
ability operation's argument, a field of a data type with no type
parameters, a tuple's component, a binding that held a literal beside a
nested call's open variable (rule C), and a `match` scrutinee whose binder
pattern names its type each missed some value: the program was refused
(E121, E170, E164, E213, E241, E613), code generation dropped the function
the value stood in (E602, then E907 at `vera run`), or the check accepted
it with the variable open in the types and instances it recorded.

The rule (spec §5.9, rule E): a sub-expression whose position's type the
context closes is checked against that type.  Where the type is known
before the sub-expression is synthesized it is handed down; where it is
known only after a call's inference, the argument is synthesized again
against the instantiated parameter, and an index the first synthesis could
not type is held, not refused, until then.

The class: every construct x every kind of open value x every source of the
type.  The instrument:

* the matrix, construct (17) x open value (9) x where the type comes from
  (a `let`, a return, a parameter, a generic call's other argument, a
  constructor field, a `match` binder pattern) x whether the type holds the
  enclosing `forall<T>` function's own `T`: each cell checks, no type
  or instance it records holds an unknown or a variable left open, and it
  compiles with no function dropped (a generic cell's `main` builds the
  clone); `empty_of(())[0]` records `empty_of` at the type the index is
  expected at.  The cells of `eq` over two `Result`s
  that each leave the other's variable open are refused by the ability
  operation's judge, #1921's mechanism: they are pinned as they are;
* the census: over the corpus and the documents' blocks, no expression of a
  program that checks holds an open type or instance, except where no
  context names the variable (the programs named in `CENSUS_EXEMPT`, each
  with the open parts it holds), a built-in's variable included.
"""

from __future__ import annotations

import importlib.util
import re
from dataclasses import fields
from pathlib import Path
from typing import Any

import pytest

from tests import pipeline
from vera import ast
from vera.types import (
    BUILTIN_TYPEVAR_MARKER,
    AdtType,
    FunctionType,
    TypeVar,
    Type,
    base_type,
    contains_fresh_typevar,
    contains_unknown,
    pretty_type,
)

pytestmark = pytest.mark.matrix(decides=[
    "vera/checker/calls.py",
    "vera/checker/control.py",
    "vera/checker/expressions.py",
    "vera/checker/resolution.py",
])

ROOT = Path(__file__).resolve().parents[1]

_SIG = "  requires(true)\n  ensures(true)\n  effects(pure)\n"

_HELPERS = f"""private forall<T> fn idg(@T -> @T)
{_SIG}{{
  @T.0
}}

private forall<T> fn pick(@T, @T -> @T)
{_SIG}{{
  @T.1
}}

private forall<T> fn none_of(@Unit -> @Option<T>)
{_SIG}{{
  None
}}

private forall<T> fn empty_of(@Unit -> @Array<T>)
{_SIG}{{
  []
}}

private forall<T where Ord<T>> fn none_ord(@Unit -> @Option<T>)
{_SIG}{{
  None
}}

private data G<A> {{ MkG(A) }}
"""


def _holds_builtin_variable(ty: Type) -> bool:
    """Whether a built-in's type variable a call left open (`K#b#f1`, a
    `map_new()` no context names) stands anywhere in *ty*."""
    ty = base_type(ty)
    if isinstance(ty, TypeVar):
        return BUILTIN_TYPEVAR_MARKER in ty.name
    if isinstance(ty, AdtType):
        return any(_holds_builtin_variable(a) for a in ty.type_args)
    if isinstance(ty, FunctionType):
        return any(_holds_builtin_variable(a)
                   for a in (*ty.params, ty.return_type))
    return False


def _is_open(ty: Type) -> bool:
    """An unknown, a minted variable or a built-in's open variable; the
    enclosing function's own `T` is a type."""
    return (contains_unknown(ty) or contains_fresh_typevar(ty)
            or _holds_builtin_variable(ty))


def _nodes(value: object) -> list[ast.Node]:
    """Every node under *value*, declarations' bodies included."""
    out: list[ast.Node] = []
    stack = [value]
    while stack:
        item = stack.pop()
        if isinstance(item, ast.Node):
            out.append(item)
            stack.extend(getattr(item, f.name) for f in fields(item))
        elif isinstance(item, tuple):
            stack.extend(item)
    return out


def _open_parts(checked: pipeline.Checked) -> list[str]:
    """Each recorded type holding an unknown or a variable left open,
    with the line it is recorded at, and each instantiation that leaves a
    callee's variable unbound or open."""
    art = checked.artifacts
    lines = {n.node_id: n.span.line for n in _nodes(checked.program)
             if n.node_id is not None and n.span is not None}
    found = {f"{lines.get(node, '?')}: {pretty_type(t)}"
             for node, t in art.node_semantic_types.items()
             if t is not None and _is_open(t)}
    for node, rec in art.instantiations.items():
        at = lines.get(node, "?")
        for tv in rec.forall_vars:
            bound = rec.mapping.get(tv)
            if bound is None:
                found.add(f"{at}: {rec.callee}: {tv} unbound")
            elif _is_open(bound):
                found.add(f"{at}: {rec.callee}: {tv} = {pretty_type(bound)}")
    return sorted(found)


def _codes(source: str) -> list[str]:
    return [e.error_code for e in pipeline.check(source).errors]


def _clean(source: str) -> None:
    """*source* checks, records nothing open, and compiles with no function
    dropped."""
    checked = pipeline.check(source)
    assert checked.ok, [d.format() for d in checked.errors]
    assert _open_parts(checked) == [], source
    compiled = pipeline.compile(source)
    assert compiled.ok, [d.format() for d in compiled.errors]
    dropped = [d for d in compiled.diagnostics
               if d.error_code in ("E602", "E620")]
    assert dropped == [], [d.format() for d in dropped]


def _main(body: str, ret: str = "@Int", params: str = "@Int",
          decls: str = "") -> str:
    return (_HELPERS + decls
            + f"\npublic fn main({params} -> {ret})\n{_SIG}{{\n  {body}\n}}\n")


# ---------------------------------------------------------------------
# The issue's lines, red first
# ---------------------------------------------------------------------

_HEAD_ORD = """private forall<T where Ord<T>> fn head_ord(@Array<T> -> @T)
  requires(array_length(@Array<T>.0) > 0)
  ensures(true)
  effects(pure)
{
  @Array<T>.0[0]
}
"""


def test_repro_handler_body_and_clause_take_the_return_type() -> None:
    """The issue's program: a handler whose body and clause each give one
    side of a `Result` is the function's `Result<Int, String>` (was E121)."""
    _clean(_main(
        "handle[Exn<Int>] {\n    throw(@Int) -> { Ok(0) }\n  } in {\n"
        "    if @Int.0 > 0 then { throw(@Int.0) } else { Ok(1) }\n  }",
        ret="@Result<Int, String>"))


def test_repro_handler_at_a_let() -> None:
    _clean(_main(
        "let @Result<Int, String> = handle[Exn<Int>] {\n"
        "    throw(@Int) -> { Ok(0) }\n  } in {\n    Ok(1)\n  };\n  0"))


def test_repro_handler_of_none() -> None:
    _clean(_main(
        "handle[Exn<Int>] {\n    throw(@Int) -> { None }\n  } in {\n"
        "    None\n  }", ret="@Option<Int>"))


def test_repro_array_of_none_records_the_element_type() -> None:
    """`[None]` at `Array<Option<Nat>>` checked since #1887; its element
    kept `Option<T$n>` in the types the check recorded."""
    _clean(_main("let @Array<Option<Nat>> = [None];\n"
                 "  option_unwrap_or(@Array<Option<Nat>>.0[0], 7)"))


@pytest.mark.parametrize("value", [
    "array_reverse([])",
    "array_reverse(array_reverse([]))",
    "array_filter([], fn(@Int -> @Bool) effects(pure) { true })",
])
def test_repro_empty_literal_argument_of_a_builtin(value: str) -> None:
    """The empty literal took no element type from the call's instance, and
    code generation dropped the function (E602 at verify, E907 at run)."""
    _clean(_main(f"let @Array<Int> = {value};\n  array_length(@Array<Int>.0)"))


def test_repro_index_over_empty_literal_in_a_generic_argument() -> None:
    _clean(_main("let @Int = idg([][0]);\n  @Int.0"))
    _clean(_main("pick([][0], 5)"))
    _clean(_main("let @Int = idg(idg([][0]));\n  @Int.0"))


def test_repro_index_over_empty_literal_in_a_non_generic_field() -> None:
    _clean(_main("let @Box = Box([][0]);\n  0",
                 decls="\nprivate data Box { Box(Int) }\n"))


def test_repro_ability_operation_argument() -> None:
    """`compare(head_ord([]), 5)` was E241 at `?`; `head_ord([])` keeps its
    precondition, so the program checks and is not compiled here."""
    for body in ("let @Ordering = compare(head_ord([]), 5);\n  0",
                 "let @Ordering = compare(5, head_ord([]));\n  0",
                 "let @Bool = eq(head_ord([]), 5);\n  0"):
        checked = pipeline.check(_HEAD_ORD + _main(body))
        assert checked.ok, [d.format() for d in checked.errors]
        assert _open_parts(checked) == [], body
    _clean(_main("let @Bool = eq(if true then { None } else { None }, Some(1));\n  0"))
    _clean(_main("let @Bool = eq({ None }, Some(1));\n  0"))


def test_repro_rule_c_beside_a_literal() -> None:
    """Rule C was skipped for a binding that held a literal hole, so
    `head_ord`'s variable fell to the default (E613)."""
    for body in ("let @Tuple<Int, Int> = idg(Tuple(head_ord([]), 1));\n  0",
                 "let @Tuple<Int, Int> = idg(Tuple(1, head_ord([])));\n  0"):
        checked = pipeline.check(_HEAD_ORD + _main(body))
        assert checked.ok, [d.format() for d in checked.errors]
        assert _open_parts(checked) == [], body
    _clean(_main("let @Result<Int, String> = idg(Ok(1));\n  0"))


def test_repro_binder_pattern_names_the_scrutinee() -> None:
    """Found by the matrix: a scrutinee call whose binder pattern names its
    type was judged at the default (E613)."""
    _clean(_main("match none_ord(()) {\n    @Option<Int> -> 0\n  }"))
    _clean(_main("match [][0] {\n    @Int -> 0\n  }"))


def test_repro_a_generic_constructors_field_is_settled() -> None:
    """A field no expected type hands down, of a constructor of a data type
    with type parameters: written (`MkW`'s `Int`) or fixed by a sibling
    (`MkP`'s `T` by the `1`), E164 before."""
    decls = ("\nprivate data W<T> { MkW(Int, T) }\n"
             "\nprivate data P<T> { MkP(T, T) }\n")
    _clean(_main('array_length([MkW([][0], "s")])', decls=decls))
    _clean(_main("array_length([MkP([][0], 1)])", decls=decls))
    _clean(_main("array_length([MkP(1, [][0])])", decls=decls))


def test_repro_apply_fn_argument_at_the_enclosing_variable() -> None:
    """A closure's formal the enclosing function's `T` closes is its
    argument's type (E164 before)."""
    source = (_HELPERS + "\ntype Endo<T> = fn(T -> T) effects(pure);\n"
              f"\nprivate forall<T> fn g(@Endo<T> -> @T)\n{_SIG}{{\n"
              "  apply_fn(@Endo<T>.0, [][0])\n}\n")
    checked = pipeline.check(source)
    assert checked.ok, [d.format() for d in checked.errors]
    assert _open_parts(checked) == []


def test_repro_a_settled_hole_is_reported_once() -> None:
    """A typed hole the context settles is reported once, at the type the
    context names: the first synthesis's `expected unknown` is withdrawn,
    with its hole record."""
    for body, ret in (("[?]", "@Array<Int>"), ("idg(?)", "@Int"),
                      ("Tuple(?, 1)", "@Tuple<Int, Int>")):
        checked = pipeline.check(_main(body, ret=ret))
        holes = [d.description for d in checked.warnings
                 if d.error_code == "W001"]
        assert holes == ["Typed hole: expected Int."], body
        assert [h.expected for h in checked.artifacts.holes] == ["Int"], body


def test_repro_a_construction_in_a_handler_is_checked_where_it_is_built(
        ) -> None:
    """A handler's construction takes the type the handler is expected at,
    so a refined field it violates is refuted where it is built (E505), in
    the handled body and in an `Exn` clause, where `main` refuted it at the
    return, or disclosed it as a run-time check (E506)."""
    for handler in (
            "handle[State<Int>](@Int = 1) {\n"
            "    get(@Unit) -> { resume(@Int.0) },\n"
            "    put(@Int) -> { resume(()) }\n  } in {\n    Some(0 - 5)\n  }",
            "handle[Exn<Int>] {\n    throw(@Int) -> { Some(0 - 5) }\n"
            "  } in {\n    throw(1)\n  }"):
        source = ("type PosInt = { @Int | @Int.0 > 0 };\n"
                  f"\npublic fn f(@Int -> @Option<PosInt>)\n{_SIG}{{\n"
                  f"  {handler}\n}}\n")
        verified = pipeline.verify(source)
        assert [(d.error_code, d.description.split(" in 'f'")[0])
                for d in verified.errors] == [
            ("E505", "Value narrowing into a refined constructor field")]


def test_repro_a_binder_pattern_holds_the_scrutinee_to_its_type() -> None:
    """The one program shape the rule refuses that checked before: the
    binding pattern names the scrutinee's type, so a constructor pattern
    beside it binding another payload type is E314, in either arm order."""
    for arms in ("Some(@Int) -> 0, @Option<String> -> 1",
                 "@Option<String> -> 1, Some(@Int) -> 0"):
        assert _codes(_main(f"match none_of(()) {{ {arms} }}")) == ["E314"]
    _clean(_main("match none_of(()) { Some(@Int) -> 0, @Option<Int> -> 1 }"))


# #1921's mechanism, not this one: the ability operation holds an argument
# to bare `is_subtype`, so two values that each leave the other's variable
# open are refused where `pick` accepts them.  Pinned as they are.
@pytest.mark.parametrize("body", [
    'let @Bool = eq(Ok(1), Err("e"));\n  0',
    'let @Bool = eq(Err("e"), Ok(1));\n  0',
    "let @Bool = eq(None, None);\n  0",
])
def test_repro_ability_judge_is_1921s(body: str) -> None:
    assert _codes(_main(body)) == ["E241"]
    pick = body.replace("eq(", "pick(").replace("@Bool", "@Result<Int, String>"
                                                 if "Ok" in body else "@Option<Int>")
    assert _codes(_main(pick)) == []


#: The same values with no context: their verdicts stand.
CONTROLS = {
    "None": [], "[]": [], "Ok(1)": [], "none_of(())": [], "empty_of(())": [],
    "idg(None)": [], "[][0]": ["E164"], "none_ord(())": ["E613"],
}


@pytest.mark.parametrize("value", sorted(CONTROLS))
def test_repro_no_context_keeps_its_verdict(value: str) -> None:
    assert _codes(_main(f"{value};\n  0")) == CONTROLS[value]


# ---------------------------------------------------------------------
# The matrix
# ---------------------------------------------------------------------

#: value: (text, the type X its context names, a closed value of X, X has
#: Eq), in a function of no type parameters and in a `forall<T>` one, where
#: the type the context names holds the function's own `T`.
VALUES = {
    "none": ("None", "Option<Int>", "Some(1)", True),
    "empty": ("[]", "Array<Int>", "[1]", False),
    "ok": ("Ok(1)", "Result<Int, String>", 'Err("e")', True),
    "call_open": ("none_of(())", "Option<Int>", "Some(1)", True),
    "empty_call": ("empty_of(())", "Array<Int>", "[1]", False),
    "index": ("[][0]", "Int", "5", True),
    "index_call": ("empty_of(())[0]", "Int", "5", True),
    "nested": ("idg(None)", "Option<Int>", "Some(1)", True),
    "ord_call": ("none_ord(())", "Option<Int>", "Some(1)", True),
}
GENERIC_VALUES = {
    "none": ("None", "Option<T>", "Some(@T.0)", True),
    "empty": ("[]", "Array<T>", "[@T.0]", False),
    "ok": ("Ok(@T.0)", "Result<T, String>", 'Err("e")', True),
    "call_open": ("none_of(())", "Option<T>", "Some(@T.0)", True),
    "empty_call": ("empty_of(())", "Array<T>", "[@T.0]", False),
    "index": ("[][0]", "T", "@T.0", True),
    "index_call": ("empty_of(())[0]", "T", "@T.0", True),
    "nested": ("idg(None)", "Option<T>", "Some(@T.0)", True),
    "ord_call": ("none_ord(())", "Option<T>", "Some(@T.0)", True),
}

#: construct: (template over {v} and {w}, its type over {X})
CONSTRUCTS = {
    "bare": ("{v}", "{X}"),
    "handler": ("handle[Exn<Int>] {{\n    throw(@Int) -> {{ {v} }}\n  }} in {{\n    {v}\n  }}", "{X}"),
    "handler_throw": ("handle[Exn<Int>] {{\n    throw(@Int) -> {{ {v} }}\n  }} in {{\n"
                      "    if @Int.0 > 0 then {{ throw(@Int.0) }} else {{ {v} }}\n  }}", "{X}"),
    "array": ("[{v}]", "Array<{X}>"),
    "array_later": ("[{w}, {v}]", "Array<{X}>"),
    "generic_arg": ("idg({v})", "{X}"),
    "generic_beside": ("pick({v}, {w})", "{X}"),
    "builtin_arg": ("array_reverse({v})", "{X}"),
    "some": ("Some({v})", "Option<{X}>"),
    "generic_ctor": ("MkG({v})", "G<{X}>"),
    "plain_ctor": ("MkW({v})", "W"),
    "tuple": ("Tuple({v}, 1)", "Tuple<{X}, Int>"),
    "block": ("{{ {v} }}", "{X}"),
    "if": ("if @Int.0 > 0 then {{ {v} }} else {{ {v} }}", "{X}"),
    "match": ("match @Int.0 > 0 {{\n    true -> {v},\n    false -> {v}\n  }}", "{X}"),
    "eq": ("eq({v}, {w})", "Bool"),
    "eq_swapped": ("eq({w}, {v})", "Bool"),
}

#: type template: a value of that type over {w}, a closed value of X.
_VALUE_OF = {
    "{X}": "{w}", "Array<{X}>": "[{w}]", "Option<{X}>": "Some({w})",
    "G<{X}>": "MkG({w})", "Tuple<{X}, Int>": "Tuple({w}, 1)", "Bool": "true",
    "W": "MkW({w})",
}

SOURCES = ("let", "return", "parameter", "beside", "field", "pattern")

#: A data type with no type parameters names no `T`: in the `forall<T>`
#: function its field is no context, and the parameter's function would be
#: another generic.
_CONCRETE_ONLY = {"plain_ctor", "parameter", "field"}

_GENERIC_SIG = ("private forall<T where Ord<T>> fn f(@T, {params} -> {ret})\n"
                + _SIG)


def _cell(construct: str, value: str, source: str,
          scope: str = "concrete") -> str | None:
    generic = scope == "generic"
    v, x, w, eqable = (GENERIC_VALUES if generic else VALUES)[value]
    template, type_template = CONSTRUCTS[construct]
    if construct.startswith("eq") and not eqable:
        return None
    if construct == "builtin_arg" and not x.startswith("Array"):
        return None
    if generic and (construct in _CONCRETE_ONLY or source in _CONCRETE_ONLY):
        return None
    e = template.format(v=v, w=w)
    t = type_template.format(X=x)
    decls = f"\nprivate data W {{ MkW({x}) }}\n" if construct == "plain_ctor" else ""
    params, ret = "@Int", "@Int"
    if source == "let":
        body = f"let @{t} = {e};\n  0"
    elif source == "return":
        ret, body = f"@{t}", e
    elif source == "parameter":
        decls += f"\nprivate fn take(@{t} -> @Int)\n{_SIG}{{\n  0\n}}\n"
        body = f"take({e})"
    elif source == "beside":
        params, body = f"@Int, @{t}", f"pick({e}, @{t}.0);\n  0"
    elif source == "field":
        decls += f"\nprivate data H {{ MkH({t}) }}\n"
        body = f"MkH({e});\n  0"
    else:
        body = f"match {e} {{\n    @{t} -> 0\n  }}"
    if not generic:
        return _main(body, ret=ret, params=params, decls=decls)
    # The generic function, and a `main` that builds it at `Int`, with a
    # value of the type its last parameter is at `T = Int` where it has one.
    if source == "beside":
        made = _VALUE_OF[type_template].format(w=VALUES[value][2])
        call = f"f(5, 0, {made});\n  0"
    else:
        call = "f(5, 0);\n  0"
    return (_HELPERS + decls + "\n"
            + _GENERIC_SIG.format(params=params, ret=ret)
            + f"{{\n  {body}\n}}\n"
            + f"\npublic fn main(@Int -> @Int)\n{_SIG}{{\n  {call}\n}}\n")


SCOPES = ("concrete", "generic")

_CELLS = [(c, v, s, sc) for sc in SCOPES for c in CONSTRUCTS for v in VALUES
          for s in SOURCES if _cell(c, v, s, sc) is not None]


@pytest.mark.parametrize(("construct", "value", "source", "scope"), _CELLS)
def test_the_context_reaches_the_construct(construct: str, value: str,
                                           source: str, scope: str) -> None:
    program = _cell(construct, value, source, scope)
    assert program is not None
    if construct.startswith("eq") and value == "ok":
        # #1921: the ability operation's judge.
        assert _codes(program) == ["E241"], program
        return
    _clean(program)
    if value == "index_call":
        # The index's type reaches the generic collection call it reads.
        instances = {pretty_type(rec.mapping["T"])
                     for rec in pipeline.check(program).artifacts
                     .instantiations.values()
                     if rec.callee.endswith("empty_of")}
        assert instances == {"T" if scope == "generic" else "Int"}, program
    if scope == "generic":
        # `main` builds `f` at `Int`, and the clone is compiled.
        funcs = re.findall(r"\(func \$(\S+)",
                           pipeline.compile(program).result.wat)
        assert any(name.endswith("f$Int") for name in funcs), program


# ---------------------------------------------------------------------
# The census
# ---------------------------------------------------------------------

#: Programs that hold a variable no context names, or one only a
#: constructor pattern names, by reason, with each open part the census
#: finds in them (`line: type`, a minted variable's number read as `n`):
#: a part found beyond these fails, and one of these no longer found makes
#: the exemption stale.
CENSUS_EXEMPT: dict[str, tuple[str, frozenset[str]]] = {
    'tests/conformance/ch09_generic_none_nested.vera': (
        '`match nest(()) { Some(@Option<Int>) .. }`: only a constructor pattern names the variable',
        frozenset({
            '73: Option<Option<T$n>>',
            '73: nest: T unbound',
            '74: Option<Option<T$n>>',
            '74: Option<T$n>',
            '78: Option<Option<T$n>>',
            '80: Option<Option<Option<T$n>>>',
            '80: nest3: T unbound',
            '81: Option<Option<Option<T$n>>>',
            '81: Option<Option<T$n>>',
            '88: Option<Option<Option<T$n>>>',
        })),
    'tests/conformance/ch09_none_err_inference.vera': (
        '`result_unwrap_or(Ok(77), 0)`: no context names the error type',
        frozenset({
            '50: Result<Int, E$n>',
            '50: result_unwrap_or: E#b = E$n',
        })),
    'tests/conformance/ch09_option_result_combinators.vera': (
        '`result_unwrap_or`/`result_map` over `Ok(..)`: no context names the error type',
        frozenset({
            '42: Result<Int, E$n>',
            '42: result_unwrap_or: E#b = E$n',
            '51: Result<Int, E$n>',
            '51: result_map: E#b = E$n',
            '51: result_unwrap_or: E#b = E$n',
        })),
    'tests/conformance/ch09_prelude.vera': (
        '`match None { Some(@Int) .. }`, `match Ok(99) { .. Err(@String) }`: only a constructor pattern names the variable',
        frozenset({
            '23: Option<T$n>',
            '24: Option<T$n>',
            '24: T$n',
            '25: Option<T$n>',
            '37: Result<Int, E$n>',
            '38: Result<Int, E$n>',
            '39: E$n',
            '39: Result<Int, E$n>',
            '48: Result<T$n, String>',
            '49: Result<T$n, String>',
            '49: T$n',
            '50: Result<T$n, String>',
            '164: Result<Int, E$n>',
            '164: result_unwrap_or: E#b = E$n',
            '219: Result<Int, E$n>',
            '219: result_map: E#b = E$n',
            '219: result_unwrap_or: E#b = E$n',
        })),
}


def _census_parts(checked: pipeline.Checked) -> frozenset[str]:
    """`_open_parts`, a minted variable's number read as `n`."""
    return frozenset(re.sub(r"(\$|#f)\d+", r"\1n", f)
                     for f in _open_parts(checked))


def _doc_gate() -> Any:
    spec = importlib.util.spec_from_file_location(
        "check_doc_examples", ROOT / "scripts" / "check_doc_examples.py")
    assert spec is not None and spec.loader is not None
    cde = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(cde)
    return cde


_CDE = _doc_gate()


def _corpus() -> list[tuple[str, Path | None, Any]]:
    """Each program file, and each gated document block with the
    document it is in."""
    out: list[tuple[str, Path | None, Any]] = []
    for d in ("examples", "tests/conformance"):
        for p in sorted((ROOT / d).rglob("*.vera")):
            out.append((p.relative_to(ROOT).as_posix(), p, None))
    for rel in _CDE.expand_gates(ROOT)[0]:
        blocks, _ = _CDE.scan_document(ROOT / rel)
        for i, b in enumerate(blocks):
            if _CDE.selects(b):
                out.append((f"{rel}#{i}", None, (rel, b)))
    return out


_CORPUS = _corpus()


@pytest.fixture(scope="module")
def doc_workspace(tmp_path_factory: pytest.TempPathFactory) -> Any:
    """The documentation gate's workspace: a block is written beside the
    import root, so an import (`vera.collections`) resolves."""
    return _CDE.Workspace(ROOT, tmp_path_factory.mktemp("census"))


def test_census_finds_an_open_part() -> None:
    """The census's own controls: an exempt program is found, and so is a
    built-in's variable no context names (`map_new()`), so the census reads
    what it claims to."""
    path = ROOT / "tests/conformance/ch09_none_err_inference.vera"
    assert _open_parts(pipeline.check(path)) != []
    assert _open_parts(pipeline.check(_main(
        "let @Nat = map_size(map_new());\n  0"))) != []


@pytest.mark.parametrize(("label", "path", "block"), _CORPUS,
                         ids=[c[0] for c in _CORPUS])
def test_census_no_open_part_in_a_checking_program(
        label: str, path: Path | None, block: Any, doc_workspace: Any) -> None:
    if path is None:
        path = doc_workspace.write(*block)
    checked = pipeline.check(path)
    if not checked.ok or any(d.error_code == "W001"
                             for d in checked.warnings):
        # A refused program, or a typed hole, whose W001 names its type.
        return
    found = _census_parts(checked)
    expected = CENSUS_EXEMPT.get(label, ("", frozenset()))[1]
    assert found == expected, label
