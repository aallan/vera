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

* the matrix, construct (16) x open value (8) x where the type comes from
  (a `let`, a return, a parameter, a generic call's other argument, a
  constructor field, a `match` binder pattern) x whether the type holds the
  enclosing `forall<T>` function's own `T`: each cell checks, no type
  or instance it records holds an unknown or a variable left open, and it
  compiles with no function dropped.  The cells of `eq` over two `Result`s
  that each leave the other's variable open are refused by the ability
  operation's judge, #1921's mechanism: they are pinned as they are;
* the census: over the corpus and the documents' blocks, no expression of a
  program that checks holds an open type or instance, except where no
  context names the variable (the programs named in `CENSUS_EXEMPT`).
"""

from __future__ import annotations

import importlib.util
from pathlib import Path

import pytest

from tests import pipeline
from vera.types import contains_fresh_typevar, contains_unknown, pretty_type

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


def _open_parts(checked: pipeline.Checked) -> list[str]:
    """Each recorded type holding an unknown or a variable left open, and
    each instantiation that leaves a callee's variable unbound or open."""
    art = checked.artifacts
    found = {pretty_type(t) for t in art.node_semantic_types.values()
             if t is not None
             and (contains_unknown(t) or contains_fresh_typevar(t))}
    for rec in art.instantiations.values():
        for tv in rec.forall_vars:
            bound = rec.mapping.get(tv)
            if bound is None:
                found.add(f"{rec.callee}: {tv} unbound")
            elif contains_unknown(bound) or contains_fresh_typevar(bound):
                found.add(f"{rec.callee}: {tv} = {pretty_type(bound)}")
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
    # The generic function, and a `main` that builds it at `Int` where
    # its parameters are `T` and `Int` alone.
    call = "f(5, 0);\n  0" if source != "beside" else "0"
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


# ---------------------------------------------------------------------
# The census
# ---------------------------------------------------------------------

#: Programs that hold a variable no context names, or one only a
#: constructor pattern names, by reason.
CENSUS_EXEMPT = {
    "tests/conformance/ch09_none_err_inference.vera":
        "`result_unwrap_or(Ok(77), 0)`: no context names the error type",
    "tests/conformance/ch09_option_result_combinators.vera":
        "`result_unwrap_or`/`result_map` over `Ok(..)`: no context names "
        "the error type",
    "tests/conformance/ch09_prelude.vera":
        "`match None { Some(@Int) .. }`, `match Ok(99) { .. Err(@String) }`"
        ": only a constructor pattern names the variable",
    "tests/conformance/ch09_generic_none_nested.vera":
        "`match nest(()) { Some(@Option<Int>) .. }`: only a constructor "
        "pattern names the variable",
}


def _corpus() -> list[tuple[str, str, str | None]]:
    spec = importlib.util.spec_from_file_location(
        "check_doc_examples", ROOT / "scripts" / "check_doc_examples.py")
    assert spec is not None and spec.loader is not None
    cde = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(cde)
    out: list[tuple[str, str, str | None]] = []
    for d in ("examples", "tests/conformance"):
        for p in sorted((ROOT / d).rglob("*.vera")):
            out.append((p.relative_to(ROOT).as_posix(), str(p), None))
    for rel in cde.expand_gates(ROOT)[0]:
        blocks, _ = cde.scan_document(ROOT / rel)
        for i, b in enumerate(blocks):
            if cde.selects(b):
                out.append((f"{rel}#{i}", b.content, "doc_block.vera"))
    return out


_CORPUS = _corpus()


def test_census_finds_an_open_part() -> None:
    """The census's own control: an exempt program is found, so the census
    reads what it claims to."""
    path = ROOT / "tests/conformance/ch09_none_err_inference.vera"
    assert _open_parts(pipeline.check(path)) != []


@pytest.mark.parametrize(("label", "source", "file"), _CORPUS,
                         ids=[c[0] for c in _CORPUS])
def test_census_no_open_part_in_a_checking_program(
        label: str, source: str, file: str | None) -> None:
    checked = pipeline.check(Path(source) if file is None else source,
                             file=file)
    if not checked.ok or any(d.error_code == "W001"
                             for d in checked.warnings):
        # A refused program, or a typed hole, whose W001 names its type.
        return
    found = _open_parts(checked)
    if label in CENSUS_EXEMPT:
        assert found, f"{label} is exempt and holds nothing open: drop it"
        return
    assert found == [], label
