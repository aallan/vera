"""An expected type fixes what a value's arguments or elements leave open,
and a type variable two arguments give different types takes one type
whichever comes first (#1684, lines 1 and 5, find (a)).

The rules, spec §5.9 and §4.12.1:

* C: a call's type variable no argument gives a type (unbound, or bound to
  a type holding a variable a nested call left open) takes it from the type
  the call's result is expected at, joined onto what the arguments gave, so
  nothing an argument fixed is overridden
  (`ResolutionMixin._infer_type_args_in_context`);
* B: a variable two or more arguments give different types takes the type
  the result is expected at where each of them fits it, each held to it
  where it is passed; otherwise the type they share (`_value_join`, the
  join of spec §4.8, its polarity at a function type's parameter included);
* J: an array literal's element type by the same rule over its elements,
  and the context's element type fills what the elements leave open;
* E and I: an empty literal takes its type from the context, and an index
  expected at a type reads an array of that type.

Before them the first argument (or element) to bind a variable decided its
type, so a variable bound by `fn(@Int -> @Int)` and then by
`fn(@Nat -> @Int)` was `fn(Int -> Int)` and the `Nat` closure ran on `-5`;
an expected type fixed only a literal's hole, so `[None, None]` met
`Array<Option<Nat>>` as `Array<Option<?>>` (E170), and
`string_length(head_plain([]))` compiled `head_plain` at the default
`Bool` and its module did not load.
"""

from __future__ import annotations

import pytest

from tests import pipeline

pytestmark = pytest.mark.matrix(decides=[
    "vera/checker/calls.py",
    "vera/checker/control.py",
    "vera/checker/expressions.py",
    "vera/checker/resolution.py",
])


def _fn(name: str, formals: str, ret: str, body: str, *,
        forall: str = "", effect: str = "pure",
        visibility: str = "private") -> str:
    indented = "\n".join(f"  {line}" if line else line
                         for line in body.splitlines())
    return (f"{visibility} {forall}fn {name}({formals} -> @{ret})\n"
            f"  requires(true)\n  ensures(true)\n"
            f"  effects({effect})\n{{\n{indented}\n}}\n")


def _codes(source: str) -> list[str]:
    return [e.error_code for e in pipeline.check(source).errors]


def _instances(source: str, key: str) -> set[tuple[str, ...]]:
    checked = pipeline.check(source)
    assert checked.ok, [e.format() for e in checked.errors]
    return {inst.args for inst in checked.typed.instances if inst.key == key}


def _trap(source: str) -> str:
    ran = pipeline.run(source)
    assert ran.trap is not None, ran.value
    return str(ran.trap)


_HEAD_PLAIN = _fn("head_plain", "@Array<T>", "T", "@Array<T>.0[0]",
                  forall="forall<T> ")


# ---------------------------------------------------------------------
# C: the expected type fixes a variable no argument gives a type
# ---------------------------------------------------------------------

def test_repro_line_5_an_empty_literal_s_variable_takes_the_expected_type(
) -> None:
    """Line 5: `head_plain([])` at a `String` parameter is `head_plain` at
    `String`.  At 6e272f19 the call kept the default `Bool`, the module
    did not load (`nothing on stack`); now it stops at the empty array's
    index, the trap the program owes."""
    source = _HEAD_PLAIN + "\n" + _fn(
        "main", "@Unit", "Int",
        "nat_to_int(string_length(head_plain([])))",
        visibility="public")
    assert _instances(source, "head_plain") == {("String",)}
    assert "Array index out of bounds" in _trap(source)


def test_repro_line_5_the_let_form_takes_the_binding_s_type() -> None:
    """`let @String = head_plain([]);` was E170 ("value has type ?")."""
    source = _HEAD_PLAIN + "\n" + _fn(
        "main", "@Unit", "Int",
        "let @String = head_plain([]);\n"
        "nat_to_int(string_length(@String.0))",
        visibility="public")
    assert _instances(source, "head_plain") == {("String",)}
    assert "Array index out of bounds" in _trap(source)


def test_repro_line_5_the_state_form_is_refused_once() -> None:
    """`let @Nat = rd(())` under a `State<Int>` handler: `rd` is at `Nat`,
    so its row asks `State<Nat>`, which the handler does not give (E125);
    the E170 "value has type ?" beside it at 6e272f19 is gone."""
    source = _fn("rd", "@Unit", "T", "get(())", forall="forall<T> ",
                 effect="<State<T>>") + "\n" + _fn(
        "main", "@Unit", "Int",
        "handle[State<Int>](@Int = 0 - 5) {\n"
        "  get(@Unit) -> { resume(@Int.0) },\n"
        "  put(@Int) -> { resume(()) }\n"
        "} in {\n"
        "  let @Nat = rd(());\n"
        "  nat_to_int(@Nat.0)\n"
        "}",
        visibility="public")
    assert _codes(source) == ["E125"]


_WRAP = _fn("wrap", "@T", "Option<T>", "Some(@T.0)", forall="forall<T> ")


def test_a_partly_open_binding_is_completed_by_the_expected_type() -> None:
    """`wrap(None)` binds `T` to `Option<?>`; the binding's `Option<Int>`
    completes it, so `wrap` is at `Option<Int>`."""
    source = _WRAP + "\n" + _fn(
        "main", "@Unit", "Int",
        "let @Option<Option<Int>> = wrap(None);\n"
        "match @Option<Option<Int>>.0 {\n"
        "  Some(@Option<Int>) -> option_unwrap_or(@Option<Int>.0, 7),\n"
        "  None -> 0\n"
        "}",
        visibility="public")
    assert _instances(source, "wrap") == {("Option<Int>",)}
    assert pipeline.run(source).value == 7


_ID = _fn("id", "@T", "T", "@T.0", forall="forall<T> ")


def test_the_expected_type_overrides_nothing_an_argument_fixed() -> None:
    """`let @Nat = id(@Int.0)`: the argument fixes `T` at `Int`, so `id`
    is at `Int`, and the narrowing is the binding's, of the call's result
    (not the argument's, which an expected `Nat` overriding `T` would make
    it)."""
    source = _ID + "\n" + _fn(
        "f", "@Int", "Nat", "let @Nat = id(@Int.0);\n@Nat.0") + "\n" + _fn(
        "main", "@Unit", "Nat", "f(4)", visibility="public")
    assert _instances(source, "id") == {("Int",)}
    rows = [(o.kind, o.expr_text) for o in pipeline.verify(source).obligations
            if o.kind == "nat_bind"]
    assert rows == [("nat_bind", "id(@Int.0)")], rows


_CELL = """\
private data Cell<T> { MkCell(fn(Unit -> Unit) effects(<State<T>>)) }

private forall<T> fn mkcell(@Unit -> @Cell<T>)
  requires(true)
  ensures(true)
  effects(pure)
{
  MkCell(fn(@Unit -> @Unit) effects(<State<T>>) { () })
}

"""

#: A value whose call leaves `T` open beside one that fixes it, at each
#: site that joins two values; the code a refusal there carries.
_SIBLING_SITES = {
    "if": ("if @Bool.0 then {{ {a} }} else {{ {b} }}", "E301"),
    "match": ("match @Bool.0 {{ true -> {a}, false -> {b} }}", "E302"),
}


@pytest.mark.parametrize("order", ["open_first", "open_second"])
@pytest.mark.parametrize("site", list(_SIBLING_SITES))
def test_a_sibling_s_type_is_no_expected_type(site: str, order: str) -> None:
    """An `if` branch or a `match` arm that leaves `mkcell`'s `T` open is
    synthesized again against its sibling's `Cell<Nat>`, for a
    constructor's sake; that type is not the one the value is expected at,
    so it fixes nothing, and the cell's behaviour-held `T` is refused in
    both orders, as at 6e272f19 (the `match` re-synthesizes only a later
    arm, so a sibling taken as expected would accept one order alone)."""
    shape, code = _SIBLING_SITES[site]
    a, b = "mkcell(())", "@Cell<Nat>.0"
    if order == "open_second":
        a, b = b, a
    source = _CELL + _fn("g", "@Cell<Nat>, @Bool", "Nat",
                         f"array_length([{shape.format(a=a, b=b)}])")
    assert _codes(source) == [code]


@pytest.mark.parametrize("order", ["open_first", "open_second"])
@pytest.mark.parametrize("site", list(_SIBLING_SITES))
def test_the_expected_type_reaches_every_branch(site: str, order: str) -> None:
    """The same join bound by a `let` at `Cell<Nat>`: that type is expected
    of each branch and arm, and fixes `mkcell`'s `T` at `Nat` in both
    orders."""
    shape, _ = _SIBLING_SITES[site]
    a, b = "mkcell(())", "@Cell<Nat>.0"
    if order == "open_second":
        a, b = b, a
    source = _CELL + _fn(
        "g", "@Cell<Nat>, @Bool", "Nat",
        f"let @Cell<Nat> = {shape.format(a=a, b=b)};\n0")
    assert _instances(source, "mkcell") == {("Nat",)}
