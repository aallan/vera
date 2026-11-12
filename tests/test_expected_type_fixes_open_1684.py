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

import typing

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


# ---------------------------------------------------------------------
# B: a variable two arguments give different types takes one type,
# whichever comes first
# ---------------------------------------------------------------------

_SECOND = _fn("second", "@T, @T", "T", "@T.0", forall="forall<T> ")

_FN_PAIR = """\
type NatFn = fn(Nat -> Int) effects(pure);

type IntFn = fn(Int -> Int) effects(pure);

"""


@pytest.mark.parametrize("order", ["int_first", "nat_first"])
def test_repro_a_nat_closure_is_never_handed_a_negative_int(
        order: str) -> None:
    """`second(int_fn, nat_fn)` applied to -5.  At 6e272f19 the first
    argument fixed `T` at `fn(Int -> Int)`, the second fitted it, and the
    `Nat` closure ran on -5 and returned -5, every gate green; in the other
    order `T` was `fn(Nat -> Int)` and the -5 was refused.  `T` is now what
    both accept, `fn(Nat -> Int)`, in both orders, and the -5 bound into
    its parameter is refuted (E503)."""
    int_fn = "fn(@Int -> @Int) effects(pure) { @Int.0 }"
    nat_fn = "fn(@Nat -> @Int) effects(pure) { nat_to_int(@Nat.0) }"
    a, b = (int_fn, nat_fn) if order == "int_first" else (nat_fn, int_fn)
    source = _FN_PAIR + _SECOND + "\n" + _fn(
        "main", "@Unit", "Int", f"apply_fn(second({a}, {b}), 0 - 5)",
        visibility="public")
    assert _instances(source, "second") == {("fn(Nat -> Int)",)}
    verified = pipeline.verify(source, reconcile=True)
    assert [e.error_code for e in verified.errors] == ["E503"], [
        e.format() for e in verified.errors]


# ---------------------------------------------------------------------
# The matrix: site x pair x order x expected
# ---------------------------------------------------------------------

_MATRIX_PRE = """\
type PosInt = { @Int | @Int.0 > 0 };

type Small = { @Int | @Int.0 < 10 };

type NatFn = fn(Nat -> Int) effects(pure);

type IntFn = fn(Int -> Int) effects(pure);

type SmallFn = fn(Small -> Int) effects(pure);

type PureCb = fn(Int -> Int) effects(pure);

type IOCb = fn(Int -> Int) effects(<IO>);

type TakesPure = fn(PureCb -> Int) effects(pure);

type TakesIO = fn(IOCb -> Int) effects(pure);

"""

_IO_CB = 'fn(@Int -> @Int) effects(<IO>) { IO.print("cb"); @Int.0 }'


class _Pair(typing.NamedTuple):
    """Two values of two types, *strong* the one a value of which is also
    one of *weak* (a subtype), the formals and arguments of `f` that make
    them, the type both accept (the join, None where there is none), and
    how a value of each type is read into an `Int`."""

    strong: str
    weak: str
    a: str           # the value of type `strong`
    b: str           # the value of type `weak`
    formals: str
    actuals: str
    join: str | None
    unrelated: str   # an expected type neither fits
    #: Whether a `weak` value fits a `strong` parameter: a narrowing
    #: (`Nat`, a refinement), or the relaxation a function type's
    #: parameter has at any parameter (issue #1819); an effect row has none.
    weak_fits: bool = True


#: How `f` reads an `Int` out of a value of each type, *v* the value.
_READ = {
    "Nat": "nat_to_int({v})", "Int": "{v}", "PosInt": "{v}",
    "String": "nat_to_int(string_length({v}))", "Bool": "0",
    "IntFn": "apply_fn({v}, 0 - 5)", "NatFn": "apply_fn({v}, 0 - 5)",
    "SmallFn": "apply_fn({v}, 50)",
    "TakesPure": "apply_fn({v}, " + _IO_CB + ")",
    "TakesIO": "apply_fn({v}, " + _IO_CB + ")",
}

PAIRS = {
    "nat_int": _Pair("Nat", "Int", "@Nat.0", "@Int.0", "@Nat, @Int",
                     "1, 0 - 5", "Int", "String"),
    "refined_base": _Pair("PosInt", "Int", "@PosInt.0", "@Int.0",
                          "@PosInt, @Int", "1, 0 - 5", "Int", "String"),
    "fn_param": _Pair(
        "IntFn", "NatFn", "fn(@Int -> @Int) effects(pure) { @Int.0 }",
        "fn(@Nat -> @Int) effects(pure) { nat_to_int(@Nat.0) }",
        "@Unit", "()", "NatFn", "String"),
    "refined_param": _Pair(
        "IntFn", "SmallFn", "fn(@Int -> @Int) effects(pure) { @Int.0 }",
        "fn(@Small -> @Int) effects(pure) { @Small.0 }",
        "@Unit", "()", "SmallFn", "String"),
    "effect_row": _Pair(
        "TakesIO", "TakesPure",
        "fn(@IOCb -> @Int) effects(pure) { 0 }",
        "fn(@PureCb -> @Int) effects(pure) { apply_fn(@PureCb.0, 1) }",
        "@Unit", "()", "TakesPure", "String", weak_fits=False),
    "unrelated": _Pair("Int", "String", "@Int.0", "@String.0",
                       "@Int, @String", '1, "s"', None, "Bool"),
}

#: The generic each call site calls, `T` its variable.
_SITE_DECLS = {
    "two_parameter": _SECOND,
    "pick": _fn("pick", "@Bool, @T, @T", "T",
                "if @Bool.0 then { @T.1 } else { @T.0 }",
                forall="forall<T> "),
}
_SITE_CALL = {"two_parameter": "second({x}, {y})",
              "pick": "pick(false, {x}, {y})"}

#: Every site: the two calls, and the array literal of the two values,
#: whose element type the same rule gives (spec §4.12.1).
SITES = [*_SITE_DECLS, "array"]

EXPECTED = ["none", "stronger", "weaker", "unrelated"]


def _expected_type(pair: _Pair, expected: str) -> str | None:
    return {"none": None, "stronger": pair.strong, "weaker": pair.weak,
            "unrelated": pair.unrelated}[expected]


def _instance(pair: _Pair, expected: str) -> str | None:
    """The type the rule gives `T`: the expected type where both values
    fit it (a `strong` value fits `weak`; neither fits `unrelated`),
    otherwise the type both accept."""
    want = _expected_type(pair, expected)
    if pair.join is not None and (
            want == pair.weak or (want == pair.strong and pair.weak_fits)):
        return want
    return pair.join


def _read(pair: _Pair, want: str | None, value: str) -> str:
    """`f`'s body reading *value*: at *want* where a type is expected, and
    where none is, as an operand or an applied function."""
    if want is None:
        return (f"{value} + 0" if pair.join in ("Int", None)
                else _READ[pair.join].replace("{v}", value))
    return f"let @{want} = {value};\n" + _READ[want].replace(
        "{v}", f"@{want}.0")


def _program(site: str, pair: _Pair, order: str, expected: str,
             decl: str, element: str | None = None) -> str:
    """The cell's program.  At the array site *element*, where given, is
    the twin's element type: the literal is bound at it, and its second
    element read where the cell's expected type (or none) reads it."""
    x, y = (pair.a, pair.b) if order == "strong_first" else (pair.b, pair.a)
    want = _expected_type(pair, expected)
    if site == "array":
        literal = f"[{x}, {y}]"
        held = element or want
        if held is None:
            read = _read(pair, None, f"{literal}[1]")
        else:
            read = (f"let @Array<{held}> = {literal};\n"
                    + _read(pair, want, f"@Array<{held}>.0[1]"))
    else:
        read = _read(pair, want, _SITE_CALL[site].format(x=x, y=y))
    return (_MATRIX_PRE + decl + "\n"
            + _fn("f", pair.formals, "Int", read, effect="<IO>") + "\n"
            + _fn("main", "@Unit", "Int", f"f({pair.actuals})",
                  effect="<IO>", visibility="public"))


def _twin(site: str, instance: str) -> str:
    """The site's generic written at *instance*: the program the rule
    makes the call, its arguments held to *instance* where they are
    passed."""
    return _SITE_DECLS[site].replace("forall<T> ", "").replace("T", instance)


def _outcome(source: str) -> tuple[object, ...]:
    """What the program does: its check codes, and for one that checks,
    its verify codes, its narrowing rows (kind, status, the expression
    narrowed, which says whether an argument or the call's result is),
    and, for one `vera verify` passes, its run (the value, or the trap's
    first line).  The narrowing rows are `f`'s, so the twin's own entry
    checks are not counted; a refuted narrowing refuses the program, so
    where `vera run` would have trapped on it is not compared."""
    checked = pipeline.check(source)
    codes = tuple(e.error_code for e in checked.errors)
    if codes:
        return (codes,)
    verified = pipeline.verify(source, reconcile=True)
    rows = tuple(sorted((o.kind, o.status, o.expr_text)
                        for o in verified.obligations
                        if o.kind in ("nat_bind", "refine_bind")
                        and o.fn_name == "f"))
    refused = tuple(e.error_code for e in verified.errors)
    if refused:
        return ((), refused, rows)
    ran = pipeline.run(source)
    run = (("trap", str(ran.trap).splitlines()[0]) if ran.trap is not None
           else ("value", ran.value, ran.stdout))
    return ((), refused, rows, run)


@pytest.mark.parametrize("expected", EXPECTED)
@pytest.mark.parametrize("order", ["strong_first", "weak_first"])
@pytest.mark.parametrize("pair", list(PAIRS))
@pytest.mark.parametrize("site", SITES)
def test_a_call_s_variable_takes_one_type_whichever_comes_first(
        site: str, pair: str, order: str, expected: str) -> None:
    """The call records `T` at the rule's type, and the program does what
    the same call to the generic written at that type does, in both
    orders: the same verdict, the same narrowing at the same expression
    (an argument where the expected type was taken, the call's result
    where the join was), and the same run."""
    p = PAIRS[pair]
    source = _program(site, p, order, expected, _SITE_DECLS.get(site, ""))
    instance = _instance(p, expected)
    if instance is None:
        # Two types no position reconciles: refused, in both orders.
        assert _outcome(source)[0], _outcome(source)
        return
    if site == "array":
        # The literal bound at the element type the rule gives it.
        twin = _program(site, p, order, expected, "", element=instance)
        assert _outcome(source) == _outcome(twin), instance
        return
    key = "second" if site == "two_parameter" else "pick"
    checked = pipeline.check(source)
    recorded = ({i.args for i in checked.typed.instances if i.key == key}
                if checked.ok else None)
    twin = _program(site, p, order, expected, _twin(site, instance))
    assert _outcome(source) == _outcome(twin), (recorded, instance)
    if checked.ok:
        # An instance is built at its type with every refinement stripped.
        names = {"IntFn": "fn(Int -> Int)", "NatFn": "fn(Nat -> Int)",
                 "SmallFn": "fn(Int -> Int)", "PosInt": "Int",
                 "TakesPure": "fn(PureCb -> Int)",
                 "TakesIO": "fn(IOCb -> Int)"}
        assert recorded is not None
        (args,) = recorded
        assert args[0] in (instance, names.get(instance)), (args, instance)


# ---------------------------------------------------------------------
# B, nested: a position the arguments' join decided is provisional until
# the context declines to decide it
# ---------------------------------------------------------------------

_INT_FN = "fn(@Int -> @Int) effects(pure) { @Int.0 }"
_NAT_FN = "fn(@Nat -> @Int) effects(pure) { nat_to_int(@Nat.0) }"


def _chain(depth: int, inner: str, fill: str = "{n}",
           outer: str = "second") -> str:
    """*outer* nested *depth* deep around *inner* (a call that holds the
    disagreement): `second`, each level adding the literal or value
    *fill* beside it (the seeds' shape, where a literal's hole meets the
    join), or `id`, which gives each level nothing but the call below."""
    call = inner
    for n in range(1, depth):
        call = (f"id({call})" if outer == "id"
                else f"second({call}, {fill.replace('{n}', str(n))})")
    return call


def _nested(depth: int, order: str, expected: str | None,
            outer: str = "second") -> str:
    x, y = ("@Nat.0", "@Int.0") if order == "nat_first" else (
        "@Int.0", "@Nat.0")
    call = _chain(depth, f"second({x}, {y})", outer=outer)
    if expected is None:
        body = f"{call} + 0"
    elif expected == "Nat":
        body = f"let @Nat = {call};\nnat_to_int(@Nat.0)"
    elif expected == "Int":
        body = f"let @Int = {call};\n@Int.0"
    else:
        body = f'let @{expected} = {call};\n0'
    return (_SECOND + "\n" + _ID + "\n"
            + _fn("f", "@Nat, @Int", "Int", body) + "\n"
            + _fn("main", "@Unit", "Int", "f(1, 0 - 5)", visibility="public"))


def _narrowed(source: str) -> list[tuple[str, str]]:
    return sorted((o.status, o.expr_text)
                  for o in pipeline.verify(source).obligations
                  if o.kind == "nat_bind" and o.fn_name == "f")


@pytest.mark.parametrize("order", ["nat_first", "int_first"])
@pytest.mark.parametrize("depth", [2, 3])
@pytest.mark.parametrize("outer", ["second", "id"])
def test_repro_seed317_the_binding_decides_every_level(
        depth: int, order: str, outer: str) -> None:
    """The shape of generator seeds 317 and 335 reduced: the outer call
    bound at `@Nat`, the inner holding a `Nat` beside an `Int`.  The inner
    call has no expected type (a generic's arguments are given none), so
    it joins at `Int`; that position is provisional, the binding decides
    the outer call's variable at `Nat`, and the inner call is synthesized
    again against it, where `Nat` is expected and both arguments fit it.
    Every level is at `Nat`, and the narrowing is the `Int` argument's,
    where the caller's facts prove it (here refuted: `f(1, 0 - 5)`).  At
    the rule-B commit the join stood: every level `Int`, the narrowing the
    binding's."""
    source = _nested(depth, order, "Nat", outer)
    assert _instances(source, "second") == {("Nat",)}
    if outer == "id":
        assert _instances(source, "id") == {("Nat",)}
    assert _narrowed(source) == [("violated", "@Int.0")]


@pytest.mark.parametrize("order", ["nat_first", "int_first"])
@pytest.mark.parametrize("expected", [None, "Int"])
@pytest.mark.parametrize("depth", [2, 3])
@pytest.mark.parametrize("outer", ["second", "id"])
def test_a_nested_join_no_context_decides_stands(
        depth: int, expected: str | None, order: str, outer: str) -> None:
    """Nothing expected outside, or an `Int` (which both fit and which is
    the join): every level is the join, `Int`, and nothing narrows."""
    source = _nested(depth, order, expected, outer)
    assert _instances(source, "second") == {("Int",)}
    if outer == "id":
        assert _instances(source, "id") == {("Int",)}
    assert _narrowed(source) == []


@pytest.mark.parametrize("order", ["nat_first", "int_first"])
@pytest.mark.parametrize("depth", [2, 3])
@pytest.mark.parametrize("outer", ["second", "id"])
def test_a_nested_join_an_unrelated_binding_declines_is_refused_once(
        depth: int, order: str, outer: str) -> None:
    """A `String` binding fits no level: every level stays the join, and
    the mismatch is reported once, at the binding."""
    errors = pipeline.check(_nested(depth, order, "String", outer)).errors
    assert [e.error_code for e in errors] == ["E170"], [
        e.format() for e in errors]


@pytest.mark.parametrize("order", ["int_fn_first", "nat_fn_first"])
@pytest.mark.parametrize("depth", [2, 3])
def test_a_nested_function_pair_joins_by_polarity_at_every_level(
        depth: int, order: str) -> None:
    """The function-type pair nested the same way, nothing expected: every
    level is what both accept, `fn(Nat -> Int)`, so the -5 is refuted
    (E503); bound at `IntFn`, which both fit (issue #1819's relaxation),
    every level is `fn(Int -> Int)`."""
    x, y = (_INT_FN, _NAT_FN) if order == "int_fn_first" else (
        _NAT_FN, _INT_FN)
    call = _chain(depth, f"second({x}, {y})", fill=_INT_FN)
    joined = _FN_PAIR + _SECOND + "\n" + _fn(
        "main", "@Unit", "Int", f"apply_fn({call}, 0 - 5)",
        visibility="public")
    assert _instances(joined, "second") == {("fn(Nat -> Int)",)}
    assert [e.error_code for e in pipeline.verify(joined).errors] == ["E503"]
    bound = _FN_PAIR + _SECOND + "\n" + _fn(
        "main", "@Unit", "Int",
        f"let @IntFn = {call};\napply_fn(@IntFn.0, 0 - 5)",
        visibility="public")
    assert _instances(bound, "second") == {("fn(Int -> Int)",)}


@pytest.mark.parametrize("outer", ["second", "id"])
def test_a_join_no_context_decides_is_recorded_as_the_join(
        outer: str) -> None:
    """Every later reader of a call whose join no context decided reads
    the join: the type the check records for each level of the chain is
    `Int`, and no record holds the provisional mark."""
    source = _nested(3, "nat_first", None, outer)
    checked = pipeline.check(source)
    assert checked.ok, [e.format() for e in checked.errors]
    recorded = checked.artifacts.expr_types
    calls = {text for key, text in recorded.items()}
    assert not any("join" in text for text in calls), calls
    lines = source.splitlines()
    body_line = next(i for i, text in enumerate(lines, 1)
                     if f"{outer}({outer}(" in text)
    at_body = [text for key, text in recorded.items()
               if key[0] == body_line and text != "Nat"]
    assert set(at_body) == {"Int"}, at_body


def test_an_inner_argument_s_own_error_is_reported_once() -> None:
    """A three-deep chain whose innermost argument is wrong on its own
    (`nope(1)`, no such function), bound at `@Nat`: each level is
    synthesized again against the binding's type, and the error is
    reported once."""
    call = _chain(3, "second(@Nat.0, nope(1))")
    source = _SECOND + "\n" + _fn(
        "f", "@Nat, @Int", "Int", f"let @Nat = {call};\nnat_to_int(@Nat.0)")
    errors = pipeline.check(source).errors
    assert [e.error_code for e in errors] == ["E200"], [
        e.format() for e in errors]


def test_an_eight_deep_chain_synthesizes_each_argument_once_per_level(
        monkeypatch: pytest.MonkeyPatch) -> None:
    """The cost of the provisional join: bound at `@Nat`, each level of a
    chain is synthesized again against the binding's type once, so the
    innermost argument of an eight-deep chain is synthesized eight times
    (the #1541 literal path: nine) and the whole chain 70 times more than
    the same chain with nothing expected.  A re-synthesis that doubled per
    level (each level synthesizing its argument twice) would count 2**8."""
    from vera import ast
    from vera.checker.core import TypeChecker

    synth = TypeChecker._synth_expr
    counts = {"all": 0, "innermost": 0}

    def counted(self, expr, *, expected=None):  # type: ignore[no-untyped-def]
        counts["all"] += 1
        if isinstance(expr, ast.SlotRef) and expr.type_name == "Int":
            counts["innermost"] += 1
        return synth(self, expr, expected=expected)

    monkeypatch.setattr(TypeChecker, "_synth_expr", counted)
    call = _chain(8, "second(@Nat.0, @Int.0)")
    totals = {}
    for bound, body in (
            (True, f"let @Nat = {call};\nnat_to_int(@Nat.0)"),
            (False, f"{call} + 0")):
        counts.update(all=0, innermost=0)
        assert pipeline.check(_SECOND + "\n" + _fn(
            "f", "@Nat, @Int", "Int", body)).ok
        totals[bound] = dict(counts)
    assert totals[True]["innermost"] == 8
    assert totals[False]["innermost"] == 1
    assert totals[True]["all"] - totals[False]["all"] == 70


# ---------------------------------------------------------------------
# J: an array literal's element type by the same rule
# ---------------------------------------------------------------------

@pytest.mark.parametrize("form", ["let", "return", "closure"])
def test_repro_line_1_elements_left_open_take_the_context_s_type(
        form: str) -> None:
    """Line 1: `[None, None]` where an `Array<Option<Nat>>` is expected.
    At 6e272f19 the elements left the element type `Option<?>`, which the
    holding site met by name: E170, E121, E171.  The context's element
    type fills what the elements leave open."""
    if form == "let":
        body = ("let @Array<Option<Nat>> = [None, None];\n"
                "array_length(@Array<Option<Nat>>.0)")
        source = _fn("main", "@Unit", "Nat", body, visibility="public")
    elif form == "return":
        source = (_fn("nones", "@Unit", "Array<Option<Nat>>",
                      "[None, None]") + "\n"
                  + _fn("main", "@Unit", "Nat",
                        "array_length(nones(()))", visibility="public"))
    else:
        source = ("type Mk = fn(Unit -> Array<Option<Nat>>) effects(pure);\n\n"
                  + _fn("main", "@Unit", "Nat",
                        "let @Mk = fn(@Unit -> @Array<Option<Nat>>) "
                        "effects(pure) { [None, None] };\n"
                        "array_length(apply_fn(@Mk.0, ()))",
                        visibility="public"))
    checked = pipeline.check(source)
    assert checked.ok, [e.format() for e in checked.errors]
    assert pipeline.run(source).value == 2


_IDG = _fn("idg", "@T", "T", "@T.0", forall="forall<T> ")


@pytest.mark.parametrize("order", ["refined_first", "base_first"])
def test_repro_find_a_the_literal_s_type_does_not_depend_on_order(
        order: str) -> None:
    """Find (a): `idg([@PosInt.0, @Int.0])`.  At 6e272f19 the first element
    decided the element type: refined first, the `Int` element was held
    to `PosInt` and refuted (E505); base first, the literal was
    `Array<Int>`.  The elements' join is `Int` in both orders, and the
    program verifies and prints 2."""
    a, b = ("@PosInt.0", "@Int.0") if order == "refined_first" else (
        "@Int.0", "@PosInt.0")
    source = ("type PosInt = { @Int | @Int.0 > 0 };\n\n" + _IDG + "\n"
              + _fn("f", "@PosInt, @Int", "Nat",
                    f"array_length(idg([{a}, {b}]))") + "\n"
              + _fn("main", "@Unit", "Nat", "f(1, 0 - 5)",
                    visibility="public"))
    assert pipeline.verify(source).errors == ()
    assert _instances(source, "idg") == {("Array<Int>",)}
    assert pipeline.run(source).value == 2


@pytest.mark.parametrize("order", ["nat_first", "int_first"])
def test_an_expected_element_type_holds_each_element(order: str) -> None:
    """`let @Array<Nat> = [@Nat.0, @Int.0]`: both fit `Nat`, so the
    element type is `Nat` and the `Int` element is the narrowing, refuted
    at the element in both orders (as at 6e272f19)."""
    a, b = ("@Nat.0", "@Int.0") if order == "nat_first" else (
        "@Int.0", "@Nat.0")
    source = _fn("f", "@Nat, @Int", "Int",
                 f"let @Array<Nat> = [{a}, {b}];\n"
                 "nat_to_int(array_length(@Array<Nat>.0))")
    assert [row for row in _narrowed(source)
            if row[1] == "@Int.0" or row[1].startswith("[")] == [
        ("violated", "@Int.0")]
