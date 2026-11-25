"""What a type states of a value, at every position the solver reads (#1814).

`Nat` is a refinement of `Int` (spec §2.2) and shares its sort in the solver,
so a `Nat` inside a data value, an array element or a tuple component was
unconstrained there: only a head `@Nat` and a `match` arm's direct binder
stated `>= 0`.  No value stated the i64 range of an `Int`, and a refinement
over a data type was neither decided at a call argument nor stated at a
position inside a type.  Correct programs were refuted with counterexamples
no value of the type has (`Tuple(-1, 2)` for a `Tuple<Nat, Nat>`, `[-1]` for
an `Array<Nat>`, `9223372036854775808` for an `Int`).

The rule: what a type states of a value (its range, every refinement over any
base, at every position, a recursive position by the type's own invariant)
is assumed of every constant whose value a check establishes before any
reader sees it (`ContractVerifier._type_invariant`), and a refinement over a
data type is decided at the position that gives a value its type.

The matrix: type x where the value comes from x how the obligation reads it x
what it rests on.  Every cell's `ensures` is true of every value of the type,
so every cell is `verified`.  A value from a call result waits for the
obligations to be discharged at their own program point (#1925), and
those cells are strict xfails until then.  The differential runs each
cell's function on values a checked producer built from the i64 boundary
values, and no postcondition check of the function may fire.
"""

from __future__ import annotations

import itertools

import pytest

from tests import pipeline
from vera.runtime.traps import WasmTrapError

pytestmark = pytest.mark.matrix(decides=[
    "vera/verifier.py", "vera/smt.py", "vera/binding.py"])

INT_MAX = 2**63 - 1
INT_MIN = -(2**63)
FILE = "cell.vera"

_DECLS = {
    "Pos": "type Pos = { @Int | @Int.0 > 0 };",
    "Box": "private data Box<T> { MkBox(T) }",
    "NB": "private data NB { MkNB(Nat) }",
    "NList": "private data NList { NCons(Nat, NList), NNil }",
    "List": "private data List<T> { Cons(T, List<T>), Nil }",
    "Color": "private data Color { Red, Green, Blue }",
    "NotRed": "type NotRed = { @Color | @Color.0 != Red };",
}

_SIGN = "@Int.result >= 0"
_HI = f"@Int.result <= {INT_MAX}"
_LO = f"@Int.result >= {INT_MIN}"
_POS = "@Int.result > 0"

#: name: (type, declarations, readers, result type, obligations, default,
#:        a checked producer's expression of the type from `@Int.0`)
_TYPES = {
    "Int": ("Int", [], {"direct": ("", "@Int.0")}, "Int",
            {"range_hi": _HI, "range_lo": _LO}, "0", "@Int.0"),
    "Nat": ("Nat", [], {"direct": ("", "nat_to_int(@Nat.0)")}, "Int",
            {"sign": _SIGN, "range_hi": _HI}, "0", "@Int.0"),
    "Pos": ("Pos", ["Pos"], {"direct": ("", "@Pos.0")}, "Int",
            {"pred": _POS}, "1", "@Int.0"),
    "OptNat": ("Option<Nat>", [], {
        "match_int": ("", "match @Option<Nat>.0 { Some(@Int) -> @Int.0, None -> 0 }"),
        "match_nat": ("", "match @Option<Nat>.0 { Some(@Nat) -> nat_to_int(@Nat.0), None -> 0 }"),
    }, "Int", {"sign": _SIGN, "range_hi": _HI}, "0", "Some(@Int.0)"),
    "OptInt": ("Option<Int>", [], {
        "match_int": ("", "match @Option<Int>.0 { Some(@Int) -> @Int.0, None -> 0 }"),
    }, "Int", {"range_hi": _HI}, "0", "Some(@Int.0)"),
    "OptPos": ("Option<Pos>", ["Pos"], {
        "match_int": ("", "match @Option<Pos>.0 { Some(@Int) -> @Int.0, None -> 1 }"),
    }, "Int", {"pred": _POS}, "1", "Some(@Int.0)"),
    "TupNat": ("Tuple<Nat, Nat>", [], {
        "match_int": ("", "match @Tuple<Nat, Nat>.0 { Tuple(@Int, @Int) -> @Int.1 }"),
        "destr_int": ("let Tuple<@Int, @Int> = @Tuple<Nat, Nat>.0;", "@Int.1"),
        "destr_nat": ("let Tuple<@Nat, @Nat> = @Tuple<Nat, Nat>.0;", "nat_to_int(@Nat.1)"),
    }, "Int", {"sign": _SIGN, "range_hi": _HI}, "0", "Tuple(@Int.0, @Int.0)"),
    "BoxNat": ("Box<Nat>", ["Box"], {
        "match_int": ("", "match @Box<Nat>.0 { MkBox(@Int) -> @Int.0 }"),
        "destr_int": ("let MkBox<@Int> = @Box<Nat>.0;", "@Int.0"),
    }, "Int", {"sign": _SIGN}, "0", "MkBox(@Int.0)"),
    "NB": ("NB", ["NB"], {
        "match_int": ("", "match @NB.0 { MkNB(@Int) -> @Int.0 }"),
        "destr_int": ("let MkNB<@Int> = @NB.0;", "@Int.0"),
    }, "Int", {"sign": _SIGN}, "0", "MkNB(@Int.0)"),
    "NList": ("NList", ["NList"], {
        "head": ("", "match @NList.0 { NCons(@Int, @NList) -> @Int.0, NNil -> 0 }"),
        "second": ("", "match @NList.0 { NCons(@Int, @NList) -> match @NList.0 { NCons(@Int, @NList) -> @Int.0, NNil -> 0 }, NNil -> 0 }"),
    }, "Int", {"sign": _SIGN}, "0", "NCons(@Int.0, NCons(@Int.0, NNil))"),
    "ListNat": ("List<Nat>", ["List"], {
        "head": ("", "match @List<Nat>.0 { Cons(@Int, @List<Nat>) -> @Int.0, Nil -> 0 }"),
        "second": ("", "match @List<Nat>.0 { Cons(@Int, @List<Nat>) -> match @List<Nat>.0 { Cons(@Int, @List<Nat>) -> @Int.0, Nil -> 0 }, Nil -> 0 }"),
    }, "Int", {"sign": _SIGN}, "0", "Cons(@Int.0, Cons(@Int.0, Nil))"),
    "ArrNat": ("Array<Nat>", [], {
        "index": ("", "if array_length(@Array<Nat>.0) > 0 then { nat_to_int(@Array<Nat>.0[0]) } else { 0 }"),
    }, "Int", {"sign": _SIGN, "range_hi": _HI}, "0", "[@Int.0]"),
    "ArrInt": ("Array<Int>", [], {
        "index": ("", "if array_length(@Array<Int>.0) > 0 then { @Array<Int>.0[0] } else { 0 }"),
    }, "Int", {"range_hi": _HI}, "0", "[@Int.0]"),
    "NotRed": ("NotRed", ["Color", "NotRed"], {
        "direct": ("", "@NotRed.0 != Red"),
    }, "Bool", {"pred": "@Bool.result"}, "true",
        "if @Int.0 > 0 then { Green } else { Red }"),
}

_SOURCES = ("param", "call", "let_param", "let_call", "match", "destr",
            "index", "state")
_CALL_SOURCES = frozenset({"call", "let_call"})

#: The products that are no program: a `State` cell of an `Array` is refused
#: by code generation (`E340`), so the checker refuses it.
_NOT_CELLS = frozenset({
    ("ArrNat", "state"), ("ArrInt", "state"),
})

#: Cells outside this class, with the status they have and why.
_OUTSIDE = {
    # A `State` cell of a refined type: the `get` is a stand-in whose
    # refutation rests on it, tier3 at d202df53 as here.
    ("Pos", "state", "direct", "pred"): "tier3",
    ("NotRed", "state", "direct", "pred"): "tier3",
    # An array bound by a `match` binder: tier3 at d202df53 as here.
    ("ArrNat", "match", "index", "sign"): "tier3",
}


def _waits_for_call_result_facts(
        tname: str, source: str, reader: str, ob: str) -> bool:
    """A value from a call result that only the result's own type facts
    prove: those wait for #1925.  The facts a call result carried before
    (a `Nat` head's range, a `match` arm's direct binder) do not."""
    if source not in _CALL_SOURCES or tname == "Nat":
        return False
    if ob.startswith("range"):
        return True
    return reader.startswith("destr") or reader == "index"


def _body(source: str, te: str, stmts: str, expr: str, dflt: str) -> tuple[str, str]:
    reader = f"{stmts}\n  {expr}" if stmts else expr
    if source == "param":
        return te, reader
    if source == "call":
        return te, f"let @{te} = idv(@{te}.0);\n  {reader}"
    if source == "let_param":
        return te, f"let @{te} = @{te}.0;\n  {reader}"
    if source == "let_call":
        return te, f"let @{te} = idv(@{te}.0);\n  let @{te} = @{te}.0;\n  {reader}"
    if source == "match":
        return f"Option<{te}>", (
            f"match @Option<{te}>.0 {{ Some(@{te}) -> {{ {stmts} {expr} }}, None -> {dflt} }}")
    if source == "destr":
        return f"Tuple<{te}, Bool>", (
            f"let Tuple<@{te}, @Bool> = @Tuple<{te}, Bool>.0;\n  {reader}")
    if source == "index":
        return f"Array<{te}>", (
            f"if array_length(@Array<{te}>.0) > 0 then {{ let @{te} = @Array<{te}>.0[0]; {stmts} {expr} }} else {{ {dflt} }}")
    assert source == "state", source
    return te, (
        f"handle[State<{te}>](@{te} = @{te}.0) {{\n"
        f"    get(@Unit) -> {{ resume(@{te}.0) }},\n"
        f"    put(@{te}) -> {{ resume(()) }}\n"
        f"  }} in {{\n    let @{te} = get(());\n    {stmts} {expr}\n  }}")


def _producer(source: str, value: str) -> str:
    """A checked producer's argument for `f` at *source*, from `value`."""
    if source == "match":
        return f"Some({value})"
    if source == "destr":
        return f"Tuple({value}, true)"
    if source == "index":
        return f"[{value}]"
    return value


def _program(tname: str, source: str, reader: str, ob: str) -> str:
    te, decls, readers, rty, obs, dflt, value = _TYPES[tname]
    stmts, expr = readers[reader]
    ptype, body = _body(source, te, stmts, expr, dflt)
    parts = [_DECLS[d] for d in decls]
    parts.append(
        f"private fn idv(@{te} -> @{te})\n  requires(true)\n  ensures(true)\n"
        f"  effects(pure)\n{{\n  @{te}.0\n}}")
    parts.append(
        f"public fn f(@{ptype} -> @{rty})\n  requires(true)\n  ensures({obs[ob]})\n"
        f"  effects(pure)\n{{\n  {body}\n}}")
    parts.append(
        f"public fn drive(@Int -> @{rty})\n  requires(true)\n  ensures(true)\n"
        f"  effects(pure)\n{{\n  f({_producer(source, value)})\n}}")
    return "\n\n".join(parts) + "\n"


def _cells() -> list[tuple[str, str, str, str]]:
    out = []
    for tname, spec in _TYPES.items():
        readers, obs = spec[2], spec[4]
        for source, reader, ob in itertools.product(_SOURCES, readers, obs):
            if (tname, source) not in _NOT_CELLS:
                out.append((tname, source, reader, ob))
    return out


_CELLS = _cells()


def test_the_matrix_spans_every_product() -> None:
    products = sum(
        len(_SOURCES) * len(spec[2]) * len(spec[4]) for spec in _TYPES.values())
    not_cells = sum(
        len(_TYPES[t][2]) * len(_TYPES[t][4]) for t, _ in _NOT_CELLS)
    assert len(_CELLS) == products - not_cells == 229


def _marks(cell: tuple[str, str, str, str]) -> list[pytest.MarkDecorator]:
    if _waits_for_call_result_facts(*cell):
        return [pytest.mark.xfail(strict=True, reason=(
            "a call result's type facts wait for each obligation to be "
            "discharged at its own program point (#1925)"))]
    return []


def _ensures_status(verified: pipeline.Verified) -> str:
    (status,) = [o.status for o in verified.obligations
                 if o.fn_name == "f" and o.kind == "ensures"]
    return status


@pytest.mark.parametrize(
    "cell", [pytest.param(c, id=".".join(c), marks=_marks(c)) for c in _CELLS])
def test_what_a_type_states_proves_the_cell(
        cell: tuple[str, str, str, str]) -> None:
    verified = pipeline.verify(_program(*cell), file=FILE)
    assert verified.ran, [d.format() for d in verified.checked.errors]
    expected = _OUTSIDE.get(cell, "verified")
    assert _ensures_status(verified) == expected, [
        (o.kind, o.status, o.error_code, o.counterexample)
        for o in verified.obligations if o.fn_name == "f"]


#: Each obligation's tightest false neighbour: one value of the type fails
#: it, so no fact may prove it (the negative space of the matrix).
_TIGHT = {
    "sign": "@Int.result >= 1",
    "range_hi": f"@Int.result <= {INT_MAX - 1}",
    "range_lo": f"@Int.result >= {INT_MIN + 1}",
    "pred": None,  # per type below
}
_TIGHT_PRED = {"Pos": "@Int.result > 1", "OptPos": "@Int.result > 1",
               "NotRed": "!@Bool.result"}


@pytest.mark.parametrize(
    "cell", [pytest.param(c, id=".".join(c)) for c in _CELLS])
def test_no_fact_proves_a_false_neighbour(
        cell: tuple[str, str, str, str]) -> None:
    tname, source, reader, ob = cell
    tight = _TIGHT[ob] or _TIGHT_PRED[tname]
    true_ensures = _TYPES[tname][4][ob]
    program = _program(*cell).replace(
        f"ensures({true_ensures})", f"ensures({tight})", 1)
    verified = pipeline.verify(program, file=FILE)
    assert verified.ran, [d.format() for d in verified.checked.errors]
    assert _ensures_status(verified) != "verified"


_BOUNDARIES = (INT_MIN, -1, 0, 1, INT_MAX)


@pytest.mark.parametrize(
    "cell", [pytest.param(c, id=".".join(c)) for c in _CELLS])
def test_no_fact_is_false_at_a_boundary_value(
        cell: tuple[str, str, str, str]) -> None:
    """A producer builds the value from each i64 boundary value and `f` is
    run on it.  A value the type does not admit is stopped at the producer's
    check, or the producer's obligation is refused or disclosed by `vera
    verify` (the program is not one whose facts were established): `f`'s
    postcondition check fires on no other program."""
    source = _program(*cell)
    compiled = pipeline.compile(source, file=FILE)
    for x in _BOUNDARIES:
        ran = pipeline.run(compiled, "drive", [x])
        if ran.ok:
            continue
        assert isinstance(ran.trap, WasmTrapError), ran.trap
        if "Postcondition violation in f(" not in str(ran.trap):
            continue
        verified = pipeline.verify(source, file=FILE)
        unestablished = [
            (o.kind, o.status, o.error_code) for o in verified.obligations
            if o.fn_name == "drive"
            and o.status in ("violated", "tier3_unguarded")]
        assert unestablished, (x, str(ran.trap))


# =====================================================================
# The issue's lines as filed, red at d202df53
# =====================================================================


def _statuses(source: str) -> dict[str, list[tuple[str, str, str]]]:
    verified = pipeline.verify(source, file=FILE)
    assert verified.ran, [d.format() for d in verified.checked.errors]
    out: dict[str, list[tuple[str, str, str]]] = {}
    for o in verified.obligations:
        out.setdefault(o.fn_name, []).append((o.kind, o.status, o.error_code))
    return out


_TUPLE_DESTRUCTURES = """\
public fn tup_int(@Tuple<Nat, Nat> -> @Int)
  requires(true)
  ensures(@Int.result >= 0)
  effects(pure)
{
  let Tuple<@Int, @Int> = @Tuple<Nat, Nat>.0;
  @Int.0
}

public fn tup_nat(@Tuple<Nat, Nat> -> @Int)
  requires(true)
  ensures(@Int.result >= 0)
  effects(pure)
{
  let Tuple<@Nat, @Nat> = @Tuple<Nat, Nat>.0;
  nat_to_int(@Nat.0)
}
"""


def test_repro_1814_a_destructured_nat_component_carries_its_sign() -> None:
    """Lines 1 and 2: `E500` with `Tuple(2, -1)` at d202df53."""
    statuses = _statuses(_TUPLE_DESTRUCTURES)
    for fn in ("tup_int", "tup_nat"):
        assert ("ensures", "verified", "") in statuses[fn], statuses[fn]


_COLOR = """\
private data Color { Red, Green, Blue }

type NotRed = { @Color | @Color.0 != Red };

private fn code_e(@NotRed -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  1
}

public fn lit_red(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  code_e(Red)
}

public fn lit_green(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  code_e(Green)
}

public fn pinned_red(@Color -> @Int)
  requires(@Color.0 == Red)
  ensures(true)
  effects(pure)
{
  code_e(@Color.0)
}
"""


def test_repro_1814_a_data_types_refinement_is_decided_at_the_argument() -> None:
    """Line 3: each `refine_bind` was tier3 `E506` at d202df53, refuted or
    proved alike."""
    statuses = _statuses(_COLOR)
    assert ("refine_bind", "violated", "E505") in statuses["lit_red"]
    assert ("refine_bind", "violated", "E505") in statuses["pinned_red"]
    assert ("refine_bind", "verified", "") in statuses["lit_green"]


_M06 = """\
public fn f(@Array<Nat> -> @Int)
  requires(array_length(@Array<Nat>.0) > 0)
  ensures(@Int.result >= 0)
  effects(pure)
{
  nat_to_int(@Array<Nat>.0[0])
}
"""


def test_repro_1814_an_array_nat_element_carries_its_sign() -> None:
    """Line 4 (#1696's m06): `E500` with `[-1]` at d202df53."""
    assert ("ensures", "verified", "") in _statuses(_M06)["f"]


_RANGE = f"""\
public fn ident(@Int -> @Int)
  requires(true)
  ensures(@Int.result <= {INT_MAX})
  effects(pure)
{{
  @Int.0
}}

public fn add0(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{{
  @Int.0 + 0
}}

public fn mul1(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{{
  @Int.0 * 1
}}
"""


def test_repro_1814_an_int_carries_the_i64_range() -> None:
    """Line 5: `ident` `E500` with `@Int.0 = 2^63`, and the `int_overflow`
    rows of `+ 0` and `* 1` tier3, at d202df53."""
    statuses = _statuses(_RANGE)
    assert ("ensures", "verified", "") in statuses["ident"]
    assert ("int_overflow", "verified", "") in statuses["add0"]
    assert ("int_overflow", "verified", "") in statuses["mul1"]


_OUT_OF_RANGE = f"""\
public fn f(@Int -> @Int)
  requires(@Int.0 > {INT_MAX})
  ensures(true)
  effects(pure)
{{
  0
}}
"""


def test_a_requires_no_i64_satisfies_is_refused() -> None:
    """The Breaking case: a `requires` that admits only out-of-range values
    admits no argument (spec §6.8.2), `E538`."""
    verified = pipeline.verify(_OUT_OF_RANGE, file=FILE)
    assert "E538" in [d.error_code for d in verified.errors], [
        d.error_code for d in verified.diagnostics]


_NARROWED_RETURN = """\
public fn h2(@Tuple<Int, Int> -> @Tuple<Nat, Int>)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Tuple<Int, Int>.0
}
"""


def test_the_result_constant_proves_no_return_row() -> None:
    """No fact of the return type answers the return position's narrowing:
    it is asked of the body's value, and stays a runtime check."""
    statuses = _statuses(_NARROWED_RETURN)["h2"]
    narrowings = [status for kind, status, _ in statuses
                  if kind in ("nat_bind", "refine_bind")]
    assert narrowings, statuses
    assert all(status != "verified" for status in narrowings), statuses


#: An operation whose exact result a row asks to be in range, inside a
#: closure, where the operation's node is a stand-in: the stand-in carries
#: no range, or the row would be answered by its own goal.
_ARITHMETIC_IN_A_CLOSURE = {
    "add": "@Int.0 + @Int.1",
    "sub": "@Int.0 - @Int.1",
    "mul": "@Int.0 * @Int.1",
    "div": "@Int.0 / @Int.1",
    "neg": "-@Int.0",
    "abs": "abs(@Int.0)",
}


@pytest.mark.parametrize("op", list(_ARITHMETIC_IN_A_CLOSURE))
def test_an_arithmetic_stand_in_does_not_answer_its_own_row(op: str) -> None:
    source = (
        "type IntToInt = fn(Int -> Int) effects(pure);\n\n"
        "public fn make(@Int -> @IntToInt)\n  requires(true)\n  ensures(true)\n"
        "  effects(pure)\n{\n"
        f"  fn(@Int -> @Int) effects(pure) {{ {_ARITHMETIC_IN_A_CLOSURE[op]} }}\n}}\n")
    rows = [(o.kind, o.status) for o in pipeline.verify(source, file=FILE).obligations
            if o.kind == "int_overflow"]
    assert rows, "the operation has its row"
    assert all(status != "verified" for _, status in rows), rows


_EMPTY_PAYLOAD = """\
private data Color { Red, Green, Blue }

type NoColor = { @Color | @Color.0 != @Color.0 };

public fn f(@Option<NoColor> -> @Int)
  requires(true)
  ensures(@Int.result == 1)
  effects(pure)
{
  0
}
"""


def test_repro_a_payloads_fact_holds_only_under_its_constructor() -> None:
    """A fact of a constructor's field is stated under that constructor's
    recognizer.  `Option<NoColor>` has a value, `None`, though `NoColor` has
    none: stated of the `Some` accessor unconditionally, the empty predicate
    would make every parameter's context unsatisfiable and prove the false
    postcondition."""
    verified = pipeline.verify(_EMPTY_PAYLOAD, file=FILE)
    assert "E500" in [d.error_code for d in verified.errors], [
        (o.kind, o.status) for o in verified.obligations]


_SHARED_HELPER_ELEMENTS = """\
private fn ident_opt(@Option<Int> -> @Option<Int>)
  requires(true)
  ensures(@Option<Int>.result == @Option<Int>.0)
  effects(pure)
{
  @Option<Int>.0
}

type R = { @Option<Int> | ident_opt(@Option<Int>.0) == @Option<Int>.0 };

public fn f(@Array<R> -> @Bool)
  requires(array_length(@Array<R>.0) == 2)
  ensures(@Bool.result == true)
  effects(pure)
{
  @Array<R>.0[0] == @Array<R>.0[1]
}

public fn go(@Int -> @Bool)
  requires(true)
  ensures(true)
  effects(pure)
{
  f([Some(1), Some(2)])
}
"""


def test_repro_an_element_predicate_with_a_helper_is_not_shared() -> None:
    """A data type's element refinement whose predicate calls a helper is
    not stated under the index quantifier: the helper's result is one
    constant for the call, so every element would share it and `a[0] ==
    a[1]` would be proved, which `go` refutes at run time."""
    verified = pipeline.verify(_SHARED_HELPER_ELEMENTS, file=FILE)
    assert "E500" in [d.error_code for d in verified.errors], [
        (o.kind, o.status) for o in verified.obligations]
    ran = pipeline.run(pipeline.compile(_SHARED_HELPER_ELEMENTS, file=FILE),
                       "go", [0])
    assert not ran.ok, ran


_SHARED_HELPER_INT_ELEMENTS = """\
private fn ident(@Int -> @Int)
  requires(true)
  ensures(@Int.result == @Int.0)
  effects(pure)
{
  @Int.0
}

type R = { @Int | ident(@Int.0) == @Int.0 };

public fn f(@Array<R> -> @Bool)
  requires(array_length(@Array<R>.0) == 2)
  ensures(@Bool.result == true)
  effects(pure)
{
  @Array<R>.0[0] == @Array<R>.0[1]
}

public fn go(@Int -> @Bool)
  requires(true)
  ensures(true)
  effects(pure)
{
  f([1, 2])
}
"""


def test_repro_an_int_element_predicate_with_a_helper_is_not_shared() -> None:
    """#1929: the same rule over an `Int` element refinement, which
    `_element_facts` stated under the index quantifier: at 252ddf61 `vera
    verify` proved `a[0] == a[1]` (every fact Tier 1), and `go` fails `f`'s
    postcondition at run time."""
    verified = pipeline.verify(_SHARED_HELPER_INT_ELEMENTS, file=FILE)
    statuses = [(o.kind, o.status) for o in verified.obligations
                if o.fn_name == "f" and o.kind == "ensures"]
    assert statuses and all(s != "verified" for _, s in statuses), statuses
    ran = pipeline.run(pipeline.compile(_SHARED_HELPER_INT_ELEMENTS, file=FILE),
                       "go", [0])
    assert not ran.ok, ran


_SHARED_HELPER_NESTED = """\
private fn ident(@Int -> @Int)
  requires(true)
  ensures(@Int.result == @Int.0)
  effects(pure)
{
  @Int.0
}

type RI = { @Int | ident(@Int.0) == @Int.0 };

public fn f(@Array<Option<RI>> -> @Bool)
  requires(array_length(@Array<Option<RI>>.0) == 2)
  ensures(@Bool.result == true)
  effects(pure)
{
  match @Array<Option<RI>>.0[0] {
    Some(@Int) -> match @Array<Option<RI>>.0[1] {
      Some(@Int) -> @Int.0 == @Int.1,
      None -> true
    },
    None -> true
  }
}
"""


def test_repro_a_nested_element_predicate_with_a_helper_is_not_shared() -> None:
    """The rule one level down: an element's payload refinement that calls
    a helper is not stated under the quantifier, or every payload would be
    equal and the postcondition proved."""
    verified = pipeline.verify(_SHARED_HELPER_NESTED, file=FILE)
    assert "E500" in [d.error_code for d in verified.errors], [
        (o.kind, o.status) for o in verified.obligations]


_WITHHELD_NESTED_GOAL = """\
private fn pos(@Int -> @Int)
  requires(true)
  ensures(@Int.result == @Int.0)
  effects(pure)
{
  @Int.0
}

type RP = { @Int | pos(@Int.0) > 0 };

type RS = { @Option<RP> | true };

private fn take(@Array<RS> -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  1
}

public fn g(@Array<Option<Int>> -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  take(@Array<Option<Int>>.0)
}
"""


def test_a_withheld_element_fact_leaves_the_goal_unproved() -> None:
    """A goal whose element fact is withheld (a payload predicate calling a
    helper) is incomplete, so the narrowing of an arbitrary array into
    `Array<RS>` is not proved by the `true` that is left."""
    verified = pipeline.verify(_WITHHELD_NESTED_GOAL, file=FILE)
    rows = [o.status for o in verified.obligations
            if o.fn_name == "g" and o.kind == "refine_bind"]
    assert rows and "verified" not in rows, rows


_NO_BINDER = """\
private data Box { MkBox(Int) }

type Nope = { @Box | false };

type Always = { @Box | true };

private fn take_nope(@Nope -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  1
}

private fn take_always(@Always -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  1
}

public fn f(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  take_nope(MkBox(1)) + take_always(MkBox(2))
}
"""


def test_repro_a_data_types_predicate_that_reads_no_binder_is_decided() -> None:
    """`{ @Box | false }` and `{ @Box | true }` read no slot: each is decided
    as written at the argument, refused and proved."""
    verified = pipeline.verify(_NO_BINDER, file=FILE)
    rows = sorted((o.status, o.error_code) for o in verified.obligations
                  if o.fn_name == "f" and o.kind == "refine_bind")
    assert rows == [("verified", ""), ("violated", "E505")], rows


_EMPTY_ELEMENTS = """\
private data Color { Red, Green, Blue }

type NoColor = { @Color | @Color.0 != @Color.0 };

public fn f(@Array<NoColor> -> @Int)
  requires(true)
  ensures(@Int.result == 1)
  effects(pure)
{
  0
}
"""


def test_repro_an_elements_fact_holds_only_inside_the_array() -> None:
    """An element's fact is stated under the index bounds.  `Array<NoColor>`
    has a value, `[]`, though `NoColor` has none: stated at an index below 0,
    at the length or past it, the empty predicate would make the parameter's
    context unsatisfiable and prove the false postcondition."""
    verified = pipeline.verify(_EMPTY_ELEMENTS, file=FILE)
    assert "E500" in [d.error_code for d in verified.errors], [
        (o.kind, o.status) for o in verified.obligations]


def test_a_quotient_stand_in_carries_the_range() -> None:
    """A quotient's own row asks of its operands (`a == INT_MIN && b == -1`,
    #1598), never of the value the division leaves, so a division's stand-in
    carries the range that value always has: the `+ 0` over it is proved.
    The `div` cell above holds the quotient's own row a runtime check."""
    source = (
        "type IntToInt = fn(Int -> Int) effects(pure);\n\n"
        "public fn make(@Int -> @IntToInt)\n  requires(true)\n  ensures(true)\n"
        "  effects(pure)\n{\n"
        "  fn(@Int -> @Int) effects(pure) { (@Int.0 / 2) + 0 }\n}\n")
    rows = [(o.kind, o.status) for o in pipeline.verify(source, file=FILE).obligations
            if o.kind == "int_overflow"]
    assert rows == [("int_overflow", "verified")], rows


_MIN_QUOTIENT = """\
type IntToInt = fn(Int -> Int) effects(pure);

public fn make(@Int -> @IntToInt)
  requires(true)
  ensures(true)
  effects(pure)
{
  fn(@Int -> @Int) effects(pure) { @Int.0 / -1 }
}

public fn go(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  apply_fn(make(0), @Int.0)
}
"""


def test_a_quotient_stand_in_does_not_prove_its_own_row() -> None:
    """The other side of the quotient's stand-in: where `INT_MIN / -1` is
    reachable, the row is not proved by the range the stand-in carries, and
    the run at `INT_MIN` traps; at 6 it returns -6."""
    rows = [(o.kind, o.status) for o in pipeline.verify(
        _MIN_QUOTIENT, file=FILE).obligations if o.kind == "int_overflow"]
    assert rows and all(status != "verified" for _, status in rows), rows
    compiled = pipeline.compile(_MIN_QUOTIENT, file=FILE)
    ran = pipeline.run(compiled, "go", [INT_MIN])
    assert not ran.ok and isinstance(ran.trap, WasmTrapError), ran
    assert pipeline.run(compiled, "go", [6]).value == -6


def test_repro_a_level_that_does_not_translate_declines_the_membership() -> None:
    """`_translate_refined_predicate` answers None (Tier 3) for a level with
    no Bool term, at either level of a chain: a call the checker never typed
    (built after the check, so no stand-in stands for it) has no term, and
    the binder alone is a term of sort `Int`.  RED with the check reading
    `translated is None and …`: the first raises, the second is returned as
    the membership itself."""
    import z3

    from vera import ast
    from vera.smt import SmtContext
    from vera.types import INT, RefinedType
    from vera.verifier import ContractVerifier

    binder = ast.SlotRef(type_name="Int", type_args=None, index=0)
    positive = ast.BinaryExpr(op=ast.BinOp.GT, left=binder,
                              right=ast.IntLit(value=0))
    untyped = ast.BinaryExpr(
        op=ast.BinOp.GT, left=ast.FnCall(name="int_to_float", args=(binder,)),
        right=ast.FloatLit(value=0.0))
    translate = ContractVerifier._translate_refined_predicate
    smt = SmtContext()
    value = z3.Int("v")
    assert translate(smt, RefinedType(INT, positive), value) is not None
    for level in (untyped, binder):
        assert translate(smt, RefinedType(INT, level), value) is None, level
        chain = RefinedType(RefinedType(INT, positive), level)
        assert translate(smt, chain, value) is None, level


#: An element whose `Nat` sits two data types down, read by destructures
#: whose binders are `Int`: only the element quantifier states its sign.
_NESTED_ELEMENT = """\
private data Inner { MkInner(Nat) }

private data Outer { MkOuter(Inner) }

public fn f(@Array<Outer> -> @Int)
  requires(true)
  ensures(@Int.result >= 0)
  effects(pure)
{
  if array_length(@Array<Outer>.0) > 0 then { let MkOuter<@Inner> = @Array<Outer>.0[0]; let MkInner<@Int> = @Inner.0; @Int.0 } else { 0 }
}
"""


def test_repro_a_nat_two_data_types_down_an_element_carries_its_sign() -> None:
    """`_states_anything` walks `Outer`'s field into `Inner` with its own
    structural key.  RED with the key one constant for every type
    (`key = None`, `_type_key(None)`): `Inner` reads as already seen, the
    element states nothing and the ensures is `E500`; and with the fields
    walked under no `seen` set, which raises."""
    assert ("ensures", "verified", "") in _statuses(_NESTED_ELEMENT)["f"]


#: A recursive element type with nothing to state on the way round.
_RECURSIVE_ELEMENT = """\
private data BList { BCons(Bool, BList), BNil }

public fn f(@Array<BList> -> @Int)
  requires(true)
  ensures(@Int.result >= 0)
  effects(pure)
{
  if array_length(@Array<BList>.0) > 0 then { 1 } else { 0 }
}
"""


def test_repro_a_recursive_element_type_that_states_nothing_ends_the_walk() -> None:
    """`BList`'s second field is `BList`: the walk stops at a key it has
    seen.  RED with `seen & {key}` for `seen | {key}` (the set never
    grows): `RecursionError`."""
    assert ("ensures", "verified", "") in _statuses(_RECURSIVE_ELEMENT)["f"]


#: A generic element whose stated field is not its type parameter.
_GENERIC_ELEMENT = """\
private data Tag<T> { MkTag(T, Nat) }

public fn f(@Array<Tag<Bool>> -> @Int)
  requires(true)
  ensures(@Int.result >= 0)
  effects(pure)
{
  if array_length(@Array<Tag<Bool>>.0) > 0 then { let MkTag<@Bool, @Int> = @Array<Tag<Bool>>.0[0]; @Int.0 } else { 0 }
}
"""


def test_repro_a_generic_elements_own_nat_field_carries_its_sign() -> None:
    """`Tag<Bool>`'s type argument states nothing; its `Nat` field does, read
    at the instantiation.  RED with the fields read against no type
    (`_payload_field_types(ctor, None)`): a generic constructor's fields are
    then unreadable, the element states nothing, and the ensures is `E500`."""
    assert ("ensures", "verified", "") in _statuses(_GENERIC_ELEMENT)["f"]


#: A refinement over a data type with no field, as a nested array's element.
_NESTED_ARRAY_DATA_REFINEMENT = """\
private data Color { Red, Green, Blue }

type NotRed = { @Color | @Color.0 != Red };

public fn f(@Array<Array<NotRed>> -> @Bool)
  requires(true)
  ensures(@Bool.result)
  effects(pure)
{
  if array_length(@Array<Array<NotRed>>.0) > 0 then { if array_length(@Array<Array<NotRed>>.0[0]) > 0 then { @Array<Array<NotRed>>.0[0][0] != Red } else { true } } else { true }
}
"""


def test_repro_a_data_refinement_on_a_nested_arrays_element_is_stated() -> None:
    """`NotRed` is a refinement over `Color`, whose constructors carry no
    field: only the refinement itself makes the inner array's element worth
    a quantifier.  RED with that test never true (`chain is None and …`):
    the outer element states nothing, the inner element's refinement is
    never stated, and the ensures is Tier 3 (`E522`)."""
    assert ("ensures", "verified", "") in _statuses(
        _NESTED_ARRAY_DATA_REFINEMENT)["f"]


#: An element refinement read from a parameter and returned whole.
_ELEMENT_REFINEMENT_GOAL = """\
type PosInt = { @Int | @Int.0 > 0 };

public fn h(@Array<PosInt> -> @Int)
  requires(array_length(@Array<PosInt>.0) > 0)
  ensures(@Int.result > 0)
  effects(pure)
{
  @Array<PosInt>.0[0]
}

public fn r(@Array<PosInt> -> @Array<PosInt>)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Array<PosInt>.0
}
"""


def test_repro_an_element_refinement_is_a_complete_goal() -> None:
    """`PosInt`'s predicate is stated of every element, so `h`'s element is
    positive and `r`'s returned array narrows to `Array<PosInt>` in full.
    RED with the per-element test joined by `or` (every stated predicate
    withheld): `h`'s ensures is `E500` and `r`'s narrowing `E506`; and with
    the position's completeness lost (`complete = None`): `r`'s narrowing
    is Tier 3 (`E506`)."""
    rows = _statuses(_ELEMENT_REFINEMENT_GOAL)
    assert [s for _k, s, _c in rows["h"] + rows["r"]] == [
        "verified"] * len(rows["h"] + rows["r"]), rows


def test_repro_an_element_predicate_withheld_leaves_the_position_incomplete() -> None:
    """An element predicate that is not about the element alone (a helper's
    result is one constant shared by every element) is withheld, and the
    position is then reported incomplete: `([], False)`.  RED with the
    withheld branch reading `complete = True` (nothing stated, reported as
    fully stated) and `complete = None`.

    A direct call: no program was found whose verdict moves under those
    mutants.  Probed with `Array<R>` returned whole, `Array<Int>` narrowed
    to `Array<P>`, and a literal narrowed to `Array<P>`, each `R` and `P`
    calling a helper: every one stays `refine_bind` tier3 (`E506`) or
    violated (`E505`) at both trees, decided before this position's
    completeness is read."""
    from types import SimpleNamespace

    import z3

    from vera import ast
    from vera.types import INT, RefinedType
    from vera.verifier import ContractVerifier

    binder = ast.SlotRef(type_name="Int", type_args=None, index=0)
    positive = ast.BinaryExpr(op=ast.BinOp.GT, left=binder,
                              right=ast.IntLit(value=0))
    shared = z3.Int("helper_result")
    index = z3.Function("index_t", z3.IntSort(), z3.IntSort(), z3.IntSort())
    length = z3.Function("length_t", z3.IntSort(), z3.IntSort())
    sequence = z3.Int("s")
    smt = SimpleNamespace(carrier_elements=lambda term, projection, element:
                          (sequence, index, length, z3.IntSort()))
    verifier = object.__new__(ContractVerifier)
    verifier._fresh_quantifier_name = lambda base: f"{base}_0"  # type: ignore[method-assign]
    verifier._translate_refined_predicate = (  # type: ignore[method-assign]
        lambda smt, ty, term: shared > 0)
    verifier._nested_refinement_facts = (  # type: ignore[method-assign]
        lambda smt, ty, term, seen: ([], True))
    carrier = SimpleNamespace(projection=None,
                              element_type=RefinedType(INT, positive))
    facts, complete = verifier._element_facts(
        smt, carrier, sequence, frozenset())  # type: ignore[arg-type]
    assert facts == [] and complete is False, (facts, complete)


# =====================================================================
# A call guards the callee's facts with what the callee assumed (#1928)
# =====================================================================
#
# What a call imports of its callee is guarded by what the callee's own
# proof assumed of its parameters, over the argument's term: the same
# function (`ContractVerifier._parameter_premise`) at both ends.  With the
# guard short of the premise, a postcondition the callee proves from a
# parameter's range is a fact over the argument's term, and the argument's
# own `int_overflow` row was proved from it while the run traps.

#: shape: (the caller's value type, the parameter's type, declarations, the
#: callee's `ensures` restating the parameter's range, the argument from x)
_RESTATED = {
    "int": ("Int", "Int", "", f"@Int.0 <= {INT_MAX}", "{x} + 1"),
    "nat": ("Nat", "Nat", "", f"@Nat.0 <= {INT_MAX}", "{x} + 1"),
    "tuple": ("Int", "Tuple<Int, Int>", "",
              f"match @Tuple<Int, Int>.0 {{ Tuple(@Int, @Int) -> @Int.1 <= {INT_MAX} }}",
              "Tuple({x} + 1, 0)"),
    "option": ("Int", "Option<Int>", "",
               f"match @Option<Int>.0 {{ Some(@Int) -> @Int.0 <= {INT_MAX}, None -> true }}",
               "Some({x} + 1)"),
    "field": ("Int", "IB", "private data IB { MkIB(Int) }\n\n",
              f"match @IB.0 {{ MkIB(@Int) -> @Int.0 <= {INT_MAX} }}", "MkIB({x} + 1)"),
    "array": ("Int", "Array<Int>", "",
              f"array_length(@Array<Int>.0) > 0 ==> @Array<Int>.0[0] <= {INT_MAX}",
              "[{x} + 1]"),
    "int2": ("Int", "Option<Tuple<Int, Int>>", "",
             "match @Option<Tuple<Int, Int>>.0 { Some(@Tuple<Int, Int>) -> "
             f"match @Tuple<Int, Int>.0 {{ Tuple(@Int, @Int) -> @Int.1 <= {INT_MAX} }}, "
             "None -> true }",
             "Some(Tuple({x} + 1, 0))"),
    "nat2": ("Nat", "Option<Tuple<Nat, Nat>>", "",
             "match @Option<Tuple<Nat, Nat>>.0 { Some(@Tuple<Nat, Nat>) -> "
             f"match @Tuple<Nat, Nat>.0 {{ Tuple(@Nat, @Nat) -> @Nat.1 <= {INT_MAX} }}, "
             "None -> true }",
             "Some(Tuple({x} + 1, 0))"),
}
_RESTATED_DEFAULT = {"int": "0", "nat": "0", "tuple": "Tuple(0, 0)",
                     "option": "None", "field": "MkIB(0)", "array": "[]",
                     "int2": "None", "nat2": "None"}


def _fn(head: str, sig: str, ens: str, body: str, extra: str = "") -> str:
    return (f"{head} fn {sig}\n  requires(true)\n  ensures({ens})\n{extra}"
            f"  effects(pure)\n{{\n  {body}\n}}\n")


def _slot(params: list[str], i: int) -> str:
    """The slot reference to parameter *i* of *params* (De Bruijn)."""
    return f"@{params[i]}.{params[i + 1:].count(params[i])}"


def _reached(kind: str, x_te: str, te: str, decls: str, ens: str,
             arg: str, dflt: str) -> dict[str, str]:
    """A callee `c` (or `r`) whose `ensures` is *ens* over its `@te`
    parameter, reached from `k(@x_te)` the way *kind* names, with *arg*
    (`{x}` the caller's value) at the parameter: the program's files."""
    a = arg.format(x=f"@{x_te}.0")
    if kind == "direct":
        return {"p.vera": decls + _fn("private", f"c(@{te} -> @Int)", ens, "0")
                + "\n" + _fn("public", f"k(@{x_te} -> @Int)", "true", f"c({a})")}
    if kind == "module":
        return {
            "plib.vera": "module plib;\n\n"
            + decls.replace("private data", "public data")
            + _fn("public", f"c(@{te} -> @Int)", ens, "0"),
            # A type alias is the module's own (SKILL.md § visibility).
            "p.vera": "import plib;\n\n" + "".join(
                line + "\n\n" for line in decls.splitlines()
                if line.startswith("type "))
            + _fn("public", f"k(@{x_te} -> @Int)", "true", f"c({a})")}
    if kind == "generic":
        return {"p.vera": decls
                + _fn("private forall<A>", f"c(@A, @{te} -> @Int)", ens, "0")
                + "\n" + _fn("public", f"k(@{x_te} -> @Int)", "true",
                             f"c(true, {a})")}
    assert kind == "recursive", kind
    params = ["Nat", x_te, te]
    n, x = _slot(params, 0), _slot(params, 1)
    body = (f"if {n} > 0 then {{ r({n} - 1, {x}, {arg.format(x=x)}) }} "
            "else { 0 }")
    return {"p.vera": decls
            + _fn("private", f"r(@Nat, @{x_te}, @{te} -> @Int)", ens, body,
                  f"  decreases({n})\n")
            + "\n" + _fn("public", f"k(@{x_te} -> @Int)", "true",
                         f"r(1, @{x_te}.0, {dflt})")}


def _assert_the_argument_is_checked(
        tmp_path, files: dict[str, str]) -> None:  # type: ignore[no-untyped-def]
    """The argument's own `+ 1` rows stay Tier 3, as at main, and the run
    at `INT_MAX` traps on the overflow they check."""
    entry = pipeline.write_tree(tmp_path, files, "p.vera")
    verified = pipeline.verify(entry)
    assert verified.ran, [d.format() for d in verified.checked.errors]
    rows = [(o.fn_name, o.expr_text, o.status) for o in verified.obligations
            if o.kind == "int_overflow" and o.expr_text.endswith("+ 1")]
    assert rows and all(s == "tier3" for _f, _e, s in rows), rows
    ran = pipeline.run(entry, "k", [INT_MAX])
    assert isinstance(ran.trap, WasmTrapError), ran
    assert "overflow" in str(ran.trap).lower(), str(ran.trap)


def _restated(tmp_path, shape: str, kind: str) -> None:  # type: ignore[no-untyped-def]
    x_te, te, decls, ens, arg = _RESTATED[shape]
    _assert_the_argument_is_checked(tmp_path, _reached(
        kind, x_te, te, decls, ens, arg, _RESTATED_DEFAULT[shape]))


_INC = f"""\
private fn low(@Int -> @Int)
  requires(true)
  ensures(@Int.0 <= {INT_MAX})
  effects(pure)
{{
  @Int.0
}}

public fn inc(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{{
  low(@Int.0 + 1)
}}

private fn same(@Int -> @Int)
  requires(true)
  ensures(@Int.result == @Int.0 && @Int.result <= {INT_MAX})
  effects(pure)
{{
  @Int.0
}}

public fn inc2(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{{
  same(@Int.0 + 1)
}}
"""


def test_repro_1928_inc_and_inc2() -> None:
    """The issue's program: `low`'s and `same`'s postconditions hold of
    every `Int` (verified), and `inc`'s and `inc2`'s `@Int.0 + 1` rows were
    `verified` at cac60692 from them, while `inc(INT_MAX)` traps."""
    statuses = _statuses(_INC)
    assert ("ensures", "verified", "") in statuses["low"]
    assert ("ensures", "verified", "") in statuses["same"]
    for fn in ("inc", "inc2"):
        assert [s for k, s, _c in statuses[fn] if k == "int_overflow"] == [
            "tier3"], statuses[fn]
        ran = pipeline.run(_INC, fn, [INT_MAX], file=FILE)
        assert isinstance(ran.trap, WasmTrapError), ran
        assert "overflow" in str(ran.trap).lower(), str(ran.trap)


def test_repro_1928_int_direct(tmp_path) -> None:  # type: ignore[no-untyped-def]
    _restated(tmp_path, "int", "direct")


def test_repro_1928_int_module(tmp_path) -> None:  # type: ignore[no-untyped-def]
    _restated(tmp_path, "int", "module")


def test_repro_1928_int_recursive(tmp_path) -> None:  # type: ignore[no-untyped-def]
    _restated(tmp_path, "int", "recursive")


def test_repro_1928_nat_direct(tmp_path) -> None:  # type: ignore[no-untyped-def]
    """A `Nat`'s upper bound: a false proof at main too."""
    _restated(tmp_path, "nat", "direct")


def test_repro_1928_nat_module(tmp_path) -> None:  # type: ignore[no-untyped-def]
    _restated(tmp_path, "nat", "module")


def test_repro_1928_nat_recursive(tmp_path) -> None:  # type: ignore[no-untyped-def]
    _restated(tmp_path, "nat", "recursive")


def test_repro_1928_tuple_direct(tmp_path) -> None:  # type: ignore[no-untyped-def]
    _restated(tmp_path, "tuple", "direct")


def test_repro_1928_tuple_module(tmp_path) -> None:  # type: ignore[no-untyped-def]
    _restated(tmp_path, "tuple", "module")


def test_repro_1928_tuple_recursive(tmp_path) -> None:  # type: ignore[no-untyped-def]
    _restated(tmp_path, "tuple", "recursive")


def test_repro_1928_option_direct(tmp_path) -> None:  # type: ignore[no-untyped-def]
    _restated(tmp_path, "option", "direct")


def test_repro_1928_option_module(tmp_path) -> None:  # type: ignore[no-untyped-def]
    _restated(tmp_path, "option", "module")


def test_repro_1928_option_recursive(tmp_path) -> None:  # type: ignore[no-untyped-def]
    _restated(tmp_path, "option", "recursive")


def test_repro_1928_field_direct(tmp_path) -> None:  # type: ignore[no-untyped-def]
    _restated(tmp_path, "field", "direct")


def test_repro_1928_field_module(tmp_path) -> None:  # type: ignore[no-untyped-def]
    _restated(tmp_path, "field", "module")


def test_repro_1928_field_recursive(tmp_path) -> None:  # type: ignore[no-untyped-def]
    _restated(tmp_path, "field", "recursive")


def test_repro_1928_array_direct(tmp_path) -> None:  # type: ignore[no-untyped-def]
    _restated(tmp_path, "array", "direct")


def test_repro_1928_array_module(tmp_path) -> None:  # type: ignore[no-untyped-def]
    _restated(tmp_path, "array", "module")


def test_repro_1928_array_recursive(tmp_path) -> None:  # type: ignore[no-untyped-def]
    _restated(tmp_path, "array", "recursive")


def test_repro_1928_int_two_levels_down_direct(tmp_path) -> None:  # type: ignore[no-untyped-def]
    _restated(tmp_path, "int2", "direct")


def test_repro_1928_int_two_levels_down_module(tmp_path) -> None:  # type: ignore[no-untyped-def]
    _restated(tmp_path, "int2", "module")


def test_repro_1928_int_two_levels_down_recursive(tmp_path) -> None:  # type: ignore[no-untyped-def]
    _restated(tmp_path, "int2", "recursive")


def test_repro_1928_nat_two_levels_down_direct(tmp_path) -> None:  # type: ignore[no-untyped-def]
    """A false proof at main too."""
    _restated(tmp_path, "nat2", "direct")


def test_repro_1928_nat_two_levels_down_module(tmp_path) -> None:  # type: ignore[no-untyped-def]
    _restated(tmp_path, "nat2", "module")


def test_repro_1928_nat_two_levels_down_recursive(tmp_path) -> None:  # type: ignore[no-untyped-def]
    _restated(tmp_path, "nat2", "recursive")


#: The ways a callee's facts reach a caller.  A generic function's call
#: imports no postcondition (`E522`, at main as here), and a closure applied
#: through `apply_fn` carries no contract: neither imports anything.
_REACH = ("direct", "module", "recursive")

#: The matrix's types that state a range at some position (every one but
#: `NotRed`), each with its first reader that is one expression.
_RANGED = [t for t in _TYPES if t != "NotRed"]


def _reader(tname: str) -> str:
    readers = _TYPES[tname][2]
    (expr,) = [e for s, e in readers.values() if not s][:1]
    return expr


def _reach_cells() -> list[tuple[str, str]]:
    return list(itertools.product(_RANGED, _REACH))


_REACH_CELLS = _reach_cells()


def test_the_reach_dimension_spans_every_product() -> None:
    assert len(_REACH_CELLS) == len(_RANGED) * len(_REACH) == 39


# The range part of the guard, by the query's kind (#1928)
# --------------------------------------------------------
#
# An argument that reaches its call is a value, and a value is in range, so
# the range part of the callee's premise holds at the call by the
# argument's own evaluation: only a query asking whether arithmetic stays
# in range (an `int_overflow` row) requires it of the argument.  At
# e35cc91a every query required it, and a caller whose argument is a
# call's result (which states nothing) or arithmetic it cannot bound lost
# the callee's postcondition: five corpus programs refuted their `ensures`.

_FROM_A_CALL = """\
private fn larger(@Int, @Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  if @Int.1 > @Int.0 then { @Int.1 } else { @Int.0 }
}

private fn magnitude(@Int -> @Int)
  requires(true)
  ensures(@Int.result >= 0)
  effects(pure)
{
  if @Int.0 >= 0 then { @Int.0 } else { 0 }
}

public fn k(@Int, @Int -> @Int)
  requires(true)
  ensures(@Int.result >= 0)
  effects(pure)
{
  magnitude(larger(@Int.1, @Int.0))
}
"""

_FROM_ARITHMETIC = """\
private fn twice(@Int -> @Int)
  requires(true)
  ensures(@Int.result == @Int.0 * 2)
  effects(pure)
{
  @Int.0 * 2
}

public fn k(@Int -> @Int)
  requires(true)
  ensures(@Int.result == (@Int.0 + 1) * 2)
  effects(pure)
{
  twice(@Int.0 + 1)
}
"""


def test_repro_1928_an_argument_from_a_call_keeps_the_callee_ensures() -> None:
    """`magnitude(larger(..))`, reduced from `examples/modules.vera`: the
    argument is a call's result, whose range nothing states; `k`'s
    `ensures` needs `magnitude`'s, which holds of any argument.  Violated
    (E500) at e35cc91a, verified at main and here."""
    assert ("ensures", "verified", "") in _statuses(_FROM_A_CALL)["k"]


def test_repro_1928_an_unbounded_argument_keeps_the_callee_ensures() -> None:
    """`twice(@Int.0 + 1)`, reduced from `ch05_nested_where_helpers.vera`:
    the caller cannot bound the argument, and `twice`'s postcondition does
    not depend on the range.  Violated (E500) at e35cc91a, verified at main
    and here; the argument's own row stays Tier 3."""
    statuses = _statuses(_FROM_ARITHMETIC)["k"]
    assert ("ensures", "verified", "") in statuses, statuses
    assert all(s == "tier3" for kd, s, _c in statuses
               if kd == "int_overflow"), statuses


#: The argument at the call, over the caller's `@Int` parameter `{x}`.
_KIND_ARGUMENTS = {
    "parameter": "{x}",
    "literal": "5",
    "bounded": "{x} + 1",
    "unbounded": "{x} + 1",
    "call": "ident({x})",
}
#: Where the obligation sits: the argument's own row, an `int_overflow` row
#: over the same term earlier in the body, the caller's postcondition.
_KIND_OBLIGATIONS = ("own", "earlier", "ensures")
#: The callee's postcondition: one that does not depend on the parameter's
#: range, and one that restates it.
_KIND_CALLEES = {
    "doubles": "@Int.result == @Int.0 * 2",
    "restates": f"@Int.0 <= {INT_MAX}",
}
_KIND_CELLS = list(itertools.product(
    _KIND_ARGUMENTS, _KIND_OBLIGATIONS, _KIND_CALLEES))


def _kind_program(argument: str, obligation: str, callee: str) -> str:
    arg = _KIND_ARGUMENTS[argument]
    requires = "@Int.0 < 100" if argument == "bounded" else "true"
    ensures = "true"
    if obligation == "ensures" and callee == "doubles":
        # A contract's own `ident(..)` is a second call, whose result is
        # not the body's: what the import gives is the result's parity.
        ensures = ("@Int.result % 2 == 0" if argument == "call"
                   else f"@Int.result == ({arg.format(x='@Int.0')}) * 2")
    if obligation == "earlier":
        body = f"let @Int = @Int.0 + 1;\n  c({arg.format(x='@Int.1')})"
    else:
        body = f"c({arg.format(x='@Int.0')})"
    # `ident` states nothing of its result (#1925): its range is not shown.
    return (_fn("private", "ident(@Int -> @Int)", "true", "@Int.0") + "\n"
            + _fn("private", "c(@Int -> @Int)", _KIND_CALLEES[callee],
                  "@Int.0 * 2" if callee == "doubles" else "@Int.0") + "\n"
            + f"public fn k(@Int -> @Int)\n  requires({requires})\n"
            f"  ensures({ensures})\n  effects(pure)\n{{\n  {body}\n}}\n")


def test_the_kind_dimension_spans_every_product() -> None:
    assert len(_KIND_CELLS) == 5 * 3 * 2 == 30


@pytest.mark.parametrize(
    "cell", [pytest.param(c, id=".".join(c)) for c in _KIND_CELLS])
def test_a_call_guards_by_the_query_kind(cell: tuple[str, str, str]) -> None:
    """Argument x obligation x callee postcondition: an `int_overflow` row
    of `k` is never `verified` where the run at `INT_MAX` traps on an
    overflow, and `k`'s postcondition that reads the callee's result is
    `verified` wherever that callee's postcondition does not depend on the
    range."""
    argument, obligation, callee = cell
    source = _kind_program(argument, obligation, callee)
    verified = pipeline.verify(source, file=FILE)
    assert verified.ran, [d.format() for d in verified.checked.errors]
    rows = [(o.kind, o.expr_text, o.status) for o in verified.obligations
            if o.fn_name == "k"]
    overflow = [r for r in rows if r[0] == "int_overflow"]
    if argument == "bounded" and obligation != "earlier":
        # `@Int.0 < 100` bounds the argument's `+ 1` (a contract's own
        # `* 2` has no lower bound, and stays Tier 3).
        bounded = [s for _k, e, s in overflow if e == "@Int.0 + 1"]
        assert bounded and all(s == "verified" for s in bounded), rows
    ran = pipeline.run(source, "k", [INT_MAX], file=FILE)
    if ran.trap is not None and "overflow" in str(ran.trap).lower():
        # The callee's own `* 2` may be what traps; no row of `k` is proved.
        assert all(s != "verified" for *_r, s in overflow), rows
    if argument != "bounded" and (
            argument == "unbounded" or obligation == "earlier"):
        # The boundary is reached: the cell is one the first assertion
        # reads, not one it passes by running nothing.
        assert isinstance(ran.trap, WasmTrapError), (ran, rows)
        assert "overflow" in str(ran.trap).lower(), str(ran.trap)
    if obligation == "ensures" and callee == "doubles":
        assert ("ensures", "verified") in [(k, s) for k, _e, s in rows], rows


@pytest.mark.parametrize(
    "cell", [pytest.param(c, id=".".join(c)) for c in _REACH_CELLS])
def test_a_call_guards_what_the_callee_assumed(
        tmp_path, cell: tuple[str, str]) -> None:  # type: ignore[no-untyped-def]
    """(a) A callee whose `ensures` restates its parameter's range at the
    position the reader reads, and a caller whose argument holds `x + 1`
    there: the argument's own row is not proved from the import, and the
    run at `INT_MAX` traps on the check it keeps.  (b) A caller whose
    argument is a parameter of the type, in range by its own type, still
    proves a goal that needs the callee's postcondition after the call."""
    tname, kind = cell
    te, decls = _TYPES[tname][0], "".join(
        _DECLS[d] + "\n\n" for d in _TYPES[tname][1])
    restated = f"({_reader(tname)}) <= {INT_MAX}"
    value = _TYPES[tname][6]
    dflt = value.replace("@Int.0", "1")
    _assert_the_argument_is_checked(tmp_path / "a", _reached(
        kind, "Int", te, decls, restated,
        value.replace("@Int.0", "{x} + 1"), dflt))
    held = _reached(kind, te, te, decls, f"@Int.result == 0 && {restated}",
                    "{x}", dflt)
    held["p.vera"] = held["p.vera"].replace(
        f"k(@{te} -> @Int)\n  requires(true)\n  ensures(true)",
        f"k(@{te} -> @Int)\n  requires(true)\n  ensures(@Int.result == 0)")
    entry = pipeline.write_tree(tmp_path / "b", held, "p.vera")
    verified = pipeline.verify(entry)
    assert verified.ran, [d.format() for d in verified.checked.errors]
    assert [(o.fn_name, o.status) for o in verified.obligations
            if o.kind == "ensures"] == [
        (o.fn_name, "verified") for o in verified.obligations
        if o.kind == "ensures"], [
        (o.fn_name, o.kind, o.status, o.error_code)
        for o in verified.obligations]
