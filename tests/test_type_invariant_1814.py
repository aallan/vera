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

#: The traps a type's own check raises: a `Nat` slot's sign, a refinement's
#: predicate.
_TYPE_CHECK_TRAPS = ("Negative value bound into a @Nat slot",
                     "Refinement violation in ")


def _outside_the_type(tname: str, x: int) -> bool:
    """Whether the value the producer builds from *x* is one *tname* does
    not admit: an `Int` admits every boundary, a refinement `> 0` (and
    `NotRed`, `Red` for `x <= 0`) none at or below `0`, a `Nat` none below
    it."""
    if tname in ("Int", "OptInt", "ArrInt"):
        return False
    if tname in ("Pos", "OptPos", "NotRed"):
        return x <= 0
    return x < 0


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
            # Only a type's own check may stop the run, and only on a value
            # outside the type: any other trap fails the cell.
            assert (str(ran.trap).startswith(_TYPE_CHECK_TRAPS)
                    and _outside_the_type(cell[0], x)), (x, str(ran.trap))
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
    # Each goal is required by name, so a row that goes missing fails here
    # rather than shrinking the list above with it.
    assert ("ensures", "verified") in [(k, s) for k, s, _c in rows["h"]], rows
    assert ("refine_bind", "verified") in [(k, s) for k, s, _c in rows["r"]], rows


#: An element refinement over a helper with a postcondition, and a goal
#: about the elements that is false: the helper's `ensures`, asserted over
#: the index quantifier's free index, is satisfiable for some index, so it
#: proves nothing about the goal.
_HELPER_ELEMENT = """\
private fn big(@Int -> @Bool)
  requires(true)
  ensures(@Bool.result == (@Int.0 > 5))
  effects(pure)
{
  @Int.0 > 5
}

type R = { @Int | big(@Int.0) };

private fn f(@Array<R> -> @Bool)
  requires(%s)
  ensures(@Bool.result)
  effects(pure)
{
  %s
}
"""


def test_repro_a_helper_postcondition_proves_no_false_goal_of_an_empty_array() -> None:
    """`f([])` returns false: the goal is refused (`E500`), at 71b3d463 and
    at 08598810 alike."""
    rows = _statuses(_HELPER_ELEMENT % ("true", "array_length(@Array<R>.0) > 0"))
    assert ("ensures", "violated") in [(k, s) for k, s, _c in rows["f"]], rows


def test_repro_a_helper_postcondition_proves_no_false_goal_of_an_element() -> None:
    """`f([6])` returns false: an element above `5` need not be above
    `100`, and the goal is refused (`E500`), at 71b3d463 and at 08598810
    alike."""
    rows = _statuses(_HELPER_ELEMENT % (
        "array_length(@Array<R>.0) > 0", "@Array<R>.0[0] > 100"))
    assert ("ensures", "violated") in [(k, s) for k, s, _c in rows["f"]], rows


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


#: A caller `k` passing its own parameter on to `c` (#1928): (k's type,
#: c's, the entry's, the value the entry passes to k, the arithmetic on k's
#: parameter after the call).  The first three are the same premise on both
#: sides, which the guard omits as already held; the last two are a premise
#: of a different type, of which only what the caller holds is omitted.  An
#: `Int` passed to a `Nat` parameter is narrowed, so `k` requires it.
_PASSED_ON = {
    "int": ("Int", "Int", "Int", "@Int.0", "@Int.1 + 1"),
    "nat": ("Nat", "Nat", "Nat", "@Nat.0", "@Nat.0 + 1"),
    "array": ("Array<Int>", "Array<Int>", "Int", "[@Int.0]",
              "@Array<Int>.0[0] + 1"),
    "nat_to_int": ("Nat", "Int", "Nat", "@Nat.0", "@Nat.0 + 1"),
    "int_to_nat": ("Int", "Nat", "Int", "@Int.0", "@Int.1 + 1"),
}


def _passed_on_program(cell: str) -> str:
    caller, callee, entry, value, arith = _PASSED_ON[cell]
    read = ("array_length(@Array<Int>.0) < 1 || @Array<Int>.0[0]"
            if callee.startswith("Array") else f"@{callee}.0")
    requires = {"array": "array_length(@Array<Int>.0) > 0",
                "int_to_nat": "@Int.0 >= 0"}.get(cell, "true")
    return (_fn("private", f"c(@{callee} -> @Int)",
                f"{read} <= {INT_MAX} && @Int.result == 0", "0") + "\n"
            + f"private fn k(@{caller} -> @Int)\n  requires({requires})\n"
            f"  ensures(true)\n  effects(pure)\n{{\n"
            f"  let @Int = c(@{caller}.0);\n  {arith}\n}}\n\n"
            + _fn("public", f"entry(@{entry} -> @Int)", "true",
                  f"k({value})"))


@pytest.mark.parametrize("cell", list(_PASSED_ON))
def test_a_call_passing_its_own_parameter_on_omits_only_what_it_holds(
        cell: str) -> None:
    """The guard's part the caller already holds as a premise of its own
    is omitted (#1928): `k`'s `int_overflow` row over its own parameter is
    never `verified`, and the run at `INT_MAX` reaches it and traps on the
    overflow, whether the callee's parameter is of the caller's type or of
    another's."""
    source = _passed_on_program(cell)
    verified = pipeline.verify(source, file=FILE)
    assert verified.ran, [d.format() for d in verified.checked.errors]
    rows = [(o.kind, o.expr_text, o.status) for o in verified.obligations
            if o.fn_name == "k"]
    overflow = [s for kd, _e, s in rows if kd == "int_overflow"]
    assert overflow and all(s != "verified" for s in overflow), rows
    ran = pipeline.run(source, "entry", [INT_MAX], file=FILE)
    assert isinstance(ran.trap, WasmTrapError), (ran, rows)
    assert "overflow" in str(ran.trap).lower(), str(ran.trap)


def test_a_premise_held_is_omitted_up_to_its_bound_names() -> None:
    """The one test of "the same premise" (`_premise_held`): a fact the
    caller holds, the same quantifier under another bound name, and
    nothing else: not a fact over another term, not a quantifier of the
    other kind or over another sort."""
    import z3

    from vera.smt import SmtContext
    from vera.verifier import ContractVerifier

    x, y = z3.Int("x"), z3.Int("y")
    i, j = z3.Int("i"), z3.Int("j")
    a = z3.Array("a", z3.IntSort(), z3.IntSort())
    held = z3.ForAll([i], z3.Implies(i >= 0, a[i] >= 0))
    smt = SmtContext()
    smt.standing_premises = (x >= 0, held)
    same = ContractVerifier._premise_held
    assert same(smt, x >= 0)
    assert same(smt, z3.ForAll([j], z3.Implies(j >= 0, a[j] >= 0)))
    assert not same(smt, y >= 0)
    assert not same(smt, x > 0)
    assert not same(smt, z3.Exists([j], z3.Implies(j >= 0, a[j] >= 0)))
    assert not same(smt, z3.ForAll(
        [z3.Real("r")], z3.Implies(z3.Real("r") >= 0, a[0] >= 0)))
    smt.reset()
    assert not same(smt, x >= 0)


_CHAIN = "private data Chain {\n  End,\n  Link(Nat, Chain)\n}\n\n"

#: A recursion over a data type with a `Nat` field (#1928, the generator's
#: seed 173): the recursive call passes the tail, a component of `f`'s own
#: parameter, whose premise `f` holds at every depth.
_CHAIN_RECURSION = _CHAIN + """\
private fn f(@Chain -> @Int)
  requires(true)
  ensures(@Int.result >= 2)
  decreases(@Chain.0)
  effects(pure)
{
  match @Chain.0 {
    End -> 2,
    Link(@Nat, @Chain) -> @Nat.0 + f(@Chain.0)
  }
}
"""

#: The same, the tail reached through a second `match`.
_CHAIN_RECURSION_TWICE = _CHAIN + """\
private fn f(@Chain -> @Int)
  requires(true)
  ensures(@Int.result >= 2)
  decreases(@Chain.0)
  effects(pure)
{
  match @Chain.0 {
    End -> 2,
    Link(@Nat, @Chain) -> match @Chain.0 {
      End -> @Nat.0 + 2,
      Link(@Nat, @Chain) -> @Nat.1 + @Nat.0 + f(@Chain.0)
    }
  }
}
"""

#: The argument a call's result of the data type, which states nothing of
#: its fields (#1925).
_CHAIN_FROM_A_CALL = _CHAIN + """\
private fn rev(@Chain -> @Chain)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Chain.0
}

private fn total(@Chain -> @Int)
  requires(true)
  ensures(@Int.result >= 0)
  decreases(@Chain.0)
  effects(pure)
{
  match @Chain.0 {
    End -> 0,
    Link(@Nat, @Chain) -> @Nat.0 + total(@Chain.0)
  }
}

public fn k(@Chain -> @Int)
  requires(true)
  ensures(@Int.result >= 0)
  effects(pure)
{
  total(rev(@Chain.0))
}
"""


def test_repro_1928_a_recursion_over_a_nat_field_keeps_its_ensures() -> None:
    """The guard's nested `Nat` `>= 0` is not what every query requires,
    and the tail's premise is held: `f`'s `ensures` is `verified`
    (violated, E500, at 873a4e84)."""
    assert ("ensures", "verified", "") in _statuses(_CHAIN_RECURSION)["f"]


def test_repro_1928_a_tail_through_a_second_match_keeps_its_ensures() -> None:
    """The same, two accessors down the caller's parameter."""
    assert ("ensures", "verified", "") in _statuses(
        _CHAIN_RECURSION_TWICE)["f"]


def test_repro_1928_a_call_result_of_a_nat_field_type_keeps_the_ensures() -> None:
    """`total(rev(..))`: the argument is a call's result, of which nothing
    is held, and `total`'s `ensures` holds of any argument: `k`'s is
    `verified`, as at main."""
    statuses = _statuses(_CHAIN_FROM_A_CALL)
    assert ("ensures", "verified", "") in statuses["k"], statuses
    assert ("ensures", "verified", "") in statuses["total"], statuses


def _premise_of(monkeypatch, param: str, decls: str = ""):  # type: ignore[no-untyped-def]
    """The `ParameterPremise` `f(@<param>)`'s own proof builds of its
    parameter, through `ContractVerifier._parameter_premise`."""
    from vera.verifier import ContractVerifier

    seen: list[object] = []
    real = ContractVerifier._parameter_premise

    def spy(self, smt, ty, term, **kw):  # type: ignore[no-untyped-def]
        premise = real(self, smt, ty, term, **kw)
        if kw.get("standing", True) and str(term).startswith("@" + param.split("<")[0]):
            seen.append(premise)
        return premise

    monkeypatch.setattr(ContractVerifier, "_parameter_premise", spy)
    source = (decls + _fn("private", f"f(@{param} -> @Int)", "true", "0"))
    assert pipeline.verify(source, file=FILE).ran
    assert len(seen) == 1, seen
    return seen[0]


_NOT_RED = ("private data Color { Red, Green }\n\n"
            "type NotRed = { @Color | @Color.0 != Red };\n\n")


def test_a_data_type_refinement_inside_a_premise_is_required_by_every_query(
        monkeypatch) -> None:  # type: ignore[no-untyped-def]
    """A refinement over a data type at a position inside the type can have
    no check where it is constructed (E506), so a call's guard requires it
    of every query (#1928): in `range_free()`, not in `range_parts()`."""
    for param in ("Option<NotRed>", "Array<NotRed>"):
        premise = _premise_of(monkeypatch, param, _NOT_RED)
        free = {f.get_id() for f in premise.range_free()}
        assert premise.invariant, param
        assert all(f.get_id() in free for f in premise.invariant), param
        assert premise.range_parts() == [], (param, premise.range_parts())


def test_a_nat_inside_a_premise_is_a_range_part(
        monkeypatch) -> None:  # type: ignore[no-untyped-def]
    """The control: a `Nat`'s facts inside the type (its `>= 0` included)
    are what the type states by construction, range parts."""
    for param, decls in (("Option<Nat>", ""), ("Array<Nat>", ""),
                         ("Chain", _CHAIN)):
        premise = _premise_of(monkeypatch, param, decls)
        parts = {f.get_id() for f in premise.range_parts()}
        assert premise.invariant, param
        assert all(f.get_id() in parts for f in premise.invariant), param
        assert any(">= 0" in str(f) for f in premise.range_parts()), param


def _restating_program(depth: int) -> str:
    """`g` restates the `Nat` field *depth* levels into its parameter; `k`
    constructs the argument with that field narrowed from `@Int.0 - 1`."""
    read = "@Nat.0 >= 0"
    field = "Link(@Int.0 - 1, End)"
    for _ in range(depth - 1):
        read = (f"match @Chain.0 {{ End -> true, Link(@Nat, @Chain) -> "
                f"{read} }}")
        field = f"Link(5, {field})"
    ens = f"match @Chain.0 {{ End -> true, Link(@Nat, @Chain) -> {read} }}"
    return (_CHAIN + _fn("private", "g(@Chain -> @Int)", ens, "0") + "\n"
            + _fn("public", "k(@Int -> @Int)", "true", f"g({field})"))


@pytest.mark.parametrize("depth", [1, 2])
def test_a_nat_field_narrowed_into_a_call_is_not_proved_by_the_callee(
        depth: int) -> None:
    """The `Nat` rows require the whole premise (#1928): a callee whose
    postcondition restates its parameter's `Nat` field does not prove the
    narrowing of the field the caller constructs, which traps at 0."""
    source = _restating_program(depth)
    verified = pipeline.verify(source, file=FILE)
    assert verified.ran, [d.format() for d in verified.checked.errors]
    rows = [(o.kind, o.expr_text, o.status) for o in verified.obligations
            if o.fn_name == "k"]
    narrowed = [s for kd, e, s in rows
                if kd == "nat_bind" and e == "@Int.0 - 1"]
    assert narrowed and all(s != "verified" for s in narrowed), rows
    ran = pipeline.run(source, "k", [0], file=FILE)
    assert isinstance(ran.trap, WasmTrapError), (ran, rows)


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


# #1928, the stand-in rule: a value is established only when every row that
# produces it has a check.  A stand-in whose node holds a narrowing row with
# no check, or an operation call a handler clause holding one answers, states
# its base and its ranges alone (`SmtContext._inherit_disclosure`).

_HEAD_1928 = """\
private data Color { Red, Green, Blue }

type NotRed = { @Color | @Color.0 != Red };

type Pos = { @Int | @Int.0 > 0 };

type Wrap = { @Option<NotRed> | true };

"""


def _program_1928(pick_sig: str, pick_body: str, main_body: str) -> str:
    return (_HEAD_1928 + _fn("private", pick_sig, "true", pick_body) + "\n"
            + _fn("public", "main(@Unit -> @Bool)", "@Bool.result", main_body))


def _state_1928(ty: str, init: str, base: str, bad: str, reader: str) -> str:
    return _program_1928(
        f"pick(@{ty} -> @{base})", bad,
        f"let @{ty} = handle[State<{ty}>](@{ty} = {init}) {{\n"
        f"    get(@Unit) -> {{ resume(pick(@{ty}.0)) }},\n"
        f"    put(@{ty}) -> {{ resume(()) }}\n  }} in {{\n    get(())\n  }};\n"
        f"  {reader}")


def _closure_1928(ty: str, base: str, bad: str, reader: str) -> str:
    return _program_1928(
        f"pick2(@Unit -> @{base})", bad,
        f"let @{ty} = apply_fn(fn(@Unit -> @{ty}) effects(pure) "
        f"{{ pick2(()) }}, ());\n  {reader}")


_OPT_NOTRED_READER = ("match @Option<NotRed>.0 { Some(@Color) -> "
                      "@Color.0 != Red, None -> true }")
_OPT_POS_READER = "match @Option<Pos>.0 { Some(@Int) -> @Int.0 > 0, None -> true }"

_MEMBERS_1928 = {
    "f4c": _program_1928(
        "pick(@Wrap -> @Option<Color>)", "Some(Red)",
        "let @Wrap = handle[State<Wrap>](@Wrap = Some(Green)) {\n"
        "    get(@Unit) -> { resume(pick(@Wrap.0)) },\n"
        "    put(@Wrap) -> { resume(()) }\n  } in {\n    get(())\n  };\n"
        "  match @Wrap.0 { Some(@Color) -> @Color.0 != Red, None -> true }"),
    "s_opt_notred": _state_1928(
        "Option<NotRed>", "Some(Green)", "Option<Color>", "Some(Red)",
        _OPT_NOTRED_READER),
    "c_opt_notred": _closure_1928(
        "Option<NotRed>", "Option<Color>", "Some(Red)", _OPT_NOTRED_READER),
    "c_arr_notred": _closure_1928(
        "Array<NotRed>", "Array<Color>", "[Red]",
        "if array_length(@Array<NotRed>.0) > 0 then {\n"
        "    let @Color = @Array<NotRed>.0[0];\n    @Color.0 != Red\n"
        "  } else {\n    true\n  }"),
    "destr_opt_notred": _program_1928(
        "pick2(@Unit -> @Tuple<Option<Color>, Int>)", "Tuple(Some(Red), 1)",
        "let @Bool = {\n    let Tuple<@Option<NotRed>, @Int> = apply_fn("
        "fn(@Unit -> @Tuple<Option<NotRed>, Int>) effects(pure) "
        "{ pick2(()) }, ());\n    " + _OPT_NOTRED_READER + "\n  };\n"
        "  @Bool.0"),
    "s_opt_pos": _state_1928(
        "Option<Pos>", "Some(1)", "Option<Int>", "Some(0 - 5)",
        _OPT_POS_READER),
    "c_opt_pos": _closure_1928(
        "Option<Pos>", "Option<Int>", "Some(0 - 5)", _OPT_POS_READER),
    # The controls: the producer's own row has a check, which traps first.
    "s_opt_nat": _state_1928(
        "Option<Nat>", "Some(1)", "Option<Int>", "Some(0 - 5)",
        "match @Option<Nat>.0 { Some(@Int) -> @Int.0 >= 0, None -> true }"),
    "c_tup_notred": _closure_1928(
        "Tuple<NotRed, Int>", "Tuple<Color, Int>", "Tuple(Red, 1)",
        "match @Tuple<NotRed, Int>.0 { Tuple(@Color, @Int) -> "
        "@Color.0 != Red }"),
}


def _reader_1928(source: str) -> tuple[str, str]:
    """`main`'s `ensures`: its status and code."""
    verified = pipeline.verify(source, file=FILE)
    assert verified.ran, [d.format() for d in verified.checked.errors]
    (found,) = [(o.status, o.error_code) for o in verified.obligations
                if o.fn_name == "main" and o.kind == "ensures"]
    return found


def _assert_unestablished_1928(name: str) -> None:
    """The reader's `ensures` is not proved over a value whose producing
    row has no check (`verified` at e35cc91a), and the run that violates
    it does not return normally."""
    source = _MEMBERS_1928[name]
    assert _reader_1928(source)[0] != "verified", name
    ran = pipeline.run(source, "main", file=FILE)
    assert ran.trap is not None, ran
    assert "postcondition" in str(ran.trap).lower(), str(ran.trap)


def test_repro_1928_f4c_base_only_handle() -> None:
    _assert_unestablished_1928("f4c")


def test_repro_1928_s_opt_notred_state_get() -> None:
    _assert_unestablished_1928("s_opt_notred")


def test_repro_1928_c_opt_notred_closure_payload() -> None:
    _assert_unestablished_1928("c_opt_notred")


def test_repro_1928_c_arr_notred_closure_element() -> None:
    _assert_unestablished_1928("c_arr_notred")


def test_repro_1928_destr_opt_notred_destructure() -> None:
    _assert_unestablished_1928("destr_opt_notred")


def test_repro_1928_s_opt_pos_state_get_primitive() -> None:
    """Main's member too: a refinement over `Int` at a payload."""
    _assert_unestablished_1928("s_opt_pos")


def test_repro_1928_c_opt_pos_closure_primitive() -> None:
    _assert_unestablished_1928("c_opt_pos")


def test_repro_1928_controls_whose_row_is_checked_stay_verified() -> None:
    """A producer row with a check: the reader stays `verified`, and the
    run traps at the producer's own check, before the reader."""
    for name in ("s_opt_nat", "c_tup_notred"):
        source = _MEMBERS_1928[name]
        assert _reader_1928(source) == ("verified", ""), name
        ran = pipeline.run(source, "main", file=FILE)
        assert ran.trap is not None, (name, ran)
        assert "postcondition" not in str(ran.trap).lower(), str(ran.trap)


# The instrument's dimension for #1928: producer x position below the head x
# refinement x the producer's row.  A row with no check that is refuted or
# undecided ("unchecked": the producer builds a violating value) must leave
# its reader unproved beside a run that does not return normally; a row
# with a check, or one whose value the solver proves ("proved": the producer
# builds a satisfying literal), leaves the reader as it was at e35cc91a
# (`_BASE_1928`, generated by a run of this generator at that head).

_REFINEMENTS_1928 = {
    # name: (base, violating value, satisfying value, predicate over {x})
    "Pos": ("Int", "0 - 5", "1", "{x} > 0"),
    "NotRed": ("Color", "Red", "Green", "{x} != Red"),
}
_POSITIONS_1928 = ("option", "array", "tuple")
_PRODUCERS_1928 = ("state_get", "closure", "base_handle", "destructure")
_ROWS_1928 = ("unchecked", "proved", "checked")


def _position_1928(position: str, ref: str) -> tuple[str, str, str, str]:
    """The value's type, its base's, a value built from `{v}`, and the
    reader of the refined position over the value at `{s}`."""
    base, _bad, _good, pred = _REFINEMENTS_1928[ref]
    if position == "option":
        return (f"Option<{ref}>", f"Option<{base}>", "Some({v})",
                f"match {{s}} {{{{ Some(@{base}) -> "
                + pred.format(x=f"@{base}.0") + ", None -> true }}")
    if position == "array":
        return (f"Array<{ref}>", f"Array<{base}>", "[{v}]",
                "if array_length({s}) > 0 then {{ "
                f"let @{base} = {{s}}[0]; " + pred.format(x=f"@{base}.0")
                + " }} else {{ true }}")
    assert position == "tuple", position
    first = f"@{base}.1" if base == "Int" else f"@{base}.0"
    return (f"Tuple<{ref}, Int>", f"Tuple<{base}, Int>", "Tuple({v}, 1)",
            f"match {{s}} {{{{ Tuple(@{base}, @Int) -> "
            + pred.format(x=first) + " }}")


def _cell_1928(producer: str, position: str, ref: str, row: str) -> str:
    _base, bad, good, _pred = _REFINEMENTS_1928[ref]
    ty, base_ty, build, reader = _position_1928(position, ref)
    value = "pick2(())" if row != "proved" else build.format(v=good)
    pick_ret, pick_body = base_ty, build.format(v=bad)
    extra = ""
    if producer == "base_handle":
        extra = f"type W = {{ @{ty} | true }};\n\n"
        ty = "W"
    if producer == "destructure":
        pick_ret = f"Tuple<{base_ty}, Int>"
        pick_body = f"Tuple({pick_body}, 1)"
        if row == "proved":
            value = f"Tuple({value}, 1)"
        body = (f"let @Bool = {{\n    let Tuple<@{ty}, @Int> = apply_fn("
                f"fn(@Unit -> @Tuple<{ty}, Int>) effects(pure) {{ {value} }}"
                f", ());\n    {reader.format(s=f'@{ty}.0')}\n  }};\n  @Bool.0")
    elif producer == "closure":
        body = (f"let @{ty} = apply_fn(fn(@Unit -> @{ty}) effects(pure) "
                f"{{ {value} }}, ());\n  {reader.format(s=f'@{ty}.0')}")
    else:
        body = (f"let @{ty} = handle[State<{ty}>](@{ty} = "
                f"{build.format(v=good)}) {{\n"
                f"    get(@Unit) -> {{ resume({value}) }},\n"
                f"    put(@{ty}) -> {{ resume(()) }}\n  }} in {{\n"
                f"    get(())\n  }};\n  {reader.format(s=f'@{ty}.0')}")
    return (_HEAD_1928 + extra
            + _fn("private", f"pick2(@Unit -> @{pick_ret})", "true", pick_body)
            + "\n" + _fn("public", "main(@Unit -> @Bool)", "@Bool.result",
                         body))


_CELLS_1928 = list(itertools.product(
    _PRODUCERS_1928, _POSITIONS_1928, _REFINEMENTS_1928, _ROWS_1928))


def test_the_stand_in_dimension_spans_every_product() -> None:
    assert len(_CELLS_1928) == 4 * 3 * 2 * 3 == 72


#: The reader of each `proved` and `checked` cell at e35cc91a, (status,
#: code), generated by a run of `_cell_1928` at that head.
_BASE_1928 = {
    "state_get.option.Pos.proved": ("verified", ""),
    "state_get.option.Pos.checked": ("verified", ""),
    "state_get.option.NotRed.proved": ("verified", ""),
    "state_get.option.NotRed.checked": ("verified", ""),
    "state_get.tuple.Pos.proved": ("verified", ""),
    "state_get.tuple.Pos.checked": ("verified", ""),
    "state_get.tuple.NotRed.proved": ("verified", ""),
    "state_get.tuple.NotRed.checked": ("verified", ""),
    "closure.option.Pos.proved": ("verified", ""),
    "closure.option.Pos.checked": ("verified", ""),
    "closure.option.NotRed.proved": ("verified", ""),
    "closure.option.NotRed.checked": ("verified", ""),
    "closure.array.Pos.proved": ("tier3", "E522"),
    "closure.array.Pos.checked": ("tier3", "E522"),
    "closure.array.NotRed.proved": ("verified", ""),
    "closure.array.NotRed.checked": ("verified", ""),
    "closure.tuple.Pos.proved": ("verified", ""),
    "closure.tuple.Pos.checked": ("verified", ""),
    "closure.tuple.NotRed.proved": ("verified", ""),
    "closure.tuple.NotRed.checked": ("verified", ""),
    "base_handle.option.Pos.proved": ("verified", ""),
    "base_handle.option.Pos.checked": ("verified", ""),
    "base_handle.option.NotRed.proved": ("verified", ""),
    "base_handle.option.NotRed.checked": ("verified", ""),
    "base_handle.tuple.Pos.proved": ("verified", ""),
    "base_handle.tuple.Pos.checked": ("verified", ""),
    "base_handle.tuple.NotRed.proved": ("verified", ""),
    "base_handle.tuple.NotRed.checked": ("verified", ""),
    "destructure.option.Pos.proved": ("verified", ""),
    "destructure.option.Pos.checked": ("verified", ""),
    "destructure.option.NotRed.proved": ("verified", ""),
    "destructure.option.NotRed.checked": ("verified", ""),
    "destructure.array.Pos.proved": ("tier3", "E522"),
    "destructure.array.Pos.checked": ("tier3", "E522"),
    "destructure.array.NotRed.proved": ("verified", ""),
    "destructure.array.NotRed.checked": ("verified", ""),
    "destructure.tuple.Pos.proved": ("verified", ""),
    "destructure.tuple.Pos.checked": ("verified", ""),
    "destructure.tuple.NotRed.proved": ("verified", ""),
    "destructure.tuple.NotRed.checked": ("verified", ""),
}

#: The cells whose reader the rule moves from Tier 1 (measured): a producer
#: row with no check whose value the solver proves (`Green` into `NotRed`:
#: "a construction store guards only a scalar-based refinement") discloses
#: as a refuted one does, its status being settled after the stand-in that
#: asks is made.  `base_handle.tuple.NotRed.checked` is the same row: the
#: handler's initial state `Tuple(Green, 1)` is under the handle's node.
_LOST_1928: frozenset[str] = frozenset({
    "state_get.option.NotRed.proved",
    "state_get.tuple.NotRed.proved",
    "closure.option.NotRed.proved",
    "closure.array.NotRed.proved",
    "closure.tuple.NotRed.proved",
    "base_handle.option.NotRed.proved",
    "base_handle.tuple.NotRed.proved",
    "base_handle.tuple.NotRed.checked",
    "destructure.option.NotRed.proved",
    "destructure.array.NotRed.proved",
    "destructure.tuple.NotRed.proved",
})


def _producer_row_checked_1928(source: str) -> bool | None:
    """Whether every narrowing row at the producer's `pick2(())` call has a
    check; None where the program states none there."""
    from vera.obligations import table as obligation_table
    rows = [r for r in obligation_table.build(
        pipeline.typed(source, file=FILE)).rows
        if r.kind in ("refine_bind", "nat_bind")
        and getattr(r.node, "name", None) == "pick2"]
    return all(r.guard.check for r in rows) if rows else None


def _cell_param_1928(cell: tuple[str, ...]) -> object:
    cid = ".".join(cell)
    marks = ([pytest.mark.xfail(strict=True, reason=(
        "#1928: a producer row with no check that the solver proves "
        "discloses; its proof is settled after the stand-in is made"))]
        if cid in _LOST_1928 else [])
    return pytest.param(cell, id=cid, marks=marks)


@pytest.mark.parametrize("cell", [_cell_param_1928(c) for c in _CELLS_1928])
def test_a_stand_in_holds_what_every_producing_row_checks(
        cell: tuple[str, str, str, str]) -> None:
    """(a) Where the producer's row has no check and its value violates the
    refinement, the reader's `ensures` is not `verified`, and the run does
    not return normally.  (b) Where the row has a check, or the value is a
    satisfying literal, the reader is what it was at e35cc91a."""
    cid = ".".join(cell)
    source = _cell_1928(*cell)
    verified = pipeline.verify(source, file=FILE)
    if not verified.ran:
        pytest.skip("refused: " + ",".join(sorted(
            {d.error_code for d in verified.checked.errors})))
    (reader,) = [(o.status, o.error_code) for o in verified.obligations
                 if o.fn_name == "main" and o.kind == "ensures"]
    row = cell[3]
    if row != "proved":
        checked = _producer_row_checked_1928(source)
        assert checked is not None, cid
        if checked != (row == "checked"):
            pytest.skip(("the producer's row has a check here"
                         if checked else "E506: no check at this position")
                         + f" (the {'checked' if checked else 'unchecked'}"
                         " cell is the program)")
    if row == "unchecked":
        assert reader[0] != "verified", (cid, reader)
        ran = pipeline.run(source, "main", file=FILE)
        assert not ran.ok, (cid, ran)
        return
    assert reader == _BASE_1928[cid], (cid, reader)


_TWO_HANDLERS_1928 = _state_1928(
    "Option<NotRed>", "None", "Option<Color>", "Some(Red)",
    _OPT_NOTRED_READER).replace(
        "resume(pick(@Option<NotRed>.0))", "resume(@Option<NotRed>.0)") + """
public fn other(@Unit -> @Bool)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Option<NotRed> = handle[State<Option<NotRed>>](@Option<NotRed> = None) {
    get(@Unit) -> { resume(pick(@Option<NotRed>.0)) },
    put(@Option<NotRed>) -> { resume(()) }
  } in {
    get(())
  };
  true
}
"""


def test_1928_an_operation_is_disclosed_by_its_own_handler() -> None:
    """`main`'s `get` is answered by its own handler, whose clause resumes
    the state it holds; `other`'s handler, whose clause resumes a value with
    no check, answers no call of `main`'s, and leaves its reader proved."""
    verified = pipeline.verify(_TWO_HANDLERS_1928, file=FILE)
    assert verified.ran, [d.format() for d in verified.checked.errors]
    statuses = {(o.fn_name, o.kind, o.status, o.error_code)
                for o in verified.obligations}
    assert ("main", "ensures", "verified", "") in statuses, statuses
    assert ("other", "refine_bind", "tier3_unguarded", "E506") in statuses
