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
    """The function's own result carries its type's facts on the goal side
    only: the return position's narrowing is asked of the body's value, and
    stays a runtime check."""
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
