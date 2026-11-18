"""No value has the checker's unknown type with no diagnostic behind it
(#1862).

An index into an array whose element type no element, argument or
expected type fixes has no type: the checker gave it its unknown type and
reported nothing, so `vera check` accepted the program, code generation
dropped the enclosing function (`E602`) and `vera run` refused it
(`E907`).  The index is refused at check (E164), with a fix that names the
type to write: the array bound at its type first, or the index read where
a type is expected; for an `Array` written with no type argument, the type
argument.  `old()` and `new()` of an effect with no state were the other
silent route (`old(IO)` checked, and `vera verify` stopped at `E699`); they
are refused at check (E189, spec §7.9.2).

With every route to an unreported `Unknown` refused, a `match` or a
destructuring `let` over a value typed `Unknown` is never judged: a
diagnostic always stands behind it, so `_unknown_is_reported` and the
E313 an `Unknown` scrutinee drew are gone.

The class: every route by which a value of the checker's unknown type
exists with no diagnostic behind it.  The instrument:

* the matrix, position the index stands in (a `let`, an argument, a
  return, an array element, a `Tuple` component, a `match` scrutinee, a
  destructuring `let`, an `if` branch, an operand, an interpolation, a
  discarded statement) × what leaves its element type unfixed (an empty
  literal, an empty literal read from an index, an `Array` written with no
  type argument) × whether the position's type reaches the index itself or
  a generic call that leaves it to the index (`idg(..)`).  Each cell is
  refused with E164 alone and its fix, applied, checks and compiles with no
  function dropped, or (a position whose type reaches the index) checks and
  compiles as it is;
* the census: over the corpus and the documents' blocks, no expression is
  typed `Unknown` while no error is reported and no typed hole stands
  inside it.
"""

from __future__ import annotations

import importlib.util
import re
from pathlib import Path

import pytest

from tests import pipeline
from vera import ast, fold
from vera.checker.core import TypeChecker
from vera.types import UnknownType, base_type

pytestmark = pytest.mark.matrix(decides=[
    "vera/checker/control.py",
    "vera/checker/expressions.py",
])

ROOT = Path(__file__).resolve().parents[1]

_SIG = "  requires(true)\n  ensures(true)\n  effects(pure)\n"

_IDG = f"private forall<T> fn idg(@T -> @T)\n{_SIG}{{\n  @T.0\n}}\n\n"


def _fn(name: str, params: str, ret: str, body: str, *,
        visibility: str = "public", effects: str = "pure") -> str:
    indented = "\n".join(f"  {line}" if line else line
                         for line in body.splitlines())
    return (f"{visibility} fn {name}({params} -> @{ret})\n"
            f"  requires(true)\n  ensures(true)\n"
            f"  effects({effects})\n{{\n{indented}\n}}\n")


def _main(ret: str, body: str) -> str:
    return _fn("main", "@Unit", ret, body)


def _errors(source: str) -> list:
    return list(pipeline.check(source).errors)


def _codes(source: str) -> list[str]:
    return [e.error_code for e in _errors(source)]


def _all_codes(source: str) -> list[str]:
    return [d.error_code for d in pipeline.check(source).diagnostics]


def _dropped(source: str) -> list[str]:
    """The compile diagnostics that drop a function (E602, E620)."""
    compiled = pipeline.compile(source)
    assert compiled.result is not None, [
        e.format() for e in compiled.front.errors]
    return [d.error_code for d in compiled.result.diagnostics
            if d.error_code in ("E602", "E620")]


@pytest.fixture(autouse=True)
def _no_program_draws_an_internal_error_from_check(
        monkeypatch: pytest.MonkeyPatch) -> None:
    """The property behind every cell of this file: no program it checks,
    compiles or runs draws an internal compiler error (E699) from check.
    Each check goes through `pipeline.check`, which `pipeline.compile`
    calls too, so one assertion here covers the whole instrument."""
    original = pipeline.check

    def checked(*args: object, **kwargs: object) -> object:
        result = original(*args, **kwargs)  # type: ignore[arg-type]
        assert "E699" not in [d.error_code for d in result.diagnostics], [
            d.format() for d in result.diagnostics if d.error_code == "E699"]
        return result

    monkeypatch.setattr(pipeline, "check", checked)


# ---------------------------------------------------------------------
# The issue's program and the two forms of 12 November
# ---------------------------------------------------------------------

_ISSUE = (
    "public fn main(@Unit -> @Unit)\n"
    "  requires(true)\n  ensures(true)\n  effects(<IO>)\n{\n"
    "  match [][0] {\n"
    '    _ -> IO.print("matched")\n'
    "  }\n}\n")


def test_repro_the_issue_s_match_over_an_empty_literal_s_index() -> None:
    """At base: `vera check` OK, `vera verify` E602, `vera run` E907.  Now
    the index is refused, once, and the `match` over it is not judged (no
    E313)."""
    assert _codes(_ISSUE) == ["E164"]


def test_repro_an_untyped_index_as_an_element_at_a_typed_binding() -> None:
    """`let @Array<Int> = [[][0]];`: the binding's type reaches the array
    literal and not the index (12 November)."""
    assert _codes(_main("Int", "let @Array<Int> = [[][0]];\n"
                               "nat_to_int(array_length(@Array<Int>.0))")) == [
        "E164"]


def test_repro_an_untyped_index_as_a_tuple_component_at_a_typed_binding(
) -> None:
    """`let @Tuple<Int, Int> = Tuple([][0], 1);` (12 November)."""
    assert _codes(_main("Int", "let @Tuple<Int, Int> = Tuple([][0], 1);\n0")
                  ) == ["E164"]


_PICK_FIRST = (f"private forall<T> fn pick_first(@T, @T -> @T)\n{_SIG}"
               f"{{\n  @T.1\n}}\n\n")

_E164_LITERAL_FIX = (
    "Give the array its element type: bind it at its type first, "
    "`let @Array<Int> = [];`, and index the binding, `@Array<Int>.0[0]`; or "
    "index it where a type is expected, as in `let @Int = [][0];`.  Write "
    "the element type the program means in place of `Int`.")


@pytest.mark.parametrize(("helpers", "call"), [
    (_IDG, "idg([][0])"),
    (_PICK_FIRST, "pick_first([][0], 5)"),
    (_IDG, "idg(idg([][0]))"),
], ids=["argument", "argument_beside_one_that_fixes_the_variable",
        "argument_of_a_nested_generic_call"])
def test_repro_an_untyped_index_as_a_generic_call_s_argument(
        helpers: str, call: str) -> None:
    """A generic call's argument is typed on its own before the call's
    variable is fixed, by the binding or by another argument, so the type
    does not reach the index: at base `vera check` passed and code
    generation dropped `main` (`E602`, then `vera run` `E907`).  Refused at
    check with the literal's fix, which, applied, checks and keeps `main`.
    Carrying the instantiated parameter type back to the argument is issue
    #1812's mechanism."""
    source = helpers + _main("Int", f"let @Int = {call};\n@Int.0")
    error, = _errors(source)
    assert error.error_code == "E164"
    assert error.fix == _E164_LITERAL_FIX
    fixed = helpers + _main(
        "Int", "let @Array<Int> = [];\n"
               f"let @Int = {call.replace('[][0]', '@Array<Int>.0[0]')};\n"
               "@Int.0")
    assert _codes(fixed) == []
    assert _dropped(fixed) == []


#: Where the type a position expects reaches an index written there (spec
#: §4.12.2's first group): each checks and compiles with no function
#: dropped.  The positions that type the index on their own first are the
#: matrix's refused cells and the repros above.
_CARRIERS = {
    "typed_let": "let @Int = [][0];\n@Int.0",
    "return": "[][0]",
    "typed_if_branch": "if true then {\n  [][0]\n} else {\n  1\n}",
    "non_generic_function_argument": "abs([][0])",
    "generic_constructor_at_its_type": "let @Option<Int> = Some([][0]);\n1",
}


@pytest.mark.parametrize("body", list(_CARRIERS.values()), ids=list(_CARRIERS))
def test_the_positions_whose_type_reaches_the_index(body: str) -> None:
    source = _main("Int", body)
    assert _codes(source) == [], body
    assert _dropped(source) == [], body


def test_repro_an_untyped_index_as_a_non_generic_constructor_s_argument(
) -> None:
    """`Box([][0])` with `Box` a constructor of a data type with no type
    parameters: its field's type does not reach the argument, as a generic
    constructor's does where its own type is expected.  Dropped at base
    (`E602`), refused at check now."""
    source = ("private data Box {\n  Box(Int)\n}\n\n"
              + _main("Int", "let @Box = Box([][0]);\n1"))
    assert _codes(source) == ["E164"]


def test_repro_an_index_into_an_array_written_with_no_type_argument() -> None:
    """`@Array.0[0]` over a parameter written `@Array`: checked clean at
    base and its function dropped.  The index is refused; the type
    accepted with no argument is issue #1732's."""
    assert _codes(_fn("f", "@Array", "Int",
                      "match @Array.0[0] {\n  _ -> 1\n}",
                      visibility="private")) == ["E164"]


def test_e164_reads_as_written() -> None:
    """The whole diagnostic, for the empty literal and the bare type."""
    error, = _errors(_ISSUE)
    assert error.description == (
        "The element type of [] is not known, so the index [][0] has no "
        "type.")
    assert error.fix == (
        "Give the array its element type: bind it at its type first, "
        "`let @Array<Int> = [];`, and index the binding, "
        "`@Array<Int>.0[0]`; or index it where a type is expected, as in "
        "`let @Int = [][0];`.  Write the element type the program means in "
        "place of `Int`.")
    assert error.spec_ref == 'Chapter 4, Section 4.12.2 "Array Indexing"'
    assert error.rationale.startswith("An array's element type is fixed by")
    assert error.rationale == (
        "An array's element type is fixed by its elements, by an argument, "
        "or by the type the array or its index is expected at.  Here "
        "nothing fixes it, so the indexed value has no type and no "
        "representation to compile to.")
    # The collection and the index are written as the program writes them,
    # an index other than 0 included.
    at_two, = _errors(_main("Int", "match [][2] {\n  _ -> 1\n}"))
    assert at_two.description == (
        "The element type of [] is not known, so the index [][2] has no "
        "type.")
    assert "`@Array<Int>.0[2]`" in at_two.fix
    bare, = _errors(_fn("f", "@Array", "Int", "@Array.0[0]",
                        visibility="private"))
    assert bare.description == (
        "The element type of @Array.0 is not known, so the index "
        "@Array.0[0] has no type.")
    assert bare.fix == (
        "Write the array's element type where its type is written: "
        "`@Array<Int>` in place of `@Array`, with the element type the "
        "program means in place of `Int`.")


def test_repro_the_typed_neighbours_check_and_keep_their_function() -> None:
    """The same index where a type is expected of it, or of an array bound
    at its type first, checks and compiles with no function dropped."""
    for body in ("let @Int = [][0];\n@Int.0",
                 "let @Array<Int> = [];\n"
                 "let @Array<Int> = [@Array<Int>.0[0]];\n0",
                 "let @Array<Int> = [];\n"
                 "let @Tuple<Int, Int> = Tuple(@Array<Int>.0[0], 1);\n0",
                 "let @Array<Int> = [];\n"
                 "match @Array<Int>.0[0] {\n  _ -> 1\n}"):
        source = _main("Int", body)
        assert _codes(source) == [], body
        assert _dropped(source) == [], body


# ---------------------------------------------------------------------
# A variable a generic call leaves open is not the unknown type
# ---------------------------------------------------------------------

#: A generic function whose variable no argument names: a call leaves it
#: open in the call's type (spec §5.9), and code generation builds the call
#: at the phantom type `Bool` (§11.4.1).
_EMPTY = f"private forall<T> fn empty(@Unit -> @Array<T>)\n{_SIG}{{\n  []\n}}\n\n"


@pytest.mark.parametrize("body", [
    "match empty(())[0] {\n  _ -> 1\n}",
    "empty(())[0];\n1",
    "match [empty(())[0]][0] {\n  _ -> 1\n}",
], ids=["match", "discard", "element_of_an_untyped_literal"])
def test_repro_an_index_into_a_generic_call_s_open_array_is_specified(
        body: str) -> None:
    """`empty(())[0]` is an index into an array that holds nothing, its
    element type the variable the call leaves open: it checks, draws no
    E164, compiles at the phantom instance `empty$Bool`, and traps on the
    bounds check where it is evaluated (spec §4.12.2, §11.4.1)."""
    source = _EMPTY + _main("Int", body)
    assert _all_codes(source) == []
    compiled = pipeline.compile(source)
    assert compiled.result is not None
    assert "$:empty$Bool " in compiled.result.wat
    assert _dropped(source) == []
    ran = pipeline.run(compiled)
    assert ran.trap is not None
    assert "out of bounds" in str(ran.trap), str(ran.trap)


def test_repro_an_operand_over_a_generic_call_s_open_index_is_e140() -> None:
    """`empty(())[0] + 1`: `+` over the open variable is E140, not E164."""
    assert _codes(_EMPTY + _main("Int", "empty(())[0] + 1")) == ["E140"]


def test_repro_a_type_the_index_stands_at_fixes_the_call_s_variable() -> None:
    """An element or a component of a typed binding, or a generic call's
    argument at a typed binding, fixes the variable (#1684): the call is
    built at that type, not at the phantom."""
    for body in ("let @Array<Int> = [empty(())[0]];\n0",
                 "let @Tuple<Int, Int> = Tuple(empty(())[0], 1);\n0",
                 "let @Int = idg(empty(())[0]);\n@Int.0"):
        source = _IDG + _EMPTY + _main("Int", body)
        assert _codes(source) == [], body
        compiled = pipeline.compile(source)
        assert compiled.result is not None
        assert "$:empty$Int " in compiled.result.wat, body
        assert "$:empty$Bool" not in compiled.result.wat, body


def test_repro_a_destructure_of_an_open_variable_after_an_error() -> None:
    """A destructuring `let` over a value its own variable leaves open is
    judged (E313) where no error stands, and not after one: the error read
    before the bindings is what left it open (#1671)."""
    body = "let Tuple<@Int, @Int> = empty(())[0];\n@Int.0"
    assert _codes(_EMPTY + _main("Int", body)) == ["E313"]
    after = (_EMPTY + "private fn g(@Array<Nope> -> @Int)\n" + _SIG + "{\n"
             + "".join(f"  {line}\n" for line in body.splitlines()) + "}\n")
    assert _codes(after) == ["E136"]


@pytest.mark.xfail(strict=True, reason=(
    "#1812: an empty literal handed to a built-in is typed by synthesis "
    "alone, so `array_reverse([])[0]`'s element is a hole variable code "
    "generation cannot build, and it drops `main` (E602)"))
def test_an_index_into_a_built_in_over_an_empty_literal_compiles() -> None:
    source = _main("Int", "match array_reverse([])[0] {\n  _ -> 1\n}")
    assert _all_codes(source) == []
    assert _dropped(source) == []


# ---------------------------------------------------------------------
# What stands behind the index: an error elsewhere, a hole inside it
# ---------------------------------------------------------------------

def test_repro_an_index_into_a_hole_s_literal_draws_the_hole_alone() -> None:
    """`[?][0]`: the hole's W001 stands behind the unknown element type, so
    the index draws nothing beside it, and the `match` over it nothing."""
    source = _main("Int", "match [?][0] {\n  1 -> 1\n}")
    assert _all_codes(source) == ["W001"]


def test_repro_a_match_over_a_hole_s_operand_draws_the_hole_alone() -> None:
    """`match ? + 1 { 1 -> 1 }` drew W001 and E313 at base: the `match`
    over a value typed `Unknown` was judged unless the value was the hole
    itself.  A diagnostic stands behind every `Unknown`, so it is never
    judged, and the hole's W001 is the one diagnostic."""
    source = _main("Int", "match ? + 1 {\n  1 -> 1\n}")
    assert _all_codes(source) == ["W001"]


def test_repro_a_destructure_of_a_hole_s_operand_draws_the_hole_alone(
) -> None:
    """`let Tuple<@Int, @Int> = ? + 1;` drew W001 and E313 at base, as the
    `match` did: a value typed `Unknown` is not judged."""
    source = _main("Int", "let Tuple<@Int, @Int> = ? + 1;\n@Int.0")
    assert _all_codes(source) == ["W001"]
    # Nor is its head held to the value: a constructor of the wrong arity
    # or a name nothing declares draws nothing beside the hole (E321 and
    # E320 would restate what the hole leaves open).
    for head in ("Some<@Int, @Int>", "Nope<@Int>"):
        source = _main("Int", f"let {head} = ? + 1;\n0")
        assert _all_codes(source) == ["W001"], head


def test_repro_a_position_typed_unknown_inside_a_scrutinee_is_not_judged(
) -> None:
    """`Tuple([?][0], 1)`: the component the hole's literal leaves
    `Unknown` is not judged, so the arm draws no E311 beside the hole's
    W001."""
    source = _main("Int", "match Tuple([?][0], 1) {\n  Tuple(1, _) -> 1\n}")
    assert _all_codes(source) == ["W001"]


def test_repro_an_index_after_an_error_is_not_refused_again() -> None:
    """An `Array<Nope>` element is unknown after E136, its own error: the
    index draws no E164 beside it."""
    source = _fn("f", "@Array<Nope>", "Int",
                 "match @Array<Nope>.0[0] {\n  _ -> 1\n}",
                 visibility="private")
    assert set(_codes(source)) == {"E136"}


# ---------------------------------------------------------------------
# old() and new() of an effect with no state (E189, spec §7.9.2)
# ---------------------------------------------------------------------

def _ensures(clause: str, effects: str) -> str:
    return (f"public fn f(@Int -> @Int)\n  requires(true)\n"
            f"  ensures({clause})\n  effects({effects})\n{{\n  @Int.0\n}}\n")


def test_repro_old_of_io_is_refused() -> None:
    """`old(IO)` checked at base, and `vera verify` stopped at E699."""
    source = _ensures("old(IO) == old(IO)", "<IO>")
    assert _codes(source) == ["E189", "E189"]


def test_repro_new_of_an_exception_effect_is_refused() -> None:
    source = _ensures("new(Exn<Int>) == new(Exn<Int>)", "<Exn<Int>>")
    assert _codes(source) == ["E189", "E189"]


def test_repro_old_of_a_state_cell_still_checks() -> None:
    source = _ensures("old(State<Int>) == new(State<Int>)", "<State<Int>>")
    assert _codes(source) == []
    assert _dropped(source) == []


def test_e189_reads_as_written_and_its_fix_clears_it() -> None:
    """Each fix, applied as it says, checks clean: with a State cell in the
    row the form names it; with none, the form names one and the row
    declares it."""
    with_cell = _ensures("old(IO) == 0", "<IO, State<Bool>>")
    error, = _errors(with_cell)
    assert error.description == (
        "old(IO) names an effect with no state: old() reads a State cell.")
    assert error.fix == (
        "Name the State cell the postcondition means: `old(State<Bool>)` in "
        "place of `old(IO)`.")
    assert error.spec_ref == (
        'Chapter 7, Section 7.9.2 "State in Contracts"')
    applied = with_cell.replace("old(IO) == 0", "old(State<Bool>) == true")
    assert _codes(applied) == []

    without = _ensures("new(Exn<Int>) == 0", "<Exn<Int>>")
    error, = _errors(without)
    assert error.fix == (
        "Name a State cell, `new(State<Int>)` in place of `new(Exn<Int>)`, "
        "and declare it in the function's effects row, "
        "`effects(<State<Int>>)`, with the cell's type in place of `Int`.")
    applied = without.replace("new(Exn<Int>)", "new(State<Int>)").replace(
        "effects(<Exn<Int>>)", "effects(<Exn<Int>, State<Int>>)")
    assert _codes(applied) == []


def test_e189_writes_an_effect_s_type_arguments_as_the_row_does() -> None:
    """An effect and a cell of two type arguments each, written in the
    message and the fix as the row writes them."""
    source = ("effect Pair<A, B> {\n  op both(A, B -> Unit);\n}\n\n"
              + _ensures("old(Pair<Int, Bool>) == 0",
                         "<Pair<Int, Bool>, State<Tuple<Int, Bool>>>"))
    error, = [e for e in _errors(source) if e.error_code == "E189"]
    assert error.description == (
        "old(Pair<Int, Bool>) names an effect with no state: old() reads a "
        "State cell.")
    assert error.fix == (
        "Name the State cell the postcondition means: "
        "`old(State<Tuple<Int, Bool>>)` in place of `old(Pair<Int, Bool>)`.")


def test_e189_names_the_first_state_cell_as_the_row_writes_it() -> None:
    """With two `State` cells in the row the fix names the first by its
    written form, `State<Bool>` before `State<Int>`, whatever order the
    row's set holds them in."""
    for row in ("<IO, State<Int>, State<Bool>>", "<IO, State<Bool>, State<Int>>"):
        error, = _errors(_ensures("old(IO) == 0", row))
        assert error.fix == (
            "Name the State cell the postcondition means: `old(State<Bool>)` "
            "in place of `old(IO)`."), row


_POSITIVE = "type Positive = { @Int | @Int.0 > 0 };\n\n"


def test_repro_e189_names_a_refinement_alias_cell_as_the_row_writes_it(
) -> None:
    """A cell whose type is a refinement alias is written by the alias,
    `old(State<Positive>)`, which pastes and checks; the resolved type's
    rendering, `State<{@Int | ...}>`, elides the predicate and does not
    parse."""
    source = _POSITIVE + _ensures("old(IO) == 1", "<IO, State<Positive>>")
    error, = _errors(source)
    assert error.fix == (
        "Name the State cell the postcondition means: "
        "`old(State<Positive>)` in place of `old(IO)`.")
    assert _codes(source.replace("old(IO)", "old(State<Positive>)")) == []


def test_repro_e189_names_an_inline_refinement_cell_as_the_row_writes_it(
) -> None:
    """A refinement written in the row is written whole, in canonical
    form."""
    source = _ensures("new(IO) == 1", "<IO, State<{ @Int | @Int.0 > 0 }>>")
    error, = _errors(source)
    assert error.fix == (
        "Name the State cell the postcondition means: "
        "`new(State<{ @Int | @Int.0 > 0 }>)` in place of `new(IO)`.")
    assert _codes(source.replace(
        "new(IO)", "new(State<{ @Int | @Int.0 > 0 }>)")) == []


def test_repro_e189_names_an_alias_of_a_composite_cell_by_the_alias() -> None:
    """An alias of a composite type is written by the alias, as the row
    writes it, not by the type it stands for."""
    source = ("type MaybeInt = Option<Int>;\n\n"
              + _ensures("old(IO) == None", "<IO, State<MaybeInt>>"))
    error, = _errors(source)
    assert error.fix == (
        "Name the State cell the postcondition means: "
        "`old(State<MaybeInt>)` in place of `old(IO)`.")
    assert _codes(source.replace("old(IO)", "old(State<MaybeInt>)")) == []


#: Each kind of State cell a row can declare: the declarations it needs and
#: the cell as the row writes it.  Every cell type has `Eq`, so the clause
#: `form(cell) == form(cell)` checks once the cell is named.
_CELL_KINDS: dict[str, tuple[str, str]] = {
    "plain": ("", "State<Int>"),
    "alias": ("type Deg = Float64;\n\n", "State<Deg>"),
    "refinement_alias": (_POSITIVE, "State<Positive>"),
    "alias_of_a_composite": ("type MaybeInt = Option<Int>;\n\n",
                             "State<MaybeInt>"),
    "composite": ("", "State<Option<Int>>"),
    "refinement_comparison": ("", "State<{ @Int | @Int.0 > 0 }>"),
    "refinement_conjunction": (
        "", "State<{ @Int | @Int.0 > 0 && @Int.0 < 10 }>"),
    "refinement_if": (
        "", "State<{ @Int | if @Int.0 > 0 then { true } else { false } }>"),
    "refinement_match_arm_block": (
        "", "State<{ @Int | match @Int.0 {\n    0 -> { true },\n"
            "    _ -> false\n  } }>"),
    "refinement_match_arm_bare": (
        "", "State<{ @Int | match @Int.0 {\n    0 -> true,\n"
            "    _ -> false\n  } }>"),
    "refinement_nested_in_a_composite": (
        "", "State<Option<{ @Int | @Int.0 > 0 }>>"),
}


@pytest.mark.parametrize("form", ["old", "new"])
@pytest.mark.parametrize("kind", list(_CELL_KINDS))
def test_repro_e189_s_proposed_cell_reads_back_as_the_row_s_cell(
        kind: str, form: str) -> None:
    """The property behind E189's fix: the `old(...)` or `new(...)` it
    proposes, pasted in place of the form, checks clean, so it names the
    row's own cell (the row declares one State cell, and naming any other
    is E177).  Round 2 wrote the cell in canonical form, which drops a match
    arm's redundant block, `0 -> { true }` read back as `0 -> true`, a
    different cell."""
    decls, cell = _CELL_KINDS[kind]
    source = decls + _ensures(f"{form}(IO) == {form}(IO)", f"<IO, {cell}>")
    errors = _errors(source)
    assert [e.error_code for e in errors] == ["E189", "E189"]
    proposed = re.search(r"`(\w+\(State<.*\))` in place of", errors[0].fix,
                         re.DOTALL)
    assert proposed is not None, errors[0].fix
    assert proposed.group(1).startswith(f"{form}(State<")
    pasted = source.replace(f"{form}(IO)", proposed.group(1))
    assert _all_codes(pasted) == [], (kind, proposed.group(1))


def test_repro_e189_in_a_where_helper_names_the_helper_s_own_cell() -> None:
    """In a `where` helper the cell is the helper's row's, not its
    parent's."""
    source = (
        "public fn f(@Int -> @Int)\n  requires(true)\n  ensures(true)\n"
        "  effects(<IO, State<Int>>)\n{\n  g(@Int.0)\n}\nwhere {\n"
        "  fn g(@Int -> @Int)\n    requires(true)\n"
        "    ensures(old(IO) == true)\n    effects(<IO, State<Bool>>)\n"
        "  {\n    @Int.0\n  }\n}\n")
    error, = [e for e in _errors(source) if e.error_code == "E189"]
    assert error.fix == (
        "Name the State cell the postcondition means: `old(State<Bool>)` in "
        "place of `old(IO)`.")


def test_repro_e189_writes_the_named_effect_as_the_form_writes_it() -> None:
    """The effect the form names is written as the form writes it, a
    refinement alias by its name, in the message and the fix."""
    source = _POSITIVE + _ensures("old(Exn<Positive>) == 1",
                                  "<Exn<Positive>, State<Int>>")
    error, = _errors(source)
    assert error.description == (
        "old(Exn<Positive>) names an effect with no state: old() reads a "
        "State cell.")
    assert error.fix == (
        "Name the State cell the postcondition means: `old(State<Int>)` in "
        "place of `old(Exn<Positive>)`.")
    assert error.rationale.endswith(
        "Exn<Positive> holds no state, so there is no value for the form to "
        "name.")


@pytest.mark.parametrize(("form", "when"), [("old", "before"),
                                            ("new", "after")])
def test_repro_e189_s_rationale_reads_as_written(form: str, when: str) -> None:
    error, = _errors(_ensures(f"{form}(IO) == 0", "<IO>"))
    assert error.rationale == (
        f"{form}() refers to the value of a State effect's cell {when} the "
        f"call.  IO holds no state, so there is no value for the form to "
        f"name.")


@pytest.mark.parametrize("form", ["old", "new"])
def test_repro_a_state_cell_the_row_does_not_declare_keeps_e177_as_written(
        form: str) -> None:
    """A `State` cell is not refused by E189: the row's E177 reads it,
    naming the form it was written in."""
    error, = _errors(_ensures(f"{form}(State<Int>) == 0", "pure"))
    assert error.error_code == "E177"
    assert error.description == (
        f"{form}(State<Int>) names an effect this function does not "
        f"declare. Declared: pure.")


def test_a_name_no_effect_declares_keeps_the_row_s_e177() -> None:
    """`old(Qze)`, a name no effect declares: the row's E177 is the error
    behind it, and no E189 says it has no state."""
    assert _codes(_ensures("old(Qze) == 0", "pure")) == ["E177"]


def test_e189_stands_in_place_of_the_row_s_e177() -> None:
    """An effect with no state the row does not declare is refused once,
    E189: the form names no cell whether the row declares it or not."""
    assert _codes(_ensures("old(IO) == 0", "pure")) == ["E189"]


# Every place `old()` / `new()` can be written, with a function around it or
# none.  {x} is the form, `old(IO)` or `new(IO)`; the expected codes put
# the placement error first, {p}: E174 for `old`, E175 for `new`.
_ROW = "<IO, State<Int>>"
_MAIN_ONLY = (f"public fn main(@Unit -> @Unit)\n  requires(true)\n"
              f"  ensures(true)\n  effects({_ROW})\n{{\n  ()\n}}\n")


def _in_fn(params: str = "@Int", ret: str = "@Int", req: str = "true",
           ens: str = "true", dec: str = "", body: str = "@Int.0",
           where: str = "") -> str:
    decreases = f"  decreases({dec})\n" if dec else ""
    return (f"public fn f({params} -> {ret})\n  requires({req})\n"
            f"  ensures({ens})\n{decreases}  effects({_ROW})\n"
            f"{{\n  {body}\n}}\n{where}")


_HELPER = ("where {{\n  fn g({params} -> @Int)\n    requires(true)\n"
           "    ensures({ens})\n    effects(" + _ROW + ")\n"
           "  {{\n    1\n  }}\n}}\n")

_FORM_POSITIONS: dict[str, tuple[str, tuple[str, ...]]] = {
    # No function around the form: a declaration's refinement or invariant.
    "type_alias_predicate": (
        "type Bad = { @Int | {x} == 1 };\n\n" + _MAIN_ONLY, ("{p}", "E189")),
    "data_invariant": (
        "private data D invariant({x} == 1) {\n  D(Int)\n}\n\n" + _MAIN_ONLY,
        ("{p}", "E189")),
    "data_field_refinement": (
        "private data D {\n  D({ @Int | {x} == 1 })\n}\n\n" + _MAIN_ONLY,
        ("{p}", "E189")),
    "effect_operation_refinement": (
        "effect E {\n  op e({ @Int | {x} == 1 } -> Unit);\n}\n\n" + _MAIN_ONLY,
        ("{p}", "E189")),
    "ability_operation_refinement": (
        "ability A<T> {\n  op a({ @Int | {x} == 1 } -> T);\n}\n\n" + _MAIN_ONLY,
        ("{p}", "E189")),
    # A function around the form.
    "parameter_refinement": (
        _in_fn(params="@{ @Int | {x} == 1 }"), ("{p}", "E189")),
    "return_refinement": (
        _in_fn(ret="@{ @Int | {x} == 1 }"), ("{p}", "E189")),
    "requires": (_in_fn(req="{x} == 1"), ("{p}", "E189")),
    "decreases": (
        _in_fn(params="@Nat", ret="@Nat", dec="{x}", body="@Nat.0"),
        ("{p}", "E189")),
    "body": (_in_fn(body="{x}"), ("{p}", "E189")),
    "closure_body": (
        _in_fn(body="let @fn(Int -> Int) effects(pure) = "
                    "fn(@Int -> @Int) effects(pure) { {x} };\n  @Int.0"),
        ("{p}", "E189")),
    "where_helper_ensures": (
        _in_fn(body="g(@Int.0)",
               where=_HELPER.format(params="@Int", ens="{x} == 1")),
        ("E189",)),
    "where_helper_parameter_refinement": (
        _in_fn(body="g(@Int.0)",
               where=_HELPER.format(params="@{ @Int | {x} == 1 }",
                                    ens="true")),
        ("{p}", "E189")),
    "ensures": (_in_fn(ens="{x} == 1"), ("E189",)),
}


@pytest.mark.parametrize("form", ["old", "new"])
@pytest.mark.parametrize("position", list(_FORM_POSITIONS))
def test_repro_old_and_new_of_io_in_every_position(
        position: str, form: str) -> None:
    """`old(IO)` / `new(IO)` written anywhere, a function around it or none,
    draws its placement error where it has one and E189, and nothing
    raises.  Round 2 read the enclosing function's row unguarded, so a form
    in a declaration's refinement or invariant raised IndexError (E699)."""
    template, expected = _FORM_POSITIONS[position]
    placement = "E174" if form == "old" else "E175"
    source = template.replace("{x}", f"{form}(IO)")
    assert _all_codes(source) == [
        placement if c == "{p}" else c for c in expected]


def test_repro_e189_with_no_function_around_it_writes_the_no_cell_fix(
) -> None:
    """With no function around the form there is no row to read a cell
    from: the fix is the one for a row with no cell."""
    source = _FORM_POSITIONS["type_alias_predicate"][0].replace(
        "{x}", "old(IO)")
    error, = [e for e in _errors(source) if e.error_code == "E189"]
    assert error.fix == (
        "Name a State cell, `old(State<Int>)` in place of `old(IO)`, and "
        "declare it in the function's effects row, `effects(<State<Int>>)`, "
        "with the cell's type in place of `Int`.")


# ---------------------------------------------------------------------
# The matrix
# ---------------------------------------------------------------------

#: What leaves the element type unfixed: the collection text, its index,
#: and the parameter the function takes (the bare type's).
SOURCES: dict[str, tuple[str, str]] = {
    "empty_literal": ("[]", ""),
    "empty_read_from_an_index": ("[[]][0]", ""),
    "no_type_argument": ("@Array.0", "@Array"),
}

#: Where the index stands: (the function's return type, the body with
#: `{e}` for the value, whether the position's type reaches the value).
POSITIONS: dict[str, tuple[str, str, bool]] = {
    "let": ("Int", "let @Int = {e};\n@Int.0", True),
    "argument": ("Int", "nat_to_int(string_length({e}))", True),
    "return": ("Int", "{e}", True),
    "if_branch": ("Int", "if true then {{\n  {e}\n}} else {{\n  1\n}}", True),
    "element": ("Int", "let @Array<Int> = [{e}];\n"
                       "nat_to_int(array_length(@Array<Int>.0))", False),
    "component": ("Int", "let @Tuple<Int, Int> = Tuple({e}, 1);\n0", False),
    "match": ("Int", "match {e} {{\n  _ -> 1\n}}", False),
    "destructure": ("Int", "let Tuple<@Int, @Int> = {e};\n@Int.0", False),
    "operand": ("Int", "{e} + 1", False),
    "interpolation": ("String", '"v=\\({e})"', False),
    "discard": ("Int", "{e};\n1", False),
}

#: Whether the position's type reaches the index or a generic call that
#: leaves the index with nothing expected of it.
FORMS = ("direct", "open_call")

#: The element type the fix writes in place of its `Int`: the type the
#: program means at the position.
ELEMENT = {"argument": "String"}

#: What an open call whose variable no argument fixes draws at a position
#: that gives it no type, beside the index's E164, as it did at base beside
#: any error behind its argument (`idg(nope(())) + 1` is E200 and E140).
OPEN_CALL_ALSO = {"operand": ["E140"], "interpolation": ["E148"]}


def _cell(source: str, position: str, form: str) -> tuple[str, bool]:
    """The program and whether it is refused."""
    coll, param = SOURCES[source]
    ret, body, typed = POSITIONS[position]
    value = f"{coll}[0]"
    if form == "open_call":
        value = f"idg({value})"
    program = _IDG + _fn("main", param or "@Unit", ret,
                         body.format(e=value),
                         visibility="private" if param else "public")
    if position == "destructure":
        # A tuple is no array element: the neighbour is the value at a
        # tuple's type, which only the bare type can be refused at.
        typed = False
    refused = source == "no_type_argument" or form == "open_call" or not typed
    return program, refused


def _apply_fix(program: str, source: str, position: str) -> str:
    """The program with E164's fix applied as its text says, the element
    type the program means written in place of `Int`."""
    elem = ELEMENT.get(position, "Int")
    if source == "no_type_argument":
        return re.sub(r"@Array(?![<\w])", f"@Array<{elem}>", program)
    coll, _ = SOURCES[source]
    head, _, rest = program.partition("public fn main")
    sig, _, body = rest.partition("{\n")
    body = body.replace(f"{coll}[0]", f"@Array<{elem}>.0[0]", 1)
    return (f"{head}public fn main{sig}{{\n  let @Array<{elem}> = {coll};\n"
            f"{body}")


_CELLS = [(s, p, f) for s in SOURCES for p in POSITIONS for f in FORMS]


@pytest.mark.parametrize(("source", "position", "form"), _CELLS)
def test_an_index_nothing_types_is_refused_and_its_fix_clears_it(
        source: str, position: str, form: str) -> None:
    """A refused cell draws E164 first and nothing else of its own (an open
    call at a position that gives it no type draws what it drew at base
    beside any error behind its argument); its fix, applied, leaves no
    E164.  Where the fixed program is well typed it checks clean and keeps
    every function at compile.  A cell whose position's type reaches the
    index checks and compiles as it is."""
    program, refused = _cell(source, position, form)
    if not refused:
        assert _codes(program) == []
        assert _dropped(program) == []
        return
    also = OPEN_CALL_ALSO.get(position, []) if form == "open_call" else []
    assert _codes(program) == ["E164", *also], program
    # The edit `_apply_fix` makes is the one the fix's text writes.
    fix = _errors(program)[0].fix
    coll, _ = SOURCES[source]
    written = ("`@Array<Int>` in place of `@Array`"
               if source == "no_type_argument"
               else f"`let @Array<Int> = {coll};`, and index the binding, "
                    f"`@Array<Int>.0[0]`")
    assert written in fix, fix
    fixed = _apply_fix(program, source, position)
    codes = _codes(fixed)
    assert "E164" not in codes, fixed
    if position != "destructure":
        assert codes == [], fixed
        assert _dropped(fixed) == [], fixed


# ---------------------------------------------------------------------
# The census: no unreported `Unknown` in the corpus
# ---------------------------------------------------------------------

def _corpus() -> list[tuple[str, str, str | None]]:
    """(label, source or path, file) for each program the census reads."""
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


def _unreported_unknowns(source: str | Path, file: str | None
                         ) -> list[tuple[str, int]]:
    """Each expression typed `Unknown` while no error is reported and no
    typed hole stands inside it."""
    found: list[tuple[str, int]] = []
    original = TypeChecker._synth_expr

    def hooked(self, expr, *, expected=None):  # type: ignore[no-untyped-def]
        result = original(self, expr, expected=expected)
        if (isinstance(base_type(result) if result is not None else None,
                       UnknownType)
                and not any(d.severity == "error" for d in self.errors)
                and not any(isinstance(n, ast.HoleExpr)
                            for n in fold.walk(expr))):
            found.append((type(expr).__name__,
                          expr.span.line if expr.span else 0))
        return result

    TypeChecker._synth_expr = hooked  # type: ignore[method-assign]
    try:
        pipeline.check(Path(source) if file is None else source, file=file)
    finally:
        TypeChecker._synth_expr = original  # type: ignore[method-assign]
    return found


@pytest.mark.parametrize(("label", "source", "file"), _CORPUS,
                         ids=[c[0] for c in _CORPUS])
def test_no_corpus_program_holds_an_unreported_unknown(
        label: str, source: str, file: str | None) -> None:
    assert _unreported_unknowns(source, file) == [], label


def test_the_census_finds_an_unreported_unknown() -> None:
    """The census's own control: an `Unknown` with nothing behind it is
    found where one stands (the base's `[][0]`, made with the index's
    refusal taken away)."""
    from vera.checker.expressions import ExpressionsMixin
    refuse = ExpressionsMixin._refuse_untyped_index
    ExpressionsMixin._refuse_untyped_index = (  # type: ignore[method-assign]
        lambda self, expr, *, bare: None)
    try:
        found = _unreported_unknowns(_ISSUE, "control.vera")
    finally:
        ExpressionsMixin._refuse_untyped_index = refuse  # type: ignore[method-assign]
    assert ("IndexExpr", 6) in found, found
