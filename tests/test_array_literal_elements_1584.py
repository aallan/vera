"""Every element of an array literal has the literal's element type (#1584).

Spec §4.12.1: "All elements must have the same type."  The checker took an
array literal's element type from its first typed element and never compared
the other elements with it, so `["a", 5]` checked as an `Array<String>` and
`[@T.0, 0]` checked in a `forall<T>` body with `T` rigid; code generation then
dropped the function or wrote a module that failed to load, and a literal
whose elements are pointers (`[Some(1), Some("a")]`) ran with one element
that is not of the array's element type.

The checker now holds every element to the element type with the judgement it
holds a call argument to its parameter with: a subtype, or, where a type
variable is still unresolved on either side, a type some instantiation makes
one.  An element that judgement refuses is E162, reported at the element and
naming its position, its type and the element type.  The element type is
still the first typed element's, which is the type the literal is given and
the layout code generation stores every element at, and the literal's type is
unchanged wherever the judgement accepts it.

The class is every literal with an element, after the first typed one, that
does not fit the element type: the instrument crosses where the element is
(the second, a middle and the last of four), what it is (a literal, a slot, a
call, a nested literal, and in a generic body a slot of the rigid type), and
where the literal stands (fifteen contexts: an expression statement, a generic
and a plain call's argument, a `let` value with and without the literal's
own annotation, a return value, a nested literal's element, a constructor
field, a generic body, a `match` arm and an `if` branch, each as a value and
in a call, a pipe and a closure body).  A type-pair matrix holds the judgement
to an oracle of its own over every arm of the comparison, and the complement
holds that every literal the judgement accepts still checks with the type it
had.
"""

from __future__ import annotations

import dataclasses
import re
from dataclasses import dataclass

import pytest

from vera import ast
from tests import pipeline

# A generated class instrument (tests/matrix_sample.py): a pull request runs a
# sample of its parametrised cells, and all of them when it changes this file
# or a module that decides its class, here the checker's judgement of an array
# literal's elements and the call-argument judgement it shares.
pytestmark = pytest.mark.matrix(
    decides=[
        "vera/checker/expressions.py",
        "vera/checker/calls.py",
    ],
)


# =====================================================================
# Helpers
# =====================================================================


def _checked(source: str) -> pipeline.Checked:
    """Check *source*; a parse or transform error is raised, not counted."""
    checked = pipeline.check(source)
    _ = checked.program
    return checked


def _codes(checked: pipeline.Checked) -> list[str]:
    """The error codes the check reported, in order."""
    return [d.error_code for d in checked.errors]


def _e162(checked: pipeline.Checked) -> list[tuple[int, int]]:
    """Where each E162 the check reported is placed."""
    return [(d.location.line, d.location.column)
            for d in checked.diagnostics if d.error_code == "E162"]


def _literal(parts: list[str]) -> tuple[str, list[int]]:
    """An array literal of *parts*, and the offset of each part in it."""
    text = "["
    offsets: list[int] = []
    for i, part in enumerate(parts):
        if i:
            text += ", "
        offsets.append(len(text))
        text += part
    return text + "]", offsets


def _place(source: str, text: str, offset: int = 0) -> tuple[int, int]:
    """The 1-based line and column of *offset* into the one occurrence of
    *text* in *source*."""
    assert source.count(text) == 1, text
    at = source.index(text) + offset
    line = source.count("\n", 0, at) + 1
    column = at - (source.rfind("\n", 0, at) + 1) + 1
    return line, column


def _literal_types(checked: pipeline.Checked) -> dict[tuple[int, int], str]:
    """Each array literal's synthesized type, by where it begins, read from
    the checker's `expr_types` table, with each fresh type variable's
    number dropped (`T$1` is `T$`): the number counts the variables minted
    before it, which says nothing about the literal."""
    found: list[ast.ArrayLit] = []

    def walk(node: object) -> None:
        if isinstance(node, ast.ArrayLit):
            found.append(node)
        if isinstance(node, ast.Node):
            for f in dataclasses.fields(node):
                walk(getattr(node, f.name))
        elif isinstance(node, (list, tuple)):
            for value in node:
                walk(value)

    walk(checked.program)
    types = checked.artifacts.expr_types
    out: dict[tuple[int, int], str] = {}
    for lit in found:
        key = ast.span_key(lit)
        assert key is not None
        if key in types:
            out[(key[0], key[1])] = re.sub(r"\$\d+", "$", types[key])
    return out


def _fn(body: str, *, ret: str = "Nat", params: str = "@Nat",
        pre: str = "", generic: bool = False) -> str:
    head = "private forall<T> fn" if generic else "public fn"
    return f"""{pre}
{head} f({params} -> @{ret})
  requires(true)
  ensures(true)
  effects(pure)
{{
  {body}
}}
"""


_TAKES = """private fn takes(@Array<String> -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  array_length(@Array<String>.0)
}
"""

_BOX = "private data Box { MkBox(Array<String>) }\n"


@dataclass(frozen=True)
class _Context:
    """A position an array literal of `String` elements can stand in."""

    body: str
    ret: str = "Nat"
    pre: str = ""
    generic: bool = False

    def source(self, literal: str) -> str:
        params = "@T, @Nat" if self.generic else "@Nat"
        return _fn(self.body.format(lit=literal), ret=self.ret,
                   params=params, pre=self.pre, generic=self.generic)


#: Every context the literal stands in, each a body with `{lit}` where the
#: literal goes.  Where the context has a type of its own for the literal
#: (`arg`, `let_ann`, `ret`, `ctor_field`, `if_value`, `match_value`), it is
#: `Array<String>`, so the literal fits it and its elements are the only
#: thing wrong.
CONTEXTS: dict[str, _Context] = {
    "stmt": _Context("{lit};\n  0"),
    "generic_arg": _Context("array_length({lit})"),
    "arg": _Context("takes({lit})", pre=_TAKES),
    "let_ann": _Context(
        "let @Array<String> = {lit};\n  array_length(@Array<String>.0)"),
    "let_value": _Context("let @Nat = array_length({lit});\n  @Nat.0"),
    "ret": _Context("{lit}", ret="Array<String>"),
    "nested": _Context("array_length([{lit}])"),
    "ctor_field": _Context(
        "match MkBox({lit}) {{\n"
        "    MkBox(@Array<String>) -> array_length(@Array<String>.0)\n  }}",
        pre=_BOX),
    "generic_body": _Context("array_length({lit})", generic=True),
    "match_arm": _Context(
        "match @Nat.0 {{\n    0 -> array_length({lit}),\n    _ -> 0\n  }}"),
    "if_branch": _Context(
        "if @Nat.0 == 0 then {{\n    array_length({lit})\n  }} else {{\n"
        "    0\n  }}"),
    "if_value": _Context(
        "let @Array<String> = if @Nat.0 == 0 then {{\n    {lit}\n  }} else "
        "{{\n    [\"t\"]\n  }};\n  array_length(@Array<String>.0)"),
    "match_value": _Context(
        "let @Array<String> = match @Nat.0 {{\n    0 -> {lit},\n"
        "    _ -> [\"t\"]\n  }};\n  array_length(@Array<String>.0)"),
    "piped": _Context("{lit} |> array_length()"),
    "closure": _Context(
        "apply_fn(fn(@Unit -> @Nat) effects(pure) {{ array_length({lit}) }}, "
        "())"),
}

#: The well-typed element: it sets the element type, `String`.
_FIT = '"s"'

#: What the element that does not fit is, with the type the diagnostic names.
#: `rigid_slot` is a slot of the generic body's own type parameter, which
#: exists only where one is in scope.
KINDS: dict[str, tuple[str, str]] = {
    "literal": ("5", "Nat"),
    "slot": ("@Nat.0", "Nat"),
    "call": ('string_length("ab")', "Nat"),
    "nested_literal": ("[5]", "Array<Nat>"),
    "rigid_slot": ("@T.0", "T"),
}

#: Where the element that does not fit is, in a literal of four elements.
POSITIONS: dict[str, int] = {"second": 1, "middle": 2, "last": 3}


def _cells() -> list[tuple[str, str, str]]:
    return [
        (context, kind, position)
        for context in CONTEXTS
        for kind in KINDS
        for position in POSITIONS
        if kind != "rigid_slot" or CONTEXTS[context].generic
    ]


# =====================================================================
# The reported programs
# =====================================================================

_ISSUE_MIXED = """public fn main(@Unit -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  string_length(["a", 5][0])
}
"""

_ISSUE_RIGID = """private forall<T> fn g(@T -> @T)
  requires(true)
  ensures(true)
  effects(pure)
{
  array_reverse([@T.0, 0])[0]
}

public fn f(@String -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  string_length(g(@String.0))
}
"""


def test_repro_mixed_literal_is_refused_at_its_second_element() -> None:
    checked = _checked(_ISSUE_MIXED)
    assert _codes(checked) == ["E162"]
    assert _e162(checked) == [_place(_ISSUE_MIXED, '["a", 5]', 6)]
    (diag,) = checked.errors
    assert diag.description == (
        "Array literal element 1 has type Nat, but the literal's element "
        "type is String, the type of element 0.")
    assert diag.spec_ref == 'Chapter 4, Section 4.12.1 "Array Literals"'
    assert diag.rationale and diag.fix


def test_repro_literal_beside_a_rigid_type_variable_is_refused() -> None:
    checked = _checked(_ISSUE_RIGID)
    assert _codes(checked) == ["E162"]
    assert _e162(checked) == [_place(_ISSUE_RIGID, "[@T.0, 0]", 7)]
    (diag,) = checked.errors
    assert diag.description == (
        "Array literal element 1 has type Nat, but the literal's element "
        "type is T, the type of element 0.")


# =====================================================================
# The class: position x kind x context
# =====================================================================


@pytest.mark.parametrize(("context", "kind", "position"), _cells())
def test_element_that_does_not_fit_is_refused_where_it_is(
        context: str, kind: str, position: str) -> None:
    misfit, misfit_type = KINDS[kind]
    index = POSITIONS[position]
    parts = [_FIT] * 4
    parts[index] = misfit
    literal, offsets = _literal(parts)
    source = CONTEXTS[context].source(literal)
    checked = _checked(source)
    assert _codes(checked) == ["E162"], checked.errors
    assert _e162(checked) == [_place(source, literal, offsets[index])]
    (diag,) = checked.errors
    assert diag.description == (
        f"Array literal element {index} has type {misfit_type}, but the "
        "literal's element type is String, the type of element 0.")


@pytest.mark.parametrize("context", sorted(CONTEXTS))
def test_same_typed_literal_still_checks_with_its_type(context: str) -> None:
    literal, _ = _literal([_FIT] * 4)
    source = CONTEXTS[context].source(literal)
    checked = _checked(source)
    assert checked.diagnostics == ()
    assert _literal_types(checked)[_place(source, literal)] == "Array<String>"


# =====================================================================
# The judgement: one pair of element types per cell, against an oracle
# =====================================================================
#
# Each entry is an element and the family the oracle files it under: two
# elements fit one another exactly when their families are equal.  The
# families follow the arms of the comparison: identical types, `Nat` and
# `Int` (each a subtype of the other), a refinement and its base, a
# constructor's arguments (an `Option`, an `Array`, a `Tuple`), a function
# type's parameters and effects, and the primitives that relate to nothing
# else (`Bool`, `Float64`, `String`, `Byte`).

_PAIR_PRE = """type PosInt = { @Int | @Int.0 > 0 };
type NatToNat = fn(Nat -> Nat) effects(pure);
type NatToNatIO = fn(Nat -> Nat) effects(<IO>);
type StrToNat = fn(String -> Nat) effects(pure);
"""

_PAIR_PARAMS = ("@Nat, @Int, @Bool, @Float64, @String, @Byte, @PosInt, "
                "@NatToNat, @NatToNatIO, @StrToNat")

ELEMENTS: dict[str, tuple[str, str]] = {
    "nat_literal": ("5", "integer"),
    "negative_literal": ("-1", "integer"),
    "nat_slot": ("@Nat.0", "integer"),
    "int_slot": ("@Int.0", "integer"),
    "refined_slot": ("@PosInt.0", "integer"),
    "int_call": ("abs(-3)", "integer"),
    "bool": ("true", "Bool"),
    "float": ("1.5", "Float64"),
    "string": ('"s"', "String"),
    "string_call": ('string_concat("a", "b")', "String"),
    "byte_slot": ("@Byte.0", "Byte"),
    "nat_array": ("[5]", "Array<integer>"),
    "int_array": ("[-1]", "Array<integer>"),
    "string_array": ('["s"]', "Array<String>"),
    "some_nat": ("Some(5)", "Option<integer>"),
    "some_string": ('Some("s")', "Option<String>"),
    "tuple": ('Tuple(1, "s")', "Tuple<integer, String>"),
    "swapped_tuple": ('Tuple("s", 1)', "Tuple<String, integer>"),
    "fn_slot": ("@NatToNat.0", "fn(integer) pure"),
    "fn_string_slot": ("@StrToNat.0", "fn(String) pure"),
}


def _pair_source(first: str, second: str) -> tuple[str, str, list[int]]:
    literal, offsets = _literal([ELEMENTS[first][0], ELEMENTS[second][0]])
    source = _fn(f"array_length({literal})", params=_PAIR_PARAMS,
                 pre=_PAIR_PRE)
    return source, literal, offsets


@pytest.mark.parametrize(
    ("first", "second"),
    [(a, b) for a in ELEMENTS for b in ELEMENTS])
def test_element_pair_against_the_oracle(first: str, second: str) -> None:
    source, literal, offsets = _pair_source(first, second)
    checked = _checked(source)
    fits = ELEMENTS[first][1] == ELEMENTS[second][1]
    if fits:
        assert checked.errors == ()
    else:
        assert _codes(checked) == ["E162"], checked.errors
        assert _e162(checked) == [_place(source, literal, offsets[1])]


#: The function-type arms the families above leave out: the effect row and
#: a parameter that is a subtype in one direction only.  A pure function
#: fits where an `IO` one is the element type, and not the other way round,
#: as an argument does.
_EFFECT_PAIRS = [
    ("@NatToNatIO.0", "@NatToNat.0", True),
    ("@NatToNat.0", "@NatToNatIO.0", False),
]


@pytest.mark.parametrize(("first", "second", "fits"), _EFFECT_PAIRS)
def test_function_effect_row_is_judged_as_an_argument_is(
        first: str, second: str, fits: bool) -> None:
    literal, offsets = _literal([first, second])
    source = _fn(f"array_length({literal})", params=_PAIR_PARAMS,
                 pre=_PAIR_PRE)
    checked = _checked(source)
    if fits:
        assert checked.errors == ()
    else:
        assert _codes(checked) == ["E162"]
        assert _e162(checked) == [_place(source, literal, offsets[1])]


# =====================================================================
# The complement: what the judgement accepts still checks, with its type
# =====================================================================

_ID = """private forall<T> fn id(@T -> @T)
  requires(true)
  ensures(true)
  effects(pure)
{
  @T.0
}
"""


@dataclass(frozen=True)
class _Kept:
    """A literal the fix must leave alone: the errors the check reports for
    it (none, or the ones another check owns), and the type the checker
    gives it, as `main` gives it."""

    literal: str
    literal_type: str
    errors: tuple[str, ...] = ()
    params: str = "@Nat, @Int, @Byte, @PosInt"
    generic: bool = False
    pre: str = ""


KEPT: dict[str, _Kept] = {
    # An integer literal or slot beside a `Nat` or an `Int` slot.
    "nat_slot_then_literal": _Kept("[@Nat.0, 5]", "Array<Nat>"),
    "literal_then_nat_slot": _Kept("[5, @Nat.0]", "Array<Nat>"),
    "int_slot_then_literal": _Kept("[@Int.0, 5]", "Array<Int>"),
    "literal_then_int_slot": _Kept("[5, @Int.0]", "Array<Nat>"),
    "literal_then_negative": _Kept("[1, -1]", "Array<Nat>"),
    "negative_then_literal": _Kept("[-1, 1]", "Array<Int>"),
    "byte_slots": _Kept("[@Byte.0, @Byte.0]", "Array<Byte>"),
    # A refinement beside its base, either way round.
    "refined_then_base": _Kept("[@PosInt.0, @Int.0]", "Array<{@Int | ...}>"),
    "base_then_refined": _Kept("[@Int.0, @PosInt.0]", "Array<Int>"),
    "refined_then_literal": _Kept("[@PosInt.0, 3]", "Array<{@Int | ...}>"),
    # An element whose type is already an error, reported by its own check.
    "unresolved_slot_first": _Kept('[@String.9, "s"]', "Array<String>",
                                   errors=("E130",)),
    "unresolved_slot_later": _Kept('["s", @String.9]', "Array<String>",
                                   errors=("E130",)),
    "unresolved_call": _Kept('["s", nope()]', "Array<String>",
                             errors=("E200",)),
    # The empty literal, alone and beside a typed one.
    "empty": _Kept("[]", "Array<?>"),
    "empty_then_typed": _Kept("[[], [1]]", "Array<Array<?>>"),
    "typed_then_empty": _Kept("[[1], []]", "Array<Array<Nat>>"),
    # A type variable left unresolved by a constructor or a call.
    "none_then_some": _Kept("[None, Some(1)]", "Array<Option<T$>>"),
    "some_then_none": _Kept("[Some(1), None]", "Array<Option<Nat>>"),
    "ok_then_err": _Kept('[Ok(1), Err("e")]', "Array<Result<Nat, E$>>"),
    "fresh_map_then_map": _Kept(
        '[map_new(), map_insert(map_new(), "k", 1)]', "Array<Map<K, V>>"),
    "map_then_fresh_map": _Kept(
        '[map_insert(map_new(), "k", 1), map_new()]',
        "Array<Map<String, Nat>>"),
    "generic_call": _Kept("[id(1), 2]", "Array<Nat>", pre=_ID),
    # The rigid type variable beside itself, and in a constructor.
    "rigid_slots": _Kept("[@T.0, @T.0]", "Array<T>", params="@T",
                         generic=True),
    "rigid_option_then_none": _Kept("[Some(@T.0), None]", "Array<Option<T>>",
                                    params="@T", generic=True),
    "none_then_rigid_option": _Kept("[None, Some(@T.0)]",
                                    "Array<Option<T$>>", params="@T",
                                    generic=True),
    # A zero-size element type is refused as a whole, once (E135), and its
    # other elements are not held to it.
    "unit_first": _Kept("[(), 1]", "Array<Unit>", errors=("E135",)),
}


_KEPT_PRE = "type PosInt = { @Int | @Int.0 > 0 };\n"


@pytest.mark.parametrize("name", sorted(KEPT))
def test_accepted_literal_keeps_its_verdict_and_type(name: str) -> None:
    kept = KEPT[name]
    source = _fn(f"array_length({kept.literal})", params=kept.params,
                 pre=_KEPT_PRE + kept.pre, generic=kept.generic)
    checked = _checked(source)
    assert tuple(_codes(checked)) == kept.errors, checked.errors
    assert _e162(checked) == []
    assert _literal_types(checked)[_place(source, kept.literal)] == (
        kept.literal_type)


# =====================================================================
# Mutant killers: each fails against the mutant the test names
# =====================================================================


def _mixed_strings(misfit_at: int, n: int = 4) -> tuple[str, str, list[int]]:
    parts = ['"s"'] * n
    parts[misfit_at] = "5"
    literal, offsets = _literal(parts)
    return _fn(f"array_length({literal})"), literal, offsets


def test_mutant_every_element_is_compared_not_only_the_second() -> None:
    # A checker that compares only element 1 passes this literal.
    source, literal, offsets = _mixed_strings(3)
    checked = _checked(source)
    assert _e162(checked) == [_place(source, literal, offsets[3])]


def test_mutant_the_element_type_is_the_first_elements_not_the_last() -> None:
    # Held to the LAST element's type, `Nat`, the three strings would each be
    # refused and the `5` accepted.
    source, literal, offsets = _mixed_strings(3)
    checked = _checked(source)
    assert _e162(checked) == [_place(source, literal, offsets[3])]
    (diag,) = checked.errors
    assert diag.description.startswith(
        "Array literal element 3 has type Nat, but the literal's element "
        "type is String")


def test_mutant_the_report_is_at_the_element_not_the_literal() -> None:
    source, literal, offsets = _mixed_strings(1)
    checked = _checked(source)
    at_element = _place(source, literal, offsets[1])
    assert at_element != _place(source, literal)
    assert _e162(checked) == [at_element]


def test_each_element_that_does_not_fit_is_reported() -> None:
    # Two misfits, two reports, each at its own element; an element after
    # the first misfit is still held to the first element's type.
    literal, offsets = _literal(['"s"', "5", '"t"', "true"])
    source = _fn(f"array_length({literal})")
    checked = _checked(source)
    assert _e162(checked) == [_place(source, literal, offsets[1]),
                              _place(source, literal, offsets[3])]


def test_element_type_comes_from_the_first_typed_element() -> None:
    # An element whose type is an error does not set the element type: the
    # first typed element after it does, and the diagnostic says which.
    literal, offsets = _literal(["@String.9", '"s"', "5"])
    source = _fn(f"array_length({literal})")
    checked = _checked(source)
    assert _codes(checked) == ["E130", "E162"]
    assert _e162(checked) == [_place(source, literal, offsets[2])]
    diag = checked.errors[1]
    assert diag.description == (
        "Array literal element 2 has type Nat, but the literal's element "
        "type is String, the type of element 1.")
