"""The type an array literal, an `if` or a `match` is given takes every part
of it into account, an open position included (#1668).

Spec §4.12.1: all elements of an array literal have the same type.  A part
whose type leaves a position open, the `T` of a `None` or the element type
of an empty literal `[]`, was held to the other parts with the position
treated as a wildcard, and the position stayed open in the type the whole
was given.  So `[None, Some("abc")]` was an `Array<Option<T>>` whose `T`
nothing had fixed, a context then fixed it to a third type
(`second([None, Some("abc")])` read the `"abc"` as a `@Nat`), and two parts
that fill it with different types (`[None, Some(1), Some("abc")]`) both
checked.  An `if` and a `match` joined their branches with the same gap:
`if c then { ["abc"] } else { [] }` was an `Array<?>`, and `match n { 0 ->
None, _ -> 5 }` was a `Nat`.

The checker now joins the parts: the type of the first typed part, with each
position it leaves open given by the first later part that fills it, and
each part is held to that joined type.  One function computes the join
(`CallsMixin._join`), and it is the witness of the judgement each part is
held to (`_compatible_modulo_typevars`): the positions that judgement treats
as wildcards are the ones the join fills.  A position no part fills stays
open, and the context fills it as before.

The class instrument crosses the site the parts are joined at (an array
literal's elements, an `if`'s branches, a `match`'s arms), the type
constructor that leaves the position open (`Option`, an empty `Array`,
`Result`'s other parameter, a user generic `data`), how deep the position
sits (directly, inside a `Tuple`, inside an `Array` of `Tuple`s), what fills
it (a later part, an earlier part, two later parts that agree, two that
disagree, the context agreeing, the context disagreeing, nothing, and a part
of another type, closed or open), and where the whole stands (a bare
`array_length`, a `let`, a call argument, a return value, a generic call's
argument), 1,584 cells.  The expectation of every cell is stated by rule,
below, never read back from the checker.  The rule has every context fill a
position the parts leave open; a `let` and a return value refuse a type
variable there instead (#1682), and those 162 cells are strict xfails.
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
# or a module that decides its class: the array literal's fold, the join it
# shares with the call-argument judgement, and the `if` and `match` joins.
pytestmark = pytest.mark.matrix(
    decides=[
        "vera/checker/expressions.py",
        "vera/checker/calls.py",
        "vera/checker/control.py",
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


def _where(checked: pipeline.Checked) -> list[tuple[str, int, int]]:
    """Each diagnostic's code and place, in order."""
    return [(d.error_code, d.location.line, d.location.column)
            for d in checked.diagnostics]


def _place(source: str, text: str, offset: int = 0) -> tuple[int, int]:
    """The 1-based line and column of *offset* into the one occurrence of
    *text* in *source*."""
    assert source.count(text) == 1, text
    at = source.index(text) + offset
    line = source.count("\n", 0, at) + 1
    column = at - (source.rfind("\n", 0, at) + 1) + 1
    return line, column


def _literal_types(checked: pipeline.Checked) -> dict[tuple[int, int], str]:
    """Each array literal's type as the checker records it, by where the
    literal begins, with each fresh type variable's number dropped (`T$1`
    is `T$`): the number counts the variables minted before it."""
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


def _fn(body: str, *, ret: str = "Nat", params: str = "@Bool, @Nat",
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


def _joined(parts: list[str], sep: str = ", ") -> tuple[str, list[int]]:
    """*parts* joined by *sep*, and the offset of each part in the text."""
    text = ""
    offsets: list[int] = []
    for i, part in enumerate(parts):
        if i:
            text += sep
        offsets.append(len(text))
        text += part
    return text, offsets


# =====================================================================
# The reported programs
# =====================================================================

_SECOND = """private fn second(@Array<Option<Nat>> -> @Nat)
  requires(array_length(@Array<Option<Nat>>.0) > 1)
  ensures(true)
  effects(pure)
{
  match @Array<Option<Nat>>.0[1] {
    Some(@Nat) -> @Nat.0,
    None -> 0
  }
}
"""

_ISSUE_CONTEXT = _SECOND + """
public fn main(@Unit -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  second([None, Some("abc")])
}
"""

_ISSUE_TWO_FILLERS = """public fn main(@Unit -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  array_length([None, Some(1), Some("abc")])
}
"""

_ISSUE_TWO_DEEP = """public fn main(@Unit -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Array<Array<Nat>> = [[], ["abc"]];
  array_length(@Array<Array<Nat>>.0)
}
"""

_ISSUE_RESULT = """public fn main(@Unit -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  array_length([Err("e"), Ok(1), Ok("x")])
}
"""

_ISSUE_RIGID = """private forall<T> fn g(@T -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  array_length([None, Some(@T.0), Some(0)])
}

public fn main(@Unit -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  g(1)
}
"""

_IF_FIRST = """private fn first(@Array<Nat> -> @Nat)
  requires(array_length(@Array<Nat>.0) > 0)
  ensures(true)
  effects(pure)
{
  @Array<Nat>.0[0]
}

public fn main(@Unit -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  first(if true then { ["abc"] } else { [] })
}
"""

_MATCH_OTHER_TYPE = """public fn main(@Nat -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  array_length([match @Nat.0 { 0 -> None, _ -> 5 }])
}
"""

_IF_OTHER_HEAD = """public fn main(@Bool -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  array_length([if @Bool.0 then { None } else { Ok(1) }])
}
"""


def test_repro_a_later_element_fills_the_position_the_context_meets() -> None:
    checked = _checked(_ISSUE_CONTEXT)
    assert _where(checked) == [
        ("E202", *_place(_ISSUE_CONTEXT, '[None, Some("abc")]'))]
    assert checked.errors[0].description == (
        "Argument 0 of 'second' has type Array<Option<String>>, expected "
        "Array<Option<Nat>>.")


def test_repro_two_later_elements_that_disagree() -> None:
    checked = _checked(_ISSUE_TWO_FILLERS)
    literal = '[None, Some(1), Some("abc")]'
    assert _where(checked) == [
        ("E162", *_place(_ISSUE_TWO_FILLERS, literal,
                         literal.index('Some("abc")')))]
    assert checked.errors[0].description == (
        "Array literal element 2 has type Option<String>, but the literal's "
        "element type is Option<Nat>, the type of element 0, completed by "
        "element 1.")


def test_repro_an_empty_literal_filled_two_deep() -> None:
    checked = _checked(_ISSUE_TWO_DEEP)
    assert _where(checked) == [
        ("E170", *_place(_ISSUE_TWO_DEEP, '[[], ["abc"]]'))]
    assert checked.errors[0].description == (
        "Let binding expects Array<Array<Nat>>, value has type "
        "Array<Array<String>>.")


def test_repro_result_parameters_filled_by_two_elements() -> None:
    checked = _checked(_ISSUE_RESULT)
    literal = '[Err("e"), Ok(1), Ok("x")]'
    assert _where(checked) == [
        ("E162", *_place(_ISSUE_RESULT, literal, literal.index('Ok("x")')))]
    assert checked.errors[0].description == (
        "Array literal element 2 has type Result<String, ?>, but the "
        "literal's element type is Result<Nat, String>, the type of element "
        "0, completed by element 1.")


def test_repro_rigid_type_variable_fills_the_position() -> None:
    checked = _checked(_ISSUE_RIGID)
    literal = "[None, Some(@T.0), Some(0)]"
    assert _where(checked) == [
        ("E162", *_place(_ISSUE_RIGID, literal, literal.index("Some(0)")))]
    assert checked.errors[0].description == (
        "Array literal element 2 has type Option<Nat>, but the literal's "
        "element type is Option<T>, the type of element 0, completed by "
        "element 1.")


def test_repro_if_branch_fills_the_empty_branch() -> None:
    checked = _checked(_IF_FIRST)
    assert _where(checked) == [
        ("E202", *_place(_IF_FIRST, 'if true then { ["abc"] } else { [] }'))]


def test_repro_match_arm_of_another_type_after_an_open_arm() -> None:
    checked = _checked(_MATCH_OTHER_TYPE)
    assert _where(checked) == [
        ("E302", *_place(_MATCH_OTHER_TYPE, "_ -> 5", 5))]


def test_repro_if_branches_of_two_open_types() -> None:
    checked = _checked(_IF_OTHER_HEAD)
    assert _where(checked) == [
        ("E301", *_place(_IF_OTHER_HEAD,
                         "if @Bool.0 then { None } else { Ok(1) }"))]


# =====================================================================
# The class: site x open type x depth x filler x context
# =====================================================================


@dataclass(frozen=True)
class _Head:
    """A type constructor a value of which can leave a type position open.

    *open* is a part that leaves it open, *fill* one that fills it with the
    value at `{v}`; *type* is the constructor applied to `{x}` as source
    spells it; *open_shown* and *open_recorded* are the open part's type as
    a diagnostic shows it (an open position is `?`) and as the checker
    records it (an open type variable is `T$`); *fill_shown* is the filling
    part's own type as a diagnostic shows it; *other_open* is an open part
    of another type constructor, shown as *other_open_shown*."""

    open: str
    fill: str
    type: str
    open_shown: str
    open_recorded: str
    fill_shown: str
    other_open: str
    other_open_shown: str
    pre: str = ""


HEADS: dict[str, _Head] = {
    "option": _Head("None", "Some({v})", "Option<{x}>", "Option<?>",
                    "Option<T$>", "Option<{x}>", 'Err("e")',
                    "Result<?, String>"),
    "array": _Head("[]", "[{v}]", "Array<{x}>", "Array<?>", "Array<?>",
                   "Array<{x}>", "None", "Option<?>"),
    "result": _Head('Err("e")', "Ok({v})", "Result<{x}, String>",
                    "Result<?, String>", "Result<T$, String>",
                    "Result<{x}, ?>", "None", "Option<?>"),
    "user": _Head("Empty", "Full({v})", "Bag<{x}>", "Bag<?>", "Bag<T$>",
                  "Bag<{x}>", "None", "Option<?>",
                  pre="private data Bag<T> { Empty, Full(T) }\n"),
}

#: How deep the open position sits in a part's type: each wraps a part at
#: `{p}`, and its type at `{t}`.
DEPTHS: dict[str, tuple[str, str]] = {
    "direct": ("{p}", "{t}"),
    "one_deep": ("Tuple({p}, -1)", "Tuple<{t}, Int>"),
    "two_deep": ("[Tuple({p}, -1)]", "Array<Tuple<{t}, Int>>"),
}

#: The values a filling part holds, and their types.
VALUES: dict[str, tuple[str, str]] = {
    "s": ('"abc"', "String"),
    "t": ('"xyz"', "String"),
    "n": ("5", "Nat"),
}


@dataclass(frozen=True)
class _Filler:
    """What fills the open position, as the parts in order: `open` (the
    head's open part), `fill:<value>`, `other_closed` (a `Nat` where the
    head's value is) or `other_open` (the head's other open part).

    *joined* is the type the position is given by the parts (None where no
    part fills it); *refused* the part that does not fit the join of the
    parts before it; *completed_by* the parts after the first that fill a
    position of the join before the refused one; *context* the type the
    context gives the position."""

    parts: tuple[str, ...]
    joined: str | None
    context: str
    refused: int | None = None
    completed_by: tuple[int, ...] = ()


FILLERS: dict[str, _Filler] = {
    "later": _Filler(("open", "fill:s"), "String", "String"),
    "earlier": _Filler(("fill:s", "open"), "String", "String"),
    "agree2": _Filler(("open", "fill:s", "fill:t"), "String", "String"),
    "disagree2": _Filler(("open", "fill:s", "fill:n"), "String", "String",
                         refused=2, completed_by=(1,)),
    "ctx_agree": _Filler(("open", "fill:n"), "Nat", "Nat"),
    "ctx_disagree": _Filler(("open", "fill:s"), "String", "Nat"),
    "nothing": _Filler(("open", "open"), None, "Nat"),
    "other_closed": _Filler(("open", "other_closed"), None, "String",
                            refused=1),
    "other_open": _Filler(("open", "other_open"), None, "String",
                          refused=1),
}


@dataclass(frozen=True)
class _Context:
    """A position the literal stands in, with `{lit}` where it goes and
    `{c}` for the element type the context gives it; *code* is what the
    context reports for a literal of another element type, and *at* the
    text of the source it reports it at (`{lit}` for the literal).

    *fills_open_var* is whether the context gives an element type a type
    variable leaves open the type it expects, as the rule says every
    context does: an argument is held to its parameter with each
    unresolved variable a wildcard, and a generic call's inference binds
    it, but a `let` and a return value hold the literal by subtyping,
    which meets a type variable only by name, and refuse it (#1682).
    Those cells are strict xfails.  Every context admits the open element
    type of an empty literal, which subtyping treats as unknown."""

    body: str
    code: str | None = None
    at: str = "{lit}"
    ret: str = "Nat"
    pre: str = ""
    param: bool = False
    fills_open_var: bool = True


_TAKES = """private fn takes(@Array<{c}> -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{{
  array_length(@Array<{c}>.0)
}}
"""

CONTEXTS: dict[str, _Context] = {
    "bare": _Context("array_length({lit})"),
    "let": _Context(
        "let @Array<{c}> = {lit};\n  array_length(@Array<{c}>.0)", "E170",
        fills_open_var=False),
    "arg": _Context("takes({lit})", "E202", pre=_TAKES),
    "ret": _Context("{lit}", "E121", ret="Array<{c}>", fills_open_var=False),
    "generic": _Context("array_length(array_append({lit}, @{c}.0))", "E205",
                        at="array_append(", param=True),
}

#: Where the parts are joined.
SITES = ("literal", "if", "match")


def _part(head: _Head, depth: str, part: str) -> tuple[str, str]:
    """The source of *part* at *depth*, and its type as a diagnostic shows
    it."""
    wrap, wrap_type = DEPTHS[depth]
    if part == "open":
        text, shown = head.open, head.open_shown
    elif part == "other_open":
        text, shown = head.other_open, head.other_open_shown
    elif part == "other_closed":
        text, shown = "5", "Nat"
    else:
        value, value_type = VALUES[part.split(":")[1]]
        text = head.fill.format(v=value)
        shown = head.fill_shown.format(x=value_type)
    return wrap.format(p=text), wrap_type.format(t=shown)


def _site(site: str, parts: list[str]) -> tuple[str, list[int], int]:
    """The parts joined at *site*: its text, the offset of each part in it,
    and the offset of the `if` that joins the last two (an `if` of three
    parts holds the last two in its else branch)."""
    if site == "literal":
        text, offsets = _joined(parts)
        return f"[{text}]", [o + 1 for o in offsets], 0
    if site == "match":
        arms = [f"{i} -> {p}" for i, p in enumerate(parts[:-1])]
        arms.append(f"_ -> {parts[-1]}")
        text, offsets = _joined(arms)
        head = "match @Nat.0 { "
        starts = [len(head) + o + arm.index("-> ") + 3
                  for o, arm in zip(offsets, arms)]
        return f"{head}{text} }}", starts, 0
    # site == "if"
    inner_at = 0
    text = f"if @Bool.0 then {{ {parts[-2]} }} else {{ {parts[-1]} }}"
    offsets = [len("if @Bool.0 then { "),
               len(f"if @Bool.0 then {{ {parts[-2]} }} else {{ ")]
    for part in reversed(parts[:-2]):
        prefix = f"if @Bool.0 then {{ {part} }} else {{ "
        text = f"{prefix}{text} }}"
        offsets = [len("if @Bool.0 then { ")] + [len(prefix) + o
                                                 for o in offsets]
        inner_at += len(prefix)
    return text, offsets, inner_at


@dataclass(frozen=True)
class _Cell:
    site: str
    head: str
    depth: str
    filler: str
    context: str


def _refused_open_var(cell: _Cell) -> bool:
    """Whether *cell*'s context refuses the type variable its parts leave
    open, which the rule says it fills (#1682, `_Context.fills_open_var`)."""
    return (FILLERS[cell.filler].joined is None and cell.head != "array"
            and not CONTEXTS[cell.context].fills_open_var)


def _cells() -> list[_Cell]:
    return [
        _Cell(site, head, depth, filler, context)
        for site in SITES
        for head in HEADS
        for depth in DEPTHS
        for filler in FILLERS
        for context in CONTEXTS
        # A bare `array_length` gives the position no type to disagree with.
        if not (context == "bare" and filler == "ctx_disagree")
    ]


def _params() -> list[object]:
    return [
        pytest.param(cell, id=_cell_id(cell), marks=pytest.mark.xfail(
            strict=True,
            reason="#1682: a `let` or a return refuses an open type "
                   "variable"))
        if _refused_open_var(cell) else pytest.param(cell, id=_cell_id(cell))
        for cell in _cells()
    ]


def _cell_id(cell: _Cell) -> str:
    return "-".join((cell.site, cell.head, cell.depth, cell.filler,
                     cell.context))


@dataclass(frozen=True)
class _Built:
    source: str
    literal: str
    expected: list[tuple[str, int, int]]
    literal_type: str
    description: str | None


def _build(cell: _Cell) -> _Built:
    """The program of *cell*, and what the rule says the check reports."""
    head = HEADS[cell.head]
    filler = FILLERS[cell.filler]
    context = CONTEXTS[cell.context]
    wrap, wrap_type = DEPTHS[cell.depth]
    parts = [_part(head, cell.depth, p) for p in filler.parts]
    site_text, offsets, inner_at = _site(cell.site, [p for p, _ in parts])
    literal = site_text if cell.site == "literal" else f"[{site_text}]"
    shift = 0 if cell.site == "literal" else 1
    c = wrap_type.format(t=head.type.format(x=filler.context))
    body = context.body.format(lit=literal, c=c)
    params = f"@Bool, @Nat, @{c}" if context.param else "@Bool, @Nat"
    source = _fn(body, ret=context.ret.format(c=c), params=params,
                 pre=head.pre + context.pre.format(c=c))

    # The rule.  The parts' join is the first part's type, with the position
    # it leaves open given by the first later part that fills it; a part of
    # another type fills nothing and is refused.
    if filler.joined is None:
        element = wrap_type.format(t=head.open_recorded)
    else:
        element = wrap_type.format(t=head.type.format(x=filler.joined))
    expected: list[tuple[str, int, int]] = []
    description = None
    if filler.refused is not None:
        k = filler.refused
        if cell.site == "literal":
            expected.append(
                ("E162", *_place(source, literal, offsets[k])))
            shown_joined = (
                wrap_type.format(t=head.open_shown) if filler.joined is None
                else wrap_type.format(t=head.type.format(x=filler.joined)))
            provenance = "the type of element 0"
            if filler.completed_by:
                by = " and ".join(str(i) for i in filler.completed_by)
                noun = "element" if len(filler.completed_by) == 1 else (
                    "elements")
                provenance += f", completed by {noun} {by}"
            description = (
                f"Array literal element {k} has type {parts[k][1]}, but the "
                f"literal's element type is {shown_joined}, {provenance}.")
        elif cell.site == "if":
            expected.append(
                ("E301", *_place(source, literal, shift + inner_at)))
        else:
            expected.append(
                ("E302", *_place(source, literal, shift + offsets[k])))
    # The context then meets the joined type: it refuses a position the
    # parts filled with another type, and fills one they left open.
    if filler.joined not in (None, filler.context):
        assert context.code is not None
        at = context.at.format(lit=literal)
        expected.append((context.code, *_place(source, at)))
    return _Built(source, literal, expected, f"Array<{element}>",
                  description)


@pytest.mark.parametrize("cell", _params())
def test_open_position_takes_the_type_of_the_parts(cell: _Cell) -> None:
    built = _build(cell)
    checked = _checked(built.source)
    assert _where(checked) == built.expected, checked.diagnostics
    if built.description is not None:
        (diag,) = [d for d in checked.diagnostics if d.error_code == "E162"]
        assert diag.description == built.description
    assert _literal_types(checked)[_place(built.source, built.literal)] == (
        built.literal_type)


# =====================================================================
# Negative space: the context fills the position before any part does
# =====================================================================
#
# An `if` and a `match` hand the type their context expects to each branch,
# so an open branch takes the context's type before the branches are
# joined; a literal's elements are not, so its context meets the joined
# type.  Each is the nearest accepted neighbour of a refused cell above:
# the same parts with the position the context gives them.

_THREADED: dict[str, str] = {
    "if": "if @Bool.0 then {{ {a} }} else {{ {b} }}",
    "match": "match @Nat.0 {{ 0 -> {a}, _ -> {b} }}",
}


@pytest.mark.parametrize(("site", "head", "fill"), [
    (site, head, fill)
    for site in _THREADED for head in HEADS for fill in ("n", None)])
def test_context_fills_each_branch_before_the_join(
        site: str, head: str, fill: str | None) -> None:
    h = HEADS[head]
    b = h.open if fill is None else h.fill.format(v=VALUES[fill][0])
    value = _THREADED[site].format(a=h.open, b=b)
    c = h.type.format(x="Nat")
    source = _fn(f"let @{c} = {value};\n  0", pre=h.pre)
    checked = _checked(source)
    assert checked.diagnostics == ()


# =====================================================================
# Mutant killers: each fails against the mutant the test names
# =====================================================================


def test_mutant_an_element_before_the_filler_is_held_to_the_full_join(
) -> None:
    # Held to the join of the elements before it (`Option<?>`), or not held
    # at all because it precedes the element that fills the position, the
    # `5` is reported naming a type it was never compared with, or missed.
    literal = "[None, 5, Some(1)]"
    source = _fn(f"array_length({literal})")
    checked = _checked(source)
    assert _where(checked) == [("E162", *_place(source, literal, 7))]
    assert checked.errors[0].description == (
        "Array literal element 1 has type Nat, but the literal's element "
        "type is Option<Nat>, the type of element 0, completed by element 2.")


def test_mutant_each_element_is_held_to_the_join_of_every_filler() -> None:
    # Two positions, each filled by its own element: an element held to the
    # join after the first filler only still sees the second position open,
    # and the `[5]` would fit it.
    literal = '[Tuple(None, []), Tuple(Some(1), []), Tuple(None, ["a"]), ' \
        "Tuple(None, [5])]"
    source = _fn(f"array_length({literal})")
    checked = _checked(source)
    at = literal.index("Tuple(None, [5])")
    assert _where(checked) == [("E162", *_place(source, literal, at))]
    assert checked.errors[0].description == (
        "Array literal element 3 has type Tuple<Option<?>, Array<Nat>>, but "
        "the literal's element type is Tuple<Option<Nat>, Array<String>>, "
        "the type of element 0, completed by elements 1 and 2.")


def test_mutant_the_literal_is_given_the_joined_type() -> None:
    # A fold that joins the elements but gives the literal its first
    # element's type leaves the position open for the context to fill.
    literal = '[None, Some("abc")]'
    source = _fn(f"array_length({literal})")
    checked = _checked(source)
    assert checked.diagnostics == ()
    assert _literal_types(checked)[_place(source, literal)] == (
        "Array<Option<String>>")


def test_mutant_if_fills_the_else_branch_from_the_then_branch() -> None:
    # `then` a subtype of `else`: the `else` type is the result, with the
    # position it leaves open filled from `then`.
    literal = '[if @Bool.0 then { ["abc"] } else { [] }]'
    source = _fn(f"array_length({literal})")
    checked = _checked(source)
    assert checked.diagnostics == ()
    assert _literal_types(checked)[_place(source, literal)] == (
        "Array<Array<String>>")


def test_mutant_if_of_two_open_branches_is_their_join() -> None:
    literal = '[if @Bool.0 then { Ok(1) } else { Err("e") }]'
    source = _fn(f"array_length({literal})")
    checked = _checked(source)
    assert checked.diagnostics == ()
    assert _literal_types(checked)[_place(source, literal)] == (
        "Array<Result<Nat, String>>")


def test_mutant_match_arm_fills_the_earlier_arms_position() -> None:
    literal = '[match @Nat.0 { 0 -> [], _ -> ["abc"] }]'
    source = _fn(f"array_length({literal})")
    checked = _checked(source)
    assert checked.diagnostics == ()
    assert _literal_types(checked)[_place(source, literal)] == (
        "Array<Array<String>>")


def test_mutant_match_of_two_open_arms_is_their_join() -> None:
    literal = '[match @Nat.0 { 0 -> Ok(1), _ -> Err("e") }]'
    source = _fn(f"array_length({literal})")
    checked = _checked(source)
    assert checked.diagnostics == ()
    assert _literal_types(checked)[_place(source, literal)] == (
        "Array<Result<Nat, String>>")


def test_mutant_match_arm_is_held_to_an_open_earlier_arm() -> None:
    # An arm with no open position after an arm with one: the arm is the
    # join's other side, not a replacement for the earlier arms.
    literal = '[match @Nat.0 { 0 -> Err("e"), _ -> @Result<Nat, Nat>.0 }]'
    source = _fn(f"array_length({literal})",
                 params="@Bool, @Nat, @Result<Nat, Nat>")
    checked = _checked(source)
    assert _where(checked) == [
        ("E302", *_place(source, literal,
                         literal.index("@Result<Nat, Nat>.0")))]


def test_mutant_the_join_keeps_the_rigid_type_variable() -> None:
    # The enclosing function's own type parameter is not open: the join does
    # not fill it, and `Some(0)` is held to `Option<T>`.
    literal = "[Some(@T.0), None, Some(0)]"
    source = _fn(f"array_length({literal})", params="@T", generic=True)
    checked = _checked(source)
    assert _where(checked) == [
        ("E162", *_place(source, literal, literal.index("Some(0)")))]
    assert checked.errors[0].description == (
        "Array literal element 2 has type Option<Nat>, but the literal's "
        "element type is Option<T>, the type of element 0.")
