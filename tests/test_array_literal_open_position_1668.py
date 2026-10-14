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
(`CallsMixin._join`), a substitution: each open type variable is bound by
name, so one that occurs twice takes one type.  It does not fill a type
variable where code generation compiles behaviour for it (inside a function
type, or under a data type's parameter a constructor field holds a function
over), nor a built-in's that a parameter of its call mentions and the
arguments left unbound, and those shapes keep the verdict each site gave
them, bar a `match` arm a variable withheld for behaviour would have to take
the type of.  A built-in's variable no parameter mentions (`map_new()`'s) is
marked free at the call and filled.  A position no part fills stays open,
and the context fills it as before.

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
variable there instead (#1684), and those 162 cells are strict xfails.
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
    which meets a type variable only by name, and refuse it (#1684).
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
    open, which the rule says it fills (#1684, `_Context.fills_open_var`)."""
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
            reason="#1684: a `let` or a return refuses an open type "
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


def test_mutant_if_joins_what_re_synthesis_does_not_reach() -> None:
    # The open branch is synthesized again against the closed one, which
    # fills nothing inside a `Tuple`: held by subtyping after it, the
    # branches would be refused, though they agree once joined.
    literal = '[if @Bool.0 then { Tuple(None, -1) } else { Tuple(Some("abc"), -1) }]'
    source = _fn(f"array_length({literal})")
    checked = _checked(source)
    assert checked.diagnostics == ()
    assert _literal_types(checked)[_place(source, literal)] == (
        "Array<Tuple<Option<String>, Int>>")


def test_mutant_a_match_arm_refused_in_an_argument_is_reported_once() -> None:
    # A call argument is synthesized more than once, each time with fresh
    # type variables: a message spelling them (`Option<T$1>`, `Option<T$2>`)
    # is not the same message twice, and is reported once per synthesis.
    literal = "[match @Nat.0 { 0 -> None, _ -> 5 }]"
    source = _fn(f"takes({literal})", pre=_TAKES.format(c="Option<Nat>"))
    checked = _checked(source)
    assert _where(checked) == [
        ("E302", *_place(source, literal, literal.index("5")))]
    assert checked.errors[0].description == (
        "Match arm type Nat is incompatible with previous arm type "
        "Option<?>.")


# =====================================================================
# A variable that occurs twice, and the shapes the join does not fill
# =====================================================================
#
# The join is a substitution: a type variable is bound by name, once per
# part, so one that occurs twice takes one type, and a part that gives it
# two is refused (E162 at the element, E301 at the `if`, E302 at the arm).
#
# It does not fill a type variable where code generation compiles
# behaviour for it: inside a function type (`fn(T -> T)`, `Endo<T>`), or
# under a data type's parameter that a constructor field holds a function
# over (`Box<T>`).  Code generation finds a generic call's instantiation
# from its arguments and the type it is expected at, never from a join, so
# it compiles `mk(())` at a default of its own (`$mk$Bool`), and a closure
# the join called `fn(Nat -> Nat)` would be called with an `@Nat` it was
# not compiled for.  Nor does it fill a built-in's type variable that a
# parameter of the call mentions and the arguments left unbound: that one
# stands for a type a failed substitution lost (`map_values` read through
# a refinement alias, whose values here are `Int`, #1688).  A built-in's
# variable no parameter mentions is one no argument could fix
# (`map_new()`'s `K` and `V`): the call marks it free, an open position as
# a constructor's type parameter no field holds is, and the join fills it.  For the
# shapes the join leaves, each site keeps the verdict it gave before: the
# literal holds each element to the element type one
# position at a time and keeps its first element's type; an `if`
# synthesizes the open branch again against the other, which fixes a call
# whose result is a data type (`mkbox(())`, `map_new()`) where it is
# checked and does not fix one whose result is a function (`mk(())`), and
# refuses what still differs (E301); a `match` arm after an open arm takes
# the arm's type where the variable is a built-in's and the argument
# judgement admits it.  A variable withheld for behaviour is refused at the
# arm (E302): a `match` cannot synthesize its earlier arms again, and
# f3b4415d took the arm's type without comparing the two, so the program
# ran with the closure called at a type it was not compiled for.

_SHAPES_PRE = """type Endo<T> = fn(T -> T) effects(pure);
type M = { @Map<String, Int> | map_size(@Map<String, Int>.0) >= 0 };
private data Box<T> { MkBox(fn(T -> T) effects(pure)) }
private data Pair<T> { P(T, T) }

private forall<T> fn mk(@Unit -> @Endo<T>)
  requires(true)
  ensures(true)
  effects(pure)
{
  fn(@T -> @T) effects(pure) { @T.0 }
}

private forall<T> fn mkf(@Unit -> @fn(T -> T) effects(pure))
  requires(true)
  ensures(true)
  effects(pure)
{
  fn(@T -> @T) effects(pure) { @T.0 }
}

private forall<T> fn mkbox(@Unit -> @Box<T>)
  requires(true)
  ensures(true)
  effects(pure)
{
  MkBox(fn(@T -> @T) effects(pure) { @T.0 })
}

private forall<T> fn twice(@Option<T> -> @Tuple<Option<T>, Option<T>>)
  requires(true)
  ensures(true)
  effects(pure)
{
  Tuple(@Option<T>.0, @Option<T>.0)
}

private forall<T> fn dup(@Option<T> -> @Tuple<Array<T>, Array<T>>)
  requires(true)
  ensures(true)
  effects(pure)
{
  Tuple([], [])
}
"""


@dataclass(frozen=True)
class _Shape:
    """Parts whose open variable occurs twice, or that the join does not
    fill.  *expect* maps each site to the part it refuses there (None for
    none) and the type the parts are recorded with where it refuses none."""

    parts: tuple[str, ...]
    expect: dict[str, tuple[int | None, str | None]]
    description: str | None = None


def _everywhere(refused: int | None, element: str | None,
                ) -> dict[str, tuple[int | None, str | None]]:
    return {site: (refused, element) for site in SITES}


_NAT_ID = "fn(@Nat -> @Nat) effects(pure) { @Nat.0 }"
_NAT_STR = 'fn(@Nat -> @String) effects(pure) { "x" }'

SHAPES: dict[str, _Shape] = {
    # The substitution: one variable, one type.
    "tuple-agree": _Shape(
        ("twice(None)", "Tuple(Some(1), Some(2))"),
        _everywhere(None, "Tuple<Option<Nat>, Option<Nat>>")),
    "tuple-disagree": _Shape(
        ("twice(None)", 'Tuple(Some(1), Some("a"))'),
        # The `if` synthesizes `twice(None)` again against the other
        # branch's type, which the call takes position by position
        # (f3b4415d's verdict, before any join is reached).
        {"literal": (1, "Tuple<Option<T$>, Option<T$>>"),
         "if": (None, "Tuple<Option<Nat>, Option<String>>"),
         "match": (1, None)},
        description=(
            "Array literal element 1 has type Tuple<Option<Nat>, "
            "Option<String>>, but the literal's element type is "
            "Tuple<Option<?>, Option<?>>, the type of element 0.")),
    "pair-agree": _Shape(
        ("P(None, None)", "P(Some(1), Some(2))"),
        _everywhere(None, "Pair<Option<Nat>>")),
    "pair-disagree": _Shape(
        ("P(None, None)", "P(Some(1), Some(2))", 'P(Some("a"), Some("b"))'),
        {"literal": (2, "Pair<Option<Nat>>"), "if": (2, None),
         "match": (2, None)},
        description=(
            "Array literal element 2 has type Pair<Option<String>>, but the "
            "literal's element type is Pair<Option<Nat>>, the type of "
            "element 0, completed by element 1.")),
    # One part's variable at two positions, one of them where the joined
    # type is still unknown: the binding holds at both.  An `if` and a
    # `match` synthesize `dup(None)` again against the other part's type,
    # which the call takes position by position (#1684), base's verdict.
    "dup-agree": _Shape(
        ("Tuple([1], [])", "dup(None)", "Tuple([2], [3])"),
        _everywhere(None, "Tuple<Array<Nat>, Array<Nat>>")),
    "dup-disagree": _Shape(
        ("Tuple([1], [])", "dup(None)", 'Tuple([2], ["s"])'),
        {"literal": (2, "Tuple<Array<Nat>, Array<Nat>>"),
         "if": (None, "Tuple<Array<Nat>, Array<String>>"),
         "match": (None, "Tuple<Array<Nat>, Array<String>>")},
        description=(
            "Array literal element 2 has type Tuple<Array<Nat>, "
            "Array<String>>, but the literal's element type is "
            "Tuple<Array<Nat>, Array<Nat>>, the type of element 0, completed "
            "by element 1.")),
    # Withheld for behaviour: not filled; refused at an `if` or a `match`.
    "fn-agree": _Shape(
        ("mkf(())", _NAT_ID),
        {"literal": (None, "fn(T -> T) effects(pure)"),
         "if": (1, None), "match": (1, None)}),
    "fn-disagree": _Shape(
        ("mkf(())", _NAT_STR),
        {"literal": (None, "fn(T -> T) effects(pure)"),
         "if": (1, None), "match": (1, None)}),
    "endo-agree": _Shape(
        ("mk(())", _NAT_ID),
        {"literal": (None, "fn(T -> T) effects(pure)"),
         "if": (1, None), "match": (1, None)}),
    "endo-disagree": _Shape(
        ("mk(())", _NAT_STR),
        {"literal": (None, "fn(T -> T) effects(pure)"),
         "if": (1, None), "match": (1, None)}),
    # The `if` synthesizes `mkbox(())` again against the other branch's
    # type, which fixes the call's instantiation where it is checked.
    "box-agree": _Shape(
        ("mkbox(())", f"MkBox({_NAT_ID})"),
        {"literal": (None, "Box<T>"), "if": (None, "Box<Nat>"),
         "match": (1, None)}),
    "box-disagree": _Shape(
        ("mkbox(())",
         "MkBox(fn(@String -> @String) effects(pure) { @String.0 })"),
        {"literal": (None, "Box<T>"), "if": (None, "Box<String>"),
         "match": (1, None)}),
    # A built-in's variable: each site's verdict as before.
    "leak-agree": _Shape(
        ("map_values(@M.0)[0]", "0 - 5"),
        {"literal": (None, "V"), "if": (1, None), "match": (None, "Int")}),
    "leak-disagree": _Shape(
        ("map_values(@M.0)[0]", '"s"'),
        {"literal": (None, "V"), "if": (1, None), "match": (None, "String")}),
    # A built-in's variable no parameter mentions is fresh: filled.
    "map-agree": _Shape(
        ("map_new()", 'map_insert(map_new(), "k", 1)'),
        _everywhere(None, "Map<String, Nat>")),
    "map-disagree": _Shape(
        ("map_new()", 'map_insert(map_new(), "k", 1)',
         'map_insert(map_new(), 5, "v")'),
        {"literal": (2, "Map<String, Nat>"), "if": (2, None),
         "match": (2, None)},
        description=(
            "Array literal element 2 has type Map<Nat, String>, but the "
            "literal's element type is Map<String, Nat>, the type of "
            "element 0, completed by element 1.")),
    "set-agree": _Shape(
        ("set_new()", "set_add(set_new(), 5)"),
        _everywhere(None, "Set<Nat>")),
    "set-disagree": _Shape(
        ("set_new()", "set_add(set_new(), 5)", 'set_add(set_new(), "s")'),
        {"literal": (2, "Set<Nat>"), "if": (2, None), "match": (2, None)},
        description=(
            "Array literal element 2 has type Set<String>, but the literal's "
            "element type is Set<Nat>, the type of element 0, completed by "
            "element 1.")),
}


@pytest.mark.parametrize(
    ("shape", "site"), [(shape, site) for shape in SHAPES for site in SITES])
def test_shape_the_join_binds_once_or_leaves(shape: str, site: str) -> None:
    spec = SHAPES[shape]
    refused, element = spec.expect[site]
    site_text, offsets, inner_at = _site(site, list(spec.parts))
    literal = site_text if site == "literal" else f"[{site_text}]"
    shift = 0 if site == "literal" else 1
    source = _fn(f"array_length({literal})", params="@M, @Bool, @Nat",
                 pre=_SHAPES_PRE)
    checked = _checked(source)
    expected: list[tuple[str, int, int]] = []
    if refused is not None:
        if site == "literal":
            expected.append(("E162", *_place(source, literal,
                                             offsets[refused])))
        elif site == "if":
            at = inner_at if refused == len(spec.parts) - 1 else 0
            expected.append(("E301", *_place(source, literal, shift + at)))
        else:
            expected.append(("E302", *_place(source, literal,
                                             shift + offsets[refused])))
    assert _where(checked) == expected, checked.diagnostics
    if site == "literal" and spec.description is not None:
        assert checked.errors[0].description == spec.description
    if element is not None:
        assert _literal_types(checked)[_place(source, literal)] == (
            f"Array<{element}>")


# The two programs refused at check and never run: R69's, where the join
# gave the identity closure `mk(())` the type `fn(Option<Nat> ->
# Option<String>)` and `vera run` read a `Nat` as a `String`, and one whose
# closure agrees with `mk(())` at `fn(Nat -> Nat)` and which, compiled at
# `mk`'s default, trapped with an indirect call type mismatch.

_CONV_PROGRAM = """type Conv = fn(Option<Nat> -> Option<String>) effects(pure);
type Endo<T> = fn(T -> T) effects(pure);

private forall<T> fn mk(@Unit -> @Endo<T>)
  requires(true)
  ensures(true)
  effects(pure)
{
  fn(@T -> @T) effects(pure) { @T.0 }
}

public fn main(@Unit -> @Unit)
  requires(true)
  ensures(true)
  effects(<IO>)
{
  let @Conv = if true then { mk(()) } else { fn(@Option<Nat> -> @Option<String>) effects(pure) { None } };
  match apply_fn(@Conv.0, Some(0)) {
    Some(@String) -> IO.print(string_concat("[", string_concat(@String.0, "]"))),
    None -> IO.print("none")
  }
}
"""

_AGREEING_PROGRAM = """type NatToNat = fn(Nat -> Nat) effects(pure);
type Endo<T> = fn(T -> T) effects(pure);

private forall<T> fn mk(@Unit -> @Endo<T>)
  requires(true)
  ensures(true)
  effects(pure)
{
  fn(@T -> @T) effects(pure) { @T.0 }
}

public fn main(@Unit -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @NatToNat = if true then { mk(()) } else { fn(@Nat -> @Nat) effects(pure) { @Nat.0 } };
  apply_fn(@NatToNat.0, 5)
}
"""


@pytest.mark.parametrize("program", [_CONV_PROGRAM, _AGREEING_PROGRAM],
                         ids=["conv", "agreeing"])
def test_run_closure_the_join_cannot_type_is_refused_before_it_runs(
        program: str) -> None:
    ran = pipeline.run(program)
    assert ran.module is None
    assert ran.compiled is not None and ran.compiled.checked is not None
    checked = ran.compiled.checked
    line = next(text for text in program.splitlines()
                if "let @" in text and "mk(())" in text)
    assert [d.error_code for d in checked.errors] == ["E301", "E170"]
    assert checked.errors[0].location.line == (
        program.splitlines().index(line) + 1)


def _shape_source(body: str) -> str:
    return _fn(body, params="@M, @Bool, @Nat", pre=_SHAPES_PRE)


def test_mutant_a_variable_that_occurs_twice_takes_one_type() -> None:
    # Filled one position at a time, `twice(None)`'s one `T` would take
    # `Nat` and `String`, the type of neither element.
    literal = '[twice(None), Tuple(Some(1), Some("a"))]'
    source = _shape_source(f"array_length({literal})")
    checked = _checked(source)
    assert _where(checked) == [
        ("E162", *_place(source, literal, literal.index("Tuple(Some")))]


def test_mutant_a_data_field_holding_a_function_keeps_its_variable() -> None:
    # `Box<T>` holds `fn(T -> T)` in its field: filled from the later arm,
    # the box `mkbox(())` built at its own default would be called as a
    # box of `Nat`.
    literal = ("[match @Nat.0 { 0 -> mkbox(()), _ -> "
               f"MkBox({_NAT_ID}) }}]")
    source = _shape_source(f"array_length({literal})")
    checked = _checked(source)
    assert _where(checked) == [
        ("E302", *_place(source, literal, literal.index("MkBox(")))]


def test_mutant_a_lost_builtin_variable_is_not_filled() -> None:
    # `map_values`'s `V` is a parameter's, left unbound through the
    # refinement alias (#1688): the literal keeps it, as it did before the
    # join.
    literal = "[map_values(@M.0)[0], 0 - 5]"
    source = _shape_source(f"array_length({literal})")
    checked = _checked(source)
    assert checked.diagnostics == ()
    assert _literal_types(checked)[_place(source, literal)] == "Array<V>"


def test_mutant_a_fresh_builtin_variable_is_filled() -> None:
    # `map_new()`'s `K` and `V` are mentioned by no parameter: the later
    # element fills them, and the context meets the joined type.
    literal = '[map_new(), map_insert(map_new(), "k", 1)]'
    source = _shape_source(f"takes({literal})") .replace(
        "\nprivate data Box", _TAKES.format(c="Map<Nat, String>")
        + "\nprivate data Box", 1)
    checked = _checked(source)
    assert _where(checked) == [("E202", *_place(source, literal))]
    assert _literal_types(checked)[_place(source, literal)] == (
        "Array<Map<String, Nat>>")


def test_mutant_a_lost_builtin_variable_keeps_the_match_verdict() -> None:
    # A `match` cannot synthesize its earlier arms again: an arm after a
    # lost variable gives the match its type, as it did before the join.
    literal = "[match @Nat.0 { 0 -> map_values(@M.0)[0], _ -> 0 - 5 }]"
    source = _shape_source(f"array_length({literal})")
    checked = _checked(source)
    assert checked.diagnostics == ()
    assert _literal_types(checked)[_place(source, literal)] == "Array<Int>"


# A fresh built-in variable meets a context that disagrees with the type
# the later element gives it: refused where the context holds the literal
# (E202), at every site.

_FRESH_CONTEXT_PARTS = ("map_new()", 'map_insert(map_new(), "k", 1)')


@pytest.mark.parametrize("site", SITES)
def test_fresh_builtin_variable_meets_its_context(site: str) -> None:
    site_text, _offsets, _inner = _site(site, list(_FRESH_CONTEXT_PARTS))
    literal = site_text if site == "literal" else f"[{site_text}]"
    source = _fn(f"takes({literal})", params="@M, @Bool, @Nat",
                 pre=_SHAPES_PRE + _TAKES.format(c="Map<Nat, String>"))
    checked = _checked(source)
    assert _where(checked) == [("E202", *_place(source, literal))]
    assert _literal_types(checked)[_place(source, literal)] == (
        "Array<Map<String, Nat>>")


# R69's two programs for the fresh built-in variable, refused at check and
# never run: two later elements that give `map_new()`'s variables
# different types, and a context that gives them a third, which f3b4415d
# ran with a map's `1` read as a `String`.

_FRESH_DISAGREE_PROGRAM = """public fn main(@Unit -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  array_length([map_new(), map_insert(map_new(), "k", 1), map_insert(map_new(), 5, "v")])
}
"""

_FRESH_CONTEXT_PROGRAM = """private fn show_value(@Array<Map<Nat, String>> -> @String)
  requires(array_length(@Array<Map<Nat, String>>.0) > 1)
  ensures(true)
  effects(pure)
{
  let @Array<String> = map_values(@Array<Map<Nat, String>>.0[1]);
  if array_length(@Array<String>.0) > 0 then { @Array<String>.0[0] } else { "none" }
}

public fn main(@Unit -> @Unit)
  requires(true)
  ensures(true)
  effects(<IO>)
{
  IO.print(string_concat("[", string_concat(show_value([map_new(), map_insert(map_new(), "k", 1)]), "]")))
}
"""


@pytest.mark.parametrize(("program", "code"), [
    (_FRESH_DISAGREE_PROGRAM, "E162"), (_FRESH_CONTEXT_PROGRAM, "E202")],
    ids=["disagree", "context"])
def test_run_fresh_builtin_variable_is_refused_before_it_runs(
        program: str, code: str) -> None:
    ran = pipeline.run(program)
    assert ran.module is None
    assert ran.compiled is not None and ran.compiled.checked is not None
    assert [d.error_code for d in ran.compiled.checked.errors] == [code]


def test_mutant_a_free_builtin_variable_displays_as_the_builtins() -> None:
    # The free mark is the join's, not the reader's: a literal nothing
    # fills shows `map_new()`'s variables as the built-in names them.
    literal = "[map_new(), map_new()]"
    source = _shape_source(f"array_length({literal})")
    checked = _checked(source)
    assert checked.diagnostics == ()
    assert _literal_types(checked)[_place(source, literal)] == (
        "Array<Map<K, V>>")


def test_mutant_each_call_marks_its_own_free_variables() -> None:
    # Two calls of `map_new()` leave two maps' variables: one name for both
    # would bind the first map's key type to the second's.
    literal = ("[Tuple(map_new(), map_new()), "
               'Tuple(map_insert(map_new(), "k", 1), '
               'map_insert(map_new(), 1, "v"))]')
    source = _shape_source(f"array_length({literal})")
    checked = _checked(source)
    assert checked.diagnostics == ()
    assert _literal_types(checked)[_place(source, literal)] == (
        "Array<Tuple<Map<String, Nat>, Map<Nat, String>>>")


# A data parameter a constructor field holds only in a function's effect
# row is held for behaviour too: the closure `mkcell(())` stores is
# compiled at `mkcell`'s default, its `State` cell with it.  Each site keeps
# f3b4415d's verdict, bar the `match`, which refuses the arm (E302) where
# f3b4415d took its type unchecked.

_CELL_PRE = """private data Cell<T> { MkCell(fn(Unit -> Unit) effects(<State<T>>)) }

private forall<T> fn mkcell(@Unit -> @Cell<T>)
  requires(true)
  ensures(true)
  effects(pure)
{
  MkCell(fn(@Unit -> @Unit) effects(<State<T>>) { () })
}
"""

_CELL_EXPECT: dict[str, tuple[int | None, str]] = {
    # The `if` synthesizes `mkcell(())` again against the other branch's
    # type, which fixes the call where it is checked (f3b4415d's verdict).
    "literal": (None, "Array<Cell<T>>"),
    "if": (None, "Array<Cell<Nat>>"),
    "match": (1, ""),
}


@pytest.mark.parametrize("site", SITES)
def test_effect_row_holds_its_variable(site: str) -> None:
    refused, literal_type = _CELL_EXPECT[site]
    site_text, offsets, _inner = _site(site, ["mkcell(())", "@Cell<Nat>.0"])
    literal = site_text if site == "literal" else f"[{site_text}]"
    source = _fn(f"array_length({literal})", params="@Cell<Nat>, @Bool, @Nat",
                 pre=_CELL_PRE)
    checked = _checked(source)
    if refused is None:
        assert checked.diagnostics == ()
        assert _literal_types(checked)[_place(source, literal)] == literal_type
    else:
        assert _where(checked) == [
            ("E302", *_place(source, literal, 1 + offsets[refused]))]


def test_mutant_an_effect_row_holds_behaviour() -> None:
    # Read without its effect row, `Cell<T>` holds no behaviour, and the
    # join would give `mkcell(())`'s cell the type `Cell<Nat>`.
    literal = "[mkcell(()), @Cell<Nat>.0]"
    source = _fn(f"array_length({literal})", params="@Cell<Nat>, @Nat",
                 pre=_CELL_PRE)
    checked = _checked(source)
    assert checked.diagnostics == ()
    assert _literal_types(checked)[_place(source, literal)] == (
        "Array<Cell<T>>")


def test_mutant_a_variable_bound_on_the_part_side_takes_one_type() -> None:
    # `dup(None)`'s one `T` meets `Nat` where element 0 fixes it and `?`
    # where element 0 leaves its second array open: kept at the second
    # position without its binding, the third element would give it
    # `String` there.
    literal = '[Tuple([1], []), dup(None), Tuple([2], ["s"])]'
    source = _shape_source(f"array_length({literal})")
    checked = _checked(source)
    assert _where(checked) == [
        ("E162", *_place(source, literal, literal.index('Tuple([2]')))]
    assert checked.errors[0].description == (
        "Array literal element 2 has type Tuple<Array<Nat>, Array<String>>, "
        "but the literal's element type is Tuple<Array<Nat>, Array<Nat>>, "
        "the type of element 0, completed by element 1.")
