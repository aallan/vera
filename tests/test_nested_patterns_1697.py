"""A nested pattern is read to its full depth, by the exhaustiveness check and by the verifier's arm condition (#1697).

Both readers of a `match` stopped at a pattern's outer constructor.  The
check covered a data type by the constructors its arms name at the top, so
`match W(Green) { W(Red) -> 1 }` over `data Wrap { W(Colour) }` checked clean
and ran the `W(Red)` arm, and `match Some(Green) { Some(Red) -> 1, None -> 0
}` printed 0 (#1540); a tuple was not judged at all, so `match Tuple(None, 3)
{ Tuple(Some(@Int), @Int) -> @Int.0 }` printed 3.  The verifier took an arm
to be taken whenever its outer constructor matched, so `Some(None)` held of
every `Some`, the arm after it was unreachable to the proof, and `ensures(
@Int.result == 0 || @Int.result == 1)` was proved over a function that
returns 7 (#1562).

`vera/patterns.py` reads a pattern to its full depth, once, for both.  The
check judges coverage over the pattern matrix (`missing_cases`): E311 iff
some value of the scrutinee's type matches no arm, naming the cases missing
at the first position that leaves one uncovered, at the scrutinee itself by
the bare constructor as before (`None`) and inside a constructor as a
pattern (`W(Green)`, `Some(_)`, `Tuple(None, _)`).  The verifier's condition
for an arm is the conjunction of every test the pattern makes
(`patterns.tests`), each on the value its path reaches through the
constructors' accessors; a `String` literal, which no pattern condition has
modelled, leaves it inexact, and a `match` with an inexact earlier arm is not
translated (Tier 3), as one with a top-level `String` arm never was.  An
exact nested condition also gives the arm's guarded refined binders their
predicate and the walks the negation of the earlier arm.  Code generation
already tested the whole pattern and took the last arm as the default; with
coverage judged to full depth that default is sound, so it does not change.
Nested redundancy (`Some(Red)` after `Some(_)`) is not judged.

The instrument crosses the scrutinee type (`Option<Colour>`, `Wrap`,
`Option<Option<Int>>`, `Result<Option<Int>, String>`, `Option<Bool>`,
`Option<Int>`, a three-constructor `Node` with payloads to depth 3, and
`Tuple<Option<Int>, Bool>`) with the arm set (split to depth 2 complete,
each case of it missing, split to depth 3 with each depth-3 case missing,
complete through a wildcard or a binder sub-pattern, a catch-all last, a
constructor missing at the top beside a nested gap, literal sub-patterns
with and without a wildcard, and the flat sets: complete, with binders, each
constructor missing, a catch-all first) and states each cell's expectation
by rule, checked against an oracle that enumerates the type's values and
matches them against the arms with first-match semantics: E311 iff a value
matches no arm, with the cases the cell names, and no other diagnostic but
an E310 after a catch-all.  Over every exhaustive set an `ensures` that holds
on every arm proves and one that fails on a reachable arm is refuted
(violated), bar a set with a `String` literal in an earlier arm, whose
`ensures` are Tier 3; over every exhaustive set code generation compiles
(none with a literal inside a constructor, which it refuses, E602), each
value of the type runs the arm the oracle selects.  The flat sets and the
`Bool`, `Int` and `String` scrutinees are the negative space: their verdicts
and messages are base's.  The binder facts, the walks' exclusion, the
decline and each mutant's killer are unparametrised tests.
"""

from __future__ import annotations

import itertools
from dataclasses import dataclass

import pytest

from vera import ast, patterns
from tests import pipeline

# A generated class instrument (tests/matrix_sample.py): a pull request runs a
# sample of its parametrised cells, and all of them when it changes this file
# or a module that decides its class: the reading of a pattern, the check's
# coverage judgement and the verifier's arm condition.
pytestmark = pytest.mark.matrix(decides=[
    "vera/patterns.py", "vera/checker/control.py", "vera/smt.py"])


def _message(*missing: str) -> str:
    return f"Non-exhaustive match: missing patterns for {', '.join(missing)}."


def _reported(checked: pipeline.Checked) -> list[tuple[str, str, str]]:
    """Each diagnostic's code, severity and description, in order."""
    return [(d.error_code, d.severity, d.description)
            for d in checked.diagnostics]


def _ensures(verified: pipeline.Verified) -> dict[str, str]:
    """Each function's `ensures` status, by function."""
    return {o.fn_name: o.status for o in verified.obligations
            if o.kind == "ensures"}


# =====================================================================
# The reported programs
# =====================================================================

_WRAP_1540 = """private data Colour {
  Red,
  Green
}

private data Wrap {
  W(Colour)
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match W(Green) {
    W(Red) -> 1
  }
}
"""

_OPTION_1540 = """private data Colour {
  Red,
  Green
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match Some(Green) {
    Some(Red) -> 1,
    None -> 0
  }
}
"""

_NESTED_1562 = """public fn f(@Option<Option<Int>> -> @Int)
  requires(true)
  ensures(@Int.result == 0 || @Int.result == 1)
  effects(pure)
{
  match @Option<Option<Int>>.0 {
    Some(None) -> 0,
    Some(Some(@Int)) -> @Int.0,
    None -> 1
  }
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  f(Some(Some(7)))
}
"""

_TUPLE = """public fn g(@Option<Int>, @Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match Tuple(@Option<Int>.0, @Int.0) {
    Tuple(Some(@Int), @Int) -> @Int.0
  }
}
"""


def test_repro_1540_a_case_missing_inside_a_wrapper_is_e311() -> None:
    checked = pipeline.check(_WRAP_1540)
    assert _reported(checked) == [("E311", "error", _message("W(Green)"))]
    [diagnostic] = checked.diagnostics
    assert (diagnostic.location.line, diagnostic.location.column) == (15, 3)


def test_repro_1540_a_case_missing_inside_some_is_e311() -> None:
    assert _reported(pipeline.check(_OPTION_1540)) == [
        ("E311", "error", _message("Some(Green)"))]


def test_repro_1562_the_nested_ensures_is_refuted_and_the_run_agrees() -> None:
    """The `ensures` the outer-constructor reading proved is refuted, and
    the run that violates it is the counterexample's shape."""
    verified = pipeline.verify(_NESTED_1562)
    assert _ensures(verified) == {"f": "violated", "main": "verified"}
    assert [d.error_code for d in verified.errors] == ["E500"]
    ran = pipeline.run(_NESTED_1562, fn="main")
    assert ran.trap is not None and ran.trap.kind == "contract_violation"
    assert "Postcondition violation in f" in str(ran.trap)


def test_repro_a_tuple_with_a_case_missing_inside_is_e311() -> None:
    """A tuple type is judged as its one constructor, `Tuple`: the check
    judged no tuple at all, and `g(None, 3)` returned 3."""
    assert _reported(pipeline.check(_TUPLE)) == [
        ("E311", "error", _message("Tuple(None, _)"))]


def test_repro_the_e311_fix_applied_literally_checks_clean() -> None:
    """E311's fix, "Add a wildcard '_' arm", applied to the reported program
    clears it."""
    [diagnostic] = pipeline.check(_WRAP_1540).diagnostics
    assert diagnostic.fix == "Add a wildcard '_' arm or cover all cases."
    fixed = _WRAP_1540.replace("    W(Red) -> 1\n", "    W(Red) -> 1,\n    _ -> 0\n")
    assert fixed != _WRAP_1540
    assert pipeline.check(fixed).diagnostics == ()


# =====================================================================
# The model: types, patterns, values, and the oracle
# =====================================================================


@dataclass(frozen=True)
class Ty:
    """A scrutinee or field type as the instrument models it: a data type's
    constructors in declaration order, or a primitive leaf."""

    text: str
    ctors: tuple[tuple[str, tuple[Ty, ...]], ...] = ()
    leaf: str = ""


@dataclass(frozen=True)
class Pat:
    """A pattern: a constructor (``ctor``), a literal (``lit``), a wildcard
    (``any``) or a binding pattern (``bind``, *name* its type)."""

    kind: str
    name: str = ""
    subs: tuple[Pat, ...] = ()
    value: bool | int | str | None = None


@dataclass(frozen=True)
class Val:
    """A value: a constructor applied to its fields, or a literal."""

    name: str = ""
    fields: tuple[Val, ...] = ()
    value: bool | int | str | None = None


ANY = Pat("any")


def ctor(name: str, *subs: Pat) -> Pat:
    return Pat("ctor", name, subs)


def lit(value: bool | int | str) -> Pat:
    return Pat("lit", value=value)


def bind(ty: Ty) -> Pat:
    return Pat("bind", ty.text)


def _literal_text(value: bool | int | str) -> str:
    if isinstance(value, bool):
        return "true" if value else "false"
    if isinstance(value, str):
        return f'"{value}"'
    return str(value)


def src(p: Pat) -> str:
    """*p* as Vera source, and as E311 names a missing case."""
    if p.kind == "any":
        return "_"
    if p.kind == "bind":
        return f"@{p.name}"
    if p.kind == "lit":
        assert p.value is not None
        return _literal_text(p.value)
    if not p.subs:
        return p.name
    return f"{p.name}({', '.join(src(s) for s in p.subs)})"


def vsrc(v: Val) -> str:
    """*v* as a Vera expression."""
    if not v.name:
        assert v.value is not None
        return _literal_text(v.value)
    if not v.fields:
        return v.name
    return f"{v.name}({', '.join(vsrc(f) for f in v.fields)})"


INT = Ty("Int", leaf="Int")
BOOL = Ty("Bool", leaf="Bool")
STRING = Ty("String", leaf="String")
#: The literals the arm sets name, and one no arm names, which stands for
#: every value no literal arm takes.
INT_VALUES = (3, 7, 1000)
STRING_VALUES = ("a", "zz")

COLOUR = Ty("Colour", (("Red", ()), ("Green", ()), ("Blue", ())))


def option(t: Ty) -> Ty:
    return Ty(f"Option<{t.text}>", (("None", ()), ("Some", (t,))))


WRAP = Ty("Wrap", (("W", (COLOUR,)),))
NODE = Ty("Node", (("Leaf", ()), ("Unary", (option(COLOUR),)),
                   ("Binary", (COLOUR, option(COLOUR)))))
RESULT = Ty("Result<Option<Int>, String>",
            (("Ok", (option(INT),)), ("Err", (STRING,))))
TUPLE = Ty("Tuple<Option<Int>, Bool>", (("Tuple", (option(INT), BOOL)),))

#: The scrutinee types, by the id their cells carry.
TYPES: dict[str, Ty] = {
    "option_colour": option(COLOUR),
    "wrap": WRAP,
    "option_option_int": option(option(INT)),
    "result_option_int": RESULT,
    "option_bool": option(BOOL),
    "option_int": option(INT),
    "node": NODE,
    "tuple": TUPLE,
}

DECLS = """private data Colour {
  Red,
  Green,
  Blue
}

private data Wrap {
  W(Colour)
}

private data Node {
  Leaf,
  Unary(Option<Colour>),
  Binary(Colour, Option<Colour>)
}
"""


def values(t: Ty) -> list[Val]:
    """Every value of *t*, a literal leaf by its representatives."""
    if t.leaf == "Int":
        return [Val(value=v) for v in INT_VALUES]
    if t.leaf == "Bool":
        return [Val(value=True), Val(value=False)]
    if t.leaf == "String":
        return [Val(value=v) for v in STRING_VALUES]
    return [Val(name, combo) for name, fields in t.ctors
            for combo in itertools.product(*(values(f) for f in fields))]


def matches(p: Pat, v: Val) -> bool:
    """Whether *p* matches *v*: the spec's semantics, independently of the
    compiler.  A literal matches a value of its own type that equals it, so
    `true` never matches the `Int` 1."""
    if p.kind in ("any", "bind"):
        return True
    if p.kind == "lit":
        return (not v.name and type(p.value) is type(v.value)
                and p.value == v.value)
    return v.name == p.name and all(
        matches(s, f) for s, f in zip(p.subs, v.fields))


def first_arm(arms: list[Pat], v: Val) -> int | None:
    """The arm the spec selects for *v*: the first that matches it."""
    return next((i for i, p in enumerate(arms) if matches(p, v)), None)


def uncovered(arms: list[Pat], t: Ty) -> list[Val]:
    return [v for v in values(t) if first_arm(arms, v) is None]


def depth(p: Pat) -> int:
    """How deep *p*'s deepest refutable position sits: 0 for a catch-all,
    1 for a literal or a constructor with catch-alls below it."""
    if p.kind in ("any", "bind"):
        return 0
    return 1 + max((depth(s) for s in p.subs), default=0)


def expand(t: Ty, levels: int) -> list[Pat]:
    """Arms that split *t*'s values into its constructors to *levels*
    levels, `_` below: each value matched by exactly one.  `Bool` splits
    into its two literals; no set of literals splits `Int` or `String`."""
    if levels == 0:
        return [ANY]
    if t.leaf == "Bool":
        return [lit(True), lit(False)]
    if t.leaf:
        return [ANY]
    return [ctor(name, *combo) for name, fields in t.ctors
            for combo in itertools.product(
                *(expand(f, levels - 1) for f in fields))]


def binders(t: Ty) -> list[Pat]:
    """*t*'s constructors, each field a binding pattern."""
    return [ctor(name, *(bind(f) for f in fields)) for name, fields in t.ctors]


def compiles(p: Pat) -> bool:
    """Whether code generation lowers *p*: it refuses (E602) a literal
    inside a constructor and a wildcard inside a `Tuple` pattern, both
    limitations of its own, outside this class."""
    if p.kind != "ctor":
        return True
    return all(s.kind != "lit" and not (p.name == "Tuple" and s.kind == "any")
               and compiles(s) for s in p.subs)


def has_string(p: Pat) -> bool:
    if p.kind == "lit":
        return isinstance(p.value, str)
    return any(has_string(s) for s in p.subs)


# =====================================================================
# The cells
# =====================================================================


@dataclass(frozen=True)
class Cell:
    """One `match` over a type: its arms, and the cases the check names."""

    id: str
    ty: Ty
    arms: tuple[Pat, ...]
    #: The uncovered cases the check names; none when the arms cover the
    #: type.
    cases: tuple[Pat, ...] = ()
    #: An arm follows a top-level catch-all (E310).
    after_catch_all: bool = False
    #: Whether every value no arm takes is one the named cases match: not
    #: where a constructor is missing at the top beside a gap inside another,
    #: since the cases named are the first position's.
    names_every_gap: bool = True


def _named(case: Pat, arms: tuple[Pat, ...]) -> str:
    """*case* as E311 names it: a constructor no arm names at the top by
    its bare name, as the flat check named one; any other case written as a
    pattern."""
    if case.kind == "ctor" and case.name not in {
            a.name for a in arms if a.kind == "ctor"}:
        return case.name
    return src(case)


def _expected(cell: Cell) -> list[tuple[str, str, str]]:
    """What the check reports for *cell*, by rule."""
    out: list[tuple[str, str, str]] = []
    if cell.after_catch_all:
        out.append(("E310", "warning", _E310))
    if not cell.cases:
        return out
    if cell.ty.leaf == "Bool":
        # E312 names `true` before `false`, as it always has.
        missing = sorted(cell.cases, key=lambda c: not c.value)
        out.append(("E312", "error", _message(*(src(c) for c in missing))))
    elif cell.ty.leaf:
        out.append(("E313", "error", _E313))
    else:
        out.append(("E311", "error", _message(
            *sorted(_named(c, cell.arms) for c in cell.cases))))
    return out


def _without(arms: list[Pat], i: int) -> tuple[Pat, ...]:
    return tuple(arms[:i] + arms[i + 1:])


def _flat_cells(name: str, t: Ty) -> list[Cell]:
    """The negative space: arms that split *t* at the top alone."""
    top = expand(t, 1)
    cells = [Cell(f"{name}-flat-complete", t, tuple(top)),
             Cell(f"{name}-flat-binders", t, tuple(binders(t))),
             Cell(f"{name}-flat-catch-all-first", t, (ANY, top[0]),
                  after_catch_all=True)]
    if len(top) > 1:
        cells += [Cell(f"{name}-flat-missing-{p.name}", t, _without(top, i),
                       (p,))
                  for i, p in enumerate(top)]
    return cells


def _deletions(name: str, t: Ty, arms: list[Pat], at: int) -> list[Cell]:
    """*arms* with each arm of depth *at* missing whose outer constructor
    another arm still names: the missing case is that arm."""
    return [Cell(f"{name}-missing-depth-{at}-{src(p)}", t, _without(arms, i),
                 (p,))
            for i, p in enumerate(arms)
            if depth(p) == at and any(q.name == p.name
                                      for q in _without(arms, i))]


def _nested_cells(name: str, t: Ty) -> list[Cell]:
    two = expand(t, 2)
    if max(depth(p) for p in two) < 2:
        return []
    cells = [Cell(f"{name}-complete-depth-2", t, tuple(two))]
    cells += _deletions(name, t, two, 2)
    three = expand(t, 3)
    if three != two:
        cells.append(Cell(f"{name}-complete-depth-3", t, tuple(three)))
        cells += _deletions(name, t, three, 3)
    for ctor_name, fields in t.ctors:
        own = [p for p in two if p.name == ctor_name]
        if len(own) < 2:
            continue
        others = [p for p in two if p.name != ctor_name]
        # Split at depth 2 to its first case, the rest of the constructor
        # covered by a wildcard or a binder sub-pattern.
        for kind, rest in (
                ("wildcard", ctor(ctor_name, *(ANY for _ in fields))),
                ("binder", ctor(ctor_name, *(bind(f) for f in fields)))):
            cells.append(Cell(f"{name}-{ctor_name}-through-a-{kind}", t,
                              (own[0], rest, *others)))
        # This constructor's cases alone, its first missing: what is named
        # is the constructors no arm names, at the top.
        absent = tuple(ctor(n, *(ANY for _ in f)) for n, f in t.ctors
                       if n != ctor_name)
        if absent:
            cells.append(Cell(f"{name}-{ctor_name}-alone-gap-inside", t,
                              tuple(own[1:]), absent,
                              names_every_gap=False))
    deletable = _deletions(name, t, two, 2)
    if deletable:
        cells.append(Cell(f"{name}-catch-all-last", t,
                          (*deletable[0].arms, ANY)))
    return cells


#: Literal sub-patterns, with and without a wildcard beside them, and the
#: cases missing without it.
LITERAL_SETS: dict[str, list[tuple[str, tuple[Pat, ...], tuple[Pat, ...]]]] = {
    "option_int": [
        ("with-a-wildcard",
         (ctor("Some", lit(3)), ctor("Some", ANY), ctor("None")), ()),
        ("without-a-wildcard",
         (ctor("Some", lit(3)), ctor("Some", lit(7)), ctor("None")),
         (ctor("Some", ANY),)),
    ],
    "option_option_int": [
        ("with-a-wildcard",
         (ctor("Some", ctor("Some", lit(3))), ctor("Some", ctor("Some", ANY)),
          ctor("Some", ctor("None")), ctor("None")), ()),
        ("without-a-wildcard",
         (ctor("Some", ctor("Some", lit(3))), ctor("Some", ctor("None")),
          ctor("None")), (ctor("Some", ctor("Some", ANY)),)),
    ],
    "result_option_int": [
        ("with-a-wildcard",
         (ctor("Ok", ctor("Some", lit(3))), ctor("Ok", ANY),
          ctor("Err", lit("a")), ctor("Err", ANY)), ()),
        ("without-an-int-wildcard",
         (ctor("Ok", ctor("Some", lit(3))), ctor("Ok", ctor("None")),
          ctor("Err", ANY)), (ctor("Ok", ctor("Some", ANY)),)),
        ("without-a-string-wildcard",
         (ctor("Ok", ANY), ctor("Err", lit("a"))), (ctor("Err", ANY),)),
    ],
    "option_bool": [
        ("with-a-wildcard",
         (ctor("Some", lit(True)), ctor("Some", ANY), ctor("None")), ()),
        ("without-a-wildcard",
         (ctor("Some", lit(True)), ctor("None")),
         (ctor("Some", lit(False)),)),
    ],
    "tuple": [
        ("with-a-wildcard",
         (ctor("Tuple", ctor("Some", lit(3)), ANY),
          ctor("Tuple", ANY, lit(True)), ctor("Tuple", ANY, ANY)), ()),
        ("without-a-wildcard",
         (ctor("Tuple", ctor("Some", lit(3)), ANY),
          ctor("Tuple", ctor("None"), ANY)),
         (ctor("Tuple", ctor("Some", ANY), ANY),)),
    ],
}

#: The primitive scrutinees, the negative space: base's E312 and E313.
PRIMITIVE_CELLS = [
    Cell("bool-complete", BOOL, (lit(True), lit(False))),
    Cell("bool-missing-false", BOOL, (lit(True),), (lit(False),)),
    Cell("bool-missing-true", BOOL, (lit(False),), (lit(True),)),
    Cell("bool-catch-all", BOOL, (lit(True), ANY)),
    Cell("bool-catch-all-first", BOOL, (ANY, lit(True)),
         after_catch_all=True),
    Cell("int-literal-alone", INT, (lit(3),), (ANY,)),
    Cell("int-literal-and-wildcard", INT, (lit(3), ANY)),
    Cell("int-binder", INT, (bind(INT),)),
    Cell("string-literal-alone", STRING, (lit("a"),), (ANY,)),
    Cell("string-literal-and-wildcard", STRING, (lit("a"), ANY)),
]

_E310 = "Unreachable match arm: pattern after catch-all will never match."
_E313 = ("Non-exhaustive match: type has infinite domain, a wildcard '_' or "
         "binding pattern is required.")


def _cells() -> list[Cell]:
    cells: list[Cell] = []
    for name, t in TYPES.items():
        cells += _flat_cells(name, t)
        cells += _nested_cells(name, t)
        cells += [Cell(f"{name}-literal-{label}", t, arms, cases)
                  for label, arms, cases in LITERAL_SETS.get(name, [])]
    return cells + PRIMITIVE_CELLS


CELLS = _cells()
#: The sets whose arms cover their type, for the verifier and the run.
EXHAUSTIVE = [c for c in CELLS if not c.cases]


def _program(t: Ty, arms: tuple[Pat, ...], fns: list[tuple[str, str]],
             entries: tuple[Val, ...] = ()) -> str:
    """A program holding one function per (name, ensures) in *fns*, each
    the `match` over *t* with *arms*, arm i returning i; and, for each value
    in *entries*, `v<j>` returning `holds` of it."""
    body = "\n".join(
        f"    {src(p)} -> {i}{',' if i < len(arms) - 1 else ''}"
        for i, p in enumerate(arms))
    parts = [DECLS]
    for fn, ensures in fns:
        parts.append(
            f"public fn {fn}(@{t.text} -> @Int)\n"
            f"  requires(true)\n"
            f"  ensures({ensures})\n"
            f"  effects(pure)\n"
            f"{{\n"
            f"  match @{t.text}.0 {{\n{body}\n  }}\n"
            f"}}\n")
    for j, v in enumerate(entries):
        parts.append(
            f"public fn v{j}(@Unit -> @Int)\n"
            f"  requires(true)\n"
            f"  ensures(true)\n"
            f"  effects(pure)\n"
            f"{{\n"
            f"  holds({vsrc(v)})\n"
            f"}}\n")
    return "\n".join(parts)


def _id(cell: Cell) -> str:
    return cell.id


# =====================================================================
# The check: coverage to the full depth of each pattern
# =====================================================================


@pytest.mark.parametrize("cell", CELLS, ids=_id)
def test_coverage_is_judged_to_the_full_depth_of_each_pattern(
        cell: Cell) -> None:
    """E311 iff a value of the type matches no arm, naming the cell's cases
    (E312 and E313 for a primitive scrutinee, as before); an E310 after a
    catch-all; nothing else."""
    gaps = uncovered(list(cell.arms), cell.ty)
    # The premise: the cell's cases are the oracle's.  A cell names cases
    # iff some value matches no arm, each case covers a value no arm takes,
    # and the cases cover every such value, bar the first-position rule.
    assert bool(cell.cases) == bool(gaps), (cell.id, gaps)
    for case in cell.cases:
        assert any(matches(case, v) for v in gaps), (cell.id, src(case))
    if cell.names_every_gap:
        assert all(any(matches(c, v) for c in cell.cases) for v in gaps)
    checked = pipeline.check(
        _program(cell.ty, cell.arms, [("holds", "true")]))
    assert _reported(checked) == _expected(cell)


@pytest.mark.parametrize(
    "cell", [c for c in CELLS if "-missing-depth-" in c.id], ids=_id)
def test_a_deleted_case_is_exactly_what_the_arms_leave(cell: Cell) -> None:
    """The deletion cells' premise, to the value: the values no arm takes
    are the deleted case's, so it is the one case E311 can name."""
    [case] = cell.cases
    assert uncovered(list(cell.arms), cell.ty) == [
        v for v in values(cell.ty) if matches(case, v)]


# =====================================================================
# The verifier: an arm is taken under its exact condition
# =====================================================================


def _reachable(cell: Cell) -> set[int]:
    return {i for v in values(cell.ty)
            if (i := first_arm(list(cell.arms), v)) is not None}


@pytest.mark.parametrize("cell", EXHAUSTIVE, ids=_id)
def test_an_ensures_over_the_match_proves_iff_it_holds_on_every_arm(
        cell: Cell) -> None:
    """`holds` (the result is an arm's index) proves; `not_k` (the result is
    not arm k's) is refuted iff a value takes arm k, and proves where none
    does.  A `String` literal in an earlier arm is not modelled, and the
    `match` is not translated: Tier 3, never a proof."""
    n = len(cell.arms)
    fns = [("holds", f"@Int.result >= 0 && @Int.result < {n}")]
    fns += [(f"not_{k}", f"@Int.result != {k}") for k in range(n)]
    statuses = _ensures(pipeline.verify(_program(cell.ty, cell.arms, fns)))
    if any(has_string(p) for p in cell.arms[:-1]):
        assert set(statuses.values()) == {"tier3"}, statuses
        return
    reach = _reachable(cell)
    assert statuses == {
        "holds": "verified",
        **{f"not_{k}": "violated" if k in reach else "verified"
           for k in range(n)},
    }


# =====================================================================
# Code generation: the arm the spec selects runs
# =====================================================================


@pytest.mark.parametrize(
    "cell", [c for c in EXHAUSTIVE if all(compiles(p) for p in c.arms)],
    ids=_id)
def test_every_value_runs_the_arm_the_spec_selects(cell: Cell) -> None:
    """Each value of the type takes the first arm that matches it, which is
    the default code generation's last arm is sound for only because the
    check now refuses arms that leave a value uncovered."""
    every = tuple(values(cell.ty))
    compiled = pipeline.compile(
        _program(cell.ty, cell.arms, [("holds", "true")], every))
    assert compiled.ok, compiled.diagnostics
    for j, v in enumerate(every):
        assert pipeline.run(compiled, fn=f"v{j}").value == first_arm(
            list(cell.arms), v), vsrc(v)


# =====================================================================
# What an exact nested condition gives the verifier
# =====================================================================

_POS = """type Pos = { @Int | @Int.0 > 0 };

private fn need_pos(@Int -> @Int)
  requires(@Int.0 > 0)
  ensures(@Int.result > 0)
  effects(pure)
{
  @Int.0
}
"""


def _statuses(verified: pipeline.Verified, fn: str) -> list[tuple[str, str]]:
    return [(o.kind, o.status) for o in verified.obligations
            if o.fn_name == fn]


def test_named_a_nested_binder_carries_its_refinement_in_the_value() -> None:
    """`Some(Some(@Pos))`'s bind is guarded, so in its arm `@Pos.0 > 0`, and
    the `match`'s value, which carries it, proves `@Int.result > 0`.  The
    bind itself narrows an unconstrained `Int` and is refused (E505): a
    payload that is not positive traps there."""
    verified = pipeline.verify(_POS + """
public fn f(@Option<Option<Int>> -> @Int)
  requires(true)
  ensures(@Int.result > 0)
  effects(pure)
{
  match @Option<Option<Int>>.0 {
    Some(Some(@Pos)) -> @Pos.0,
    Some(None) -> 1,
    None -> 2
  }
}
""")
    assert _statuses(verified, "f") == [
        ("requires", "verified"), ("refine_bind", "violated"),
        ("ensures", "verified")]


def test_named_a_nested_binder_discharges_a_call_in_its_arm() -> None:
    verified = pipeline.verify(_POS + """
public fn f(@Option<Option<Int>> -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match @Option<Option<Int>>.0 {
    Some(Some(@Pos)) -> need_pos(@Pos.0),
    Some(None) -> 1,
    None -> 2
  }
}
""")
    assert [d.error_code for d in verified.errors] == ["E505"]
    assert ("call_pre", "violated") not in _statuses(verified, "f")


def test_named_an_inner_match_under_a_nested_arm_reaches_its_binder() -> None:
    """An inner `match`'s guarded binder needs the point the translation
    reached, which a nested outer arm now under-approximates."""
    verified = pipeline.verify(_POS + """
public fn f(@Option<Option<Int>> -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match @Option<Option<Int>>.0 {
    Some(Some(@Int)) -> match Some(@Int.0) {
      Some(@Pos) -> need_pos(@Pos.0),
      None -> 0
    },
    Some(None) -> 1,
    None -> 2
  }
}
""")
    assert [d.error_code for d in verified.errors] == ["E505"]
    assert ("call_pre", "violated") not in _statuses(verified, "f")


def test_named_a_nested_match_in_a_requires_says_what_it_says() -> None:
    """A `requires` read by its outer constructor said more than it does,
    so a caller passing `Some(None)` was refused (E501); the program
    verifies, and runs."""
    source = _POS + """
public fn guarded(@Option<Option<Int>> -> @Int)
  requires(match @Option<Option<Int>>.0 {
    Some(Some(@Int)) -> @Int.0 > 0,
    _ -> true
  })
  ensures(@Int.result > 0)
  effects(pure)
{
  match @Option<Option<Int>>.0 {
    Some(Some(@Pos)) -> need_pos(@Pos.0),
    Some(None) -> 1,
    None -> 2
  }
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  guarded(Some(Some(5))) + guarded(Some(None)) + guarded(None)
}
"""
    assert pipeline.verify(source).ok
    assert pipeline.run(source, fn="main").value == 8


def test_named_a_walk_excludes_an_earlier_nested_arm() -> None:
    """After `Some(None)`, a `Some(@Option<Int>)` arm's payload is a `Some`,
    so the inner `None` arm is unreachable and its division is safe; the
    walk, which negated no nested arm, refused it E526."""
    verified = pipeline.verify("""
public fn f(@Int, @Option<Option<Int>> -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match @Option<Option<Int>>.0 {
    Some(None) -> 0,
    Some(@Option<Int>) -> match @Option<Int>.0 {
      Some(@Int) -> @Int.0,
      None -> 100 / @Int.0
    },
    None -> 1
  }
}
""")
    assert verified.ok
    assert ("div_zero", "verified") in _statuses(verified, "f")


def test_named_the_default_arm_is_reached_by_what_no_earlier_arm_takes(
) -> None:
    """`_` after `Some(None)` takes `None` and `Some(Some(_))`: a call there
    that needs `None` is refused, for `Some(Some(5))` reaches it."""
    verified = pipeline.verify("""
private fn only_none(@Option<Option<Int>> -> @Int)
  requires(match @Option<Option<Int>>.0 {
    None -> true,
    _ -> false
  })
  ensures(true)
  effects(pure)
{
  0
}

public fn f(@Option<Option<Int>> -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match @Option<Option<Int>>.0 {
    Some(None) -> 1,
    _ -> only_none(@Option<Option<Int>>.0)
  }
}
""")
    assert [d.error_code for d in verified.errors] == ["E501"]


def test_named_a_string_inside_a_constructor_is_not_a_proof() -> None:
    """`Err("a")`'s condition was `Err`'s alone, so `Err(_)` was unreachable
    to the proof and `ensures(@Int.result != 2)` was proved, though
    `f(Err("zz"))` returns 2; no condition models a `String` literal, so
    the `match` is not translated and the `ensures` is Tier 3."""
    verified = pipeline.verify("""public fn f(@Result<Option<Int>, String> -> @Int)
  requires(true)
  ensures(@Int.result != 2)
  effects(pure)
{
  match @Result<Option<Int>, String>.0 {
    Ok(_) -> 0,
    Err("a") -> 1,
    Err(_) -> 2
  }
}
""")
    assert _ensures(verified) == {"f": "tier3"}
    assert [d.error_code for d in verified.warnings] == ["E522"]


def _generic(name: str, arms: str) -> str:
    return (f"private forall<T> fn {name}(@Option<T> -> @Int)\n"
            f"  requires(true)\n  ensures(true)\n  effects(pure)\n"
            f"{{\n  match @Option<T>.0 {{\n{arms}\n  }}\n}}\n")


def test_named_a_type_parameter_position_is_read_from_its_patterns() -> None:
    """Under `Option<T>` the field's type says nothing, so the patterns at
    it do: `None` names `Option`'s constructors, `true` `Bool`'s values, `3`
    an open domain.  `Some(None) -> 1, None -> 0` sends `Some(Some(3))` to
    the `None` arm when `T` is `Option<Int>`, and `Some(5)` when `T` is
    `Int`."""
    source = "\n".join([
        _generic("gap", "    Some(None) -> 1,\n    None -> 0"),
        _generic("complete",
                 "    Some(None) -> 1,\n    Some(Some(_)) -> 2,\n    None -> 0"),
        _generic("bools", "    Some(true) -> 1,\n    None -> 0"),
        _generic("ints", "    Some(3) -> 1,\n    None -> 0"),
        _generic("binder", "    Some(@T) -> 1,\n    None -> 0"),
    ])
    assert _reported(pipeline.check(source)) == [
        ("E311", "error", _message("Some(Some(_))")),
        ("E311", "error", _message("Some(false)")),
        ("E311", "error", _message("Some(_)")),
    ]


def test_named_a_constructor_given_too_few_sub_patterns_draws_e321_alone(
) -> None:
    """An arm whose constructor has the wrong number of sub-patterns is read
    as covering every value it builds, as the check read it before it read
    sub-patterns at all: its E321 is the one error."""
    checked = pipeline.check(DECLS + """
private data Pair {
  P(Colour, Colour)
}

private fn f(@Pair -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match @Pair.0 {
    P(Red) -> 1
  }
}
""")
    assert [(d.error_code, d.severity) for d in checked.diagnostics] == [
        ("E321", "error")]


def test_named_arms_of_another_type_leave_every_constructor_missing() -> None:
    """At the scrutinee itself the constructors no arm names are named, as
    before, even when no arm names any (each arm's E314 says why)."""
    checked = pipeline.check(_program(
        option(INT), (lit(3),), [("holds", "true")]))
    assert [(d.error_code, d.description) for d in checked.diagnostics] == [
        ("E314", "Pattern literal 3 has type Int, but the scrutinee has type "
                 "Option<Int>."),
        ("E311", _message("None", "Some")),
    ]


_REFINED = {"Option<Int>": "type Held = { @Option<Int> | true };\n",
            "Tuple<Int, Bool>": "type Held = { @Tuple<Int, Bool> | true };\n"}


@pytest.mark.parametrize(("base", "arms", "codes"), [
    ("Option<Int>", "Some(Red) -> 1,\n    Some(_) -> 2,\n    None -> 0",
     ["E314"]),
    ("Option<Int>", "Some(@Int) -> 1,\n    None -> 0", []),
    ("Option<Int>", "Some(3) -> 1,\n    None -> 0", ["E311"]),
    ("Tuple<Int, Bool>", "Tuple(Red, @Bool) -> 1,\n    Tuple(@Int, @Bool) -> 0",
     ["E314"]),
    ("Tuple<Int, Bool>", "Tuple(@Int, @Bool) -> 0", []),
], ids=["ctor-ill-typed", "ctor-binder", "ctor-gap", "tuple-ill-typed",
        "tuple-binder"])
def test_named_a_refined_scrutinee_is_read_as_its_base(
        base: str, arms: str, codes: list[str]) -> None:
    """A refinement does not change which patterns match a value (§4.9.1),
    so a constructor's or a tuple's fields are read at the base type's
    arguments for the pattern's sub-patterns as for its coverage, and a
    `match` over a refinement reports what one over its base does.  The
    sub-patterns were checked against the declaration's `T`, so `Some(Red)`
    under a refinement of `Option<Int>` was accepted."""
    def program(scrutinee: str, decl: str) -> str:
        return (DECLS + decl + f"\nprivate fn f(@{scrutinee} -> @Int)\n"
                f"  requires(true)\n  ensures(true)\n  effects(pure)\n"
                f"{{\n  match @{scrutinee}.0 {{\n    {arms}\n  }}\n}}\n")
    plain = pipeline.check(program(base, ""))
    refined = pipeline.check(program("Held", _REFINED[base]))
    assert [d.error_code for d in plain.diagnostics] == codes
    assert [(d.error_code, d.description) for d in refined.diagnostics] == [
        (d.error_code, d.description) for d in plain.diagnostics]


# =====================================================================
# The mutants' killers
# =====================================================================


def test_mutant_the_reading_descends_past_the_outer_constructor() -> None:
    """Killed: a reading that stops at depth 1 judges these arms complete."""
    assert _reported(pipeline.check(_program(
        option(option(INT)),
        (ctor("Some", ctor("None")), ctor("None")), [("holds", "true")]))) \
        == [("E311", "error", _message("Some(Some(_))"))]


def test_mutant_a_literal_sub_pattern_is_not_a_wildcard() -> None:
    """Killed: a literal read as a catch-all covers `Some` with `Some(3)`."""
    assert _reported(pipeline.check(_program(
        option(INT), (ctor("Some", lit(3)), ctor("None")),
        [("holds", "true")]))) == [("E311", "error", _message("Some(_)"))]


def test_mutant_the_missing_case_is_named_to_its_depth() -> None:
    """Killed: a case named at its outer constructor alone (`W`)."""
    assert _reported(pipeline.check(_program(
        WRAP, (ctor("W", ctor("Red")),), [("holds", "true")]))) == [
        ("E311", "error", _message("W(Blue)", "W(Green)"))]


def test_mutant_a_field_no_arm_splits_is_named_by_a_wildcard() -> None:
    """Killed: a field the arms never split, a data type's or a `Bool`'s,
    named by each of its values rather than by `_`."""
    assert _reported(pipeline.check(_program(
        NODE, (ctor("Leaf"), ctor("Unary", ANY), ctor("Binary", ctor("Red"), ANY)),
        [("holds", "true")]))) == [
        ("E311", "error", _message("Binary(Blue, _)", "Binary(Green, _)"))]
    assert _reported(pipeline.check(_program(
        TUPLE, (ctor("Tuple", ctor("Some", lit(3)), ANY),
                ctor("Tuple", ctor("None"), ANY)),
        [("holds", "true")]))) == [
        ("E311", "error", _message("Tuple(Some(_), _)"))]


# =====================================================================
# The reading itself
# =====================================================================


def test_every_pattern_form_has_a_head() -> None:
    """A pattern form the grammar grows fails here, rather than being read
    as a catch-all, which would judge the arms it leaves uncovered
    complete."""
    samples: dict[type, ast.Pattern] = {
        ast.ConstructorPattern: ast.ConstructorPattern(
            "Some", (ast.WildcardPattern(),)),
        ast.NullaryPattern: ast.NullaryPattern("None"),
        ast.BindingPattern: ast.BindingPattern(
            ast.NamedType("Int", ())),
        ast.WildcardPattern: ast.WildcardPattern(),
        ast.IntPattern: ast.IntPattern(3),
        ast.StringPattern: ast.StringPattern("a"),
        ast.BoolPattern: ast.BoolPattern(True),
    }
    forms = {cls for cls in vars(ast).values()
             if isinstance(cls, type) and issubclass(cls, ast.Pattern)
             and cls is not ast.Pattern}
    assert forms == set(samples)
    assert [patterns.head(p) for p in samples.values()] == [
        patterns.CtorHead("Some", (ast.WildcardPattern(),)),
        patterns.CtorHead("None", ()),
        None,
        None,
        patterns.LitHead("Int", 3),
        patterns.LitHead("String", "a"),
        patterns.LitHead("Bool", True),
    ]


def test_a_pattern_requires_every_test_its_positions_make() -> None:
    """`patterns.tests`, the verifier's reading: outermost first, a step
    per field, nothing for a catch-all."""
    pattern = ast.ConstructorPattern("Binary", (
        ast.NullaryPattern("Red"),
        ast.ConstructorPattern("Some", (ast.WildcardPattern(),))))
    found = patterns.tests(pattern)
    assert [(t.path, t.head) for t in found] == [
        ((), patterns.CtorHead("Binary", pattern.sub_patterns)),
        ((patterns.Step("Binary", 0),), patterns.CtorHead("Red", ())),
        ((patterns.Step("Binary", 1),),
         patterns.CtorHead("Some", (ast.WildcardPattern(),))),
    ]
    assert patterns.tests(ast.WildcardPattern()) == ()
