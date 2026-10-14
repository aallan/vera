"""A `match` over a scrutinee already in error is not judged for coverage (#1671).

The checker types an expression it has refused as `Unknown`, which is
neither a data type nor `Bool`, so `_check_exhaustiveness` reached its
infinite-domain arm and reported the `match` E313 ("type has infinite
domain"), however completely its arms covered the type the scrutinee was
written to have: `match @Option<Int>.0 { Some(@Int) -> @Int.0, None -> 0 }`
with no `Option<Int>` binding in scope was reported E130 at the reference
and then E313 at the `match`.

The rule: a scrutinee typed `Unknown`, refinements stripped, after the check
has reported an error is not judged for exhaustiveness (spec §4.9.2).  The
judgements that read only the arms still run: an arm after a catch-all is
still reported (E310, §4.9.3), and the arms' patterns and bodies are still
checked, so an error inside an arm is still reported.  The pattern-fit rule
(E314, §4.9.1) already withholds itself from an `Unknown` scrutinee and is
unchanged.  An `Unknown` scrutinee with no error reported (`apply_fn` over a
type variable) is judged as before, so the one error that refuses such a
program stays.  The skip is keyed on the type, never on a list of codes, and
every error the module has reported by the time the scrutinee is typed
counts, since the error behind an `Unknown` can sit at a declaration (E158)
or an import (E155): an `Unknown` with no error of its own beside an earlier,
unrelated error is not judged until that error is fixed.

The class is every `match` whose scrutinee is typed `Unknown` after an
error.  The instrument crosses how the scrutinee came to be in error (an
unresolved slot E130, an undefined call E200, a result reference naming
another type E163, a result reference outside a postcondition E131, an
undefined constructor E210, an index into a value that is no collection
E161, the slot inside a block, both branches of an `if` in error, a block
whose `let` declares the removed alias `Float`, an error with no code, and
the constructor of a declaration refused as E158, its error placed at the
declaration) with the arm shape (constructor arms complete and incomplete,
a literal nested in a constructor, literal arms with and without a
wildcard, `true`/`false` and `true` alone, a wildcard alone, an arm after a
wildcard, patterns of another type, an error inside an arm) and where the
`match` is written (a function body, an `ensures`, a `where` helper's body).
Each such `match` reports exactly its scrutinee's codes, then what its arms
report whatever the scrutinee.  The negative space holds the same arm
shapes over the same scrutinee written correctly, each keeping its verdict
(E311, E312, E313, E314 and E310 where the arms draw them, and a clean check
with every obligation verified where they do not); over a scrutinee whose
error leaves it a type (a call with the wrong arity, a `let` whose
initialiser is in error, an `if` with one branch in error), judged as
before; and over an `Unknown` scrutinee with no error reported, judged as
before.  The call two imports supply (E155), the module-wide count and each
mechanism's edge are pinned by unparametrised tests.
"""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path

import pytest

from tests import pipeline

# A generated class instrument (tests/matrix_sample.py): a pull request runs a
# sample of its parametrised cells, and all of them when it changes this file
# or the module that decides its class, the checker's judgement of a match.
pytestmark = pytest.mark.matrix(decides=["vera/checker/control.py"])


# =====================================================================
# Helpers
# =====================================================================

#: A diagnostic as the instrument compares it: its code ("" for one that
#: carries none) and its severity.
Report = tuple[str, str]


def _report(checked: pipeline.Checked) -> list[Report]:
    """The check's diagnostics, in the order it reports them."""
    return [(d.error_code, d.severity) for d in checked.diagnostics]


def _errors(*codes: str) -> list[Report]:
    return [(code, "error") for code in codes]


def _place(source: str, text: str) -> tuple[int, int]:
    """The 1-based line and column of the one occurrence of *text*."""
    assert source.count(text) == 1, text
    at = source.index(text)
    return (source.count("\n", 0, at) + 1,
            at - (source.rfind("\n", 0, at) + 1) + 1)


def _at(checked: pipeline.Checked) -> list[tuple[str, int, int]]:
    """Each diagnostic's code and where it is placed."""
    return [(d.error_code, d.location.line, d.location.column)
            for d in checked.diagnostics]


# =====================================================================
# The reported programs
# =====================================================================

_ISSUE = """public fn f(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{{
  match {scrutinee} {{
    {arms}
  }}
}}
"""


def _reported_once(scrutinee: str, arms: str, code: str) -> None:
    """The issue's program over *scrutinee* reports *code* at the
    scrutinee, and nothing else."""
    source = _ISSUE.format(scrutinee=scrutinee, arms=arms)
    checked = pipeline.check(source)
    assert _at(checked) == [(code, *_place(source, scrutinee))], (
        checked.diagnostics)


def test_repro_an_unresolved_slot_is_reported_once() -> None:
    _reported_once("@Option<Int>.0", "Some(@Int) -> @Int.0,\n    None -> 0",
                   "E130")


def test_repro_an_undefined_call_is_reported_once() -> None:
    _reported_once("nope(@Int.0)", "Some(@Int) -> @Int.0,\n    None -> 0",
                   "E200")


def test_repro_an_unresolved_bool_slot_is_reported_once() -> None:
    _reported_once("@Bool.0", "true -> 1,\n    false -> 0", "E130")


def test_repro_a_refused_result_reference_is_reported_once() -> None:
    """The issue's E163 instance: the result reference #1517's fix refuses
    types as `Unknown` too."""
    ref = "@Tuple<String, Int>.result"
    source = f"""public fn f(@Int, @String -> @Tuple<Int, String>)
  requires(true)
  ensures(match {ref} {{ Tuple(@Int, @String) -> @Int.0 == @Int.1 }})
  effects(pure)
{{
  Tuple(@Int.0, @String.0)
}}
"""
    checked = pipeline.check(source)
    assert _at(checked) == [("E163", *_place(source, ref))], (
        checked.diagnostics)


# =====================================================================
# The rule's edges, one per mechanism (each kills a documented mutant)
# =====================================================================


def test_a_match_over_a_well_typed_scrutinee_is_still_judged() -> None:
    """Coverage is judged wherever the scrutinee has a type: E311 for a
    missing constructor, E312 for a missing `Bool`, E313 for an infinite
    domain without a catch-all."""
    for arms, code in (("Some(@Int) -> 1", "E311"),
                       ("true -> 1", "E312"),
                       ("1 -> 1", "E313")):
        scrutinee = {"E311": "@Option<Int>.0", "E312": "@Bool.0",
                     "E313": "@Int.0"}[code]
        source = f"""public fn f(@Option<Int>, @Bool, @Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{{
  match {scrutinee} {{
    {arms}
  }}
}}
"""
        assert _report(pipeline.check(source)) == _errors(code), arms


def test_an_error_inside_an_arm_is_still_reported() -> None:
    """The arms of a match over a scrutinee in error are still checked."""
    source = _ISSUE.format(
        scrutinee="@Option<Int>.0",
        arms="Some(@Int) -> @String.0,\n    None -> 0")
    checked = pipeline.check(source)
    assert _at(checked) == [
        ("E130", *_place(source, "@Option<Int>.0")),
        ("E130", *_place(source, "@String.0")),
    ], checked.diagnostics


def test_an_arm_after_a_wildcard_is_still_reported() -> None:
    """The redundancy check reads the arms alone, so it stands over a
    scrutinee in error as over any other."""
    source = _ISSUE.format(scrutinee="@Option<Int>.0",
                           arms="_ -> 0,\n    None -> 1")
    assert _report(pipeline.check(source)) == [
        ("E130", "error"), ("E310", "warning")]


_GENERIC = """private forall<T> fn g(@T -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{{
  match apply_fn(@T.0, 1) {{
    {arms}
  }}
}}
"""


def test_an_unknown_scrutinee_with_no_error_reported_is_still_judged() -> None:
    """`apply_fn` over a type variable is `Unknown` with no error reported,
    and the E313 its `match` draws is the one error that refuses the
    program: without it, the program passes check and code generation
    refuses it."""
    source = _GENERIC.format(arms="Some(@Int) -> @Int.0,\n    None -> 0")
    assert _report(pipeline.check(source)) == _errors("E313")


def test_an_error_after_the_scrutinee_does_not_count() -> None:
    """Whether the scrutinee is in error is read once it is typed: an error
    inside an arm says nothing about it."""
    source = _GENERIC.format(arms="Some(@Int) -> @String.0,\n    None -> 0")
    assert _report(pipeline.check(source)) == _errors("E130", "E313")


_UNRELATED = """public fn h(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{{
  {body}
}}

"""


def test_an_unrelated_error_withholds_the_judgement_of_an_unknown() -> None:
    """The rule counts every error the module has reported by the time the
    scrutinee is typed, not only those raised while typing it, because the
    error behind an `Unknown` can sit elsewhere (E158 at a declaration,
    E155 at an import).  So an `Unknown` with no error of its own beside an
    earlier, unrelated error is not judged: the program is refused by that
    error alone, and the E313 returns once it is fixed.  An error reported
    after the scrutinee is typed does not count."""
    generic = _GENERIC.format(arms="Some(@Int) -> @Int.0,\n    None -> 0")
    broken = _UNRELATED.format(body="@Int.1")
    fixed = _UNRELATED.format(body="@Int.0")
    checked = pipeline.check(broken + generic)
    assert _at(checked) == [("E130", *_place(broken + generic, "@Int.1"))]
    assert not checked.ok
    assert _report(pipeline.check(fixed + generic)) == _errors("E313")
    assert _report(pipeline.check(generic + "\n" + broken)) == _errors(
        "E313", "E130")


def test_a_call_two_imports_supply_is_reported_at_the_import_alone(
        tmp_path: Path) -> None:
    """The name two imports supply denotes neither declaration, so the call
    is typed `Unknown` and its one error, E155, is placed at the import."""
    module = """module {name};

public fn pick(@Int -> @Option<Int>)
  requires(true)
  ensures(true)
  effects(pure)
{{
  Some(@Int.0)
}}
"""
    main = """import a(pick);
import b(pick);

public fn f(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match pick(@Int.0) {
    Some(@Int) -> @Int.0,
    None -> 0
  }
}
"""
    entry = pipeline.write_tree(tmp_path, {
        "a.vera": module.format(name="a"), "b.vera": module.format(name="b"),
        "main.vera": main})
    checked = pipeline.check(entry, root=tmp_path)
    assert _at(checked) == [("E155", *_place(main, "import b"))], (
        checked.diagnostics)


def test_a_refinement_of_a_type_in_error_is_not_judged() -> None:
    """`@{ @Float | true }` resolves to a refinement over `Unknown`, its
    error, which carries no code, reported at the signature."""
    source = """public fn f(@{ @Float | true } -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match @Float.0 {
    Some(@Int) -> 1,
    None -> 0
  }
}
"""
    checked = pipeline.check(source)
    assert _at(checked) == [("", *_place(source, "Float |"))], (
        checked.diagnostics)


# =====================================================================
# The class
# =====================================================================

#: The types a scrutinee is written to have.
_TYPES = {"opt": "Option<Int>", "bool": "Bool", "int": "Int"}


@dataclass(frozen=True)
class Shape:
    """A match's arms, over a scrutinee written to have the type *ty*.

    *arms* writes each arm's value as ``{v}``.  *verdict* is what the check
    reports about them over a scrutinee of that type, and *arms_alone* the
    part of it that reads only the arms, which a scrutinee in error draws
    too.  *catch_all* says whether a wildcard arm makes coverage moot.
    """

    ty: str
    arms: tuple[str, ...]
    verdict: tuple[Report, ...] = ()
    arms_alone: tuple[Report, ...] = ()
    catch_all: bool = False


SHAPES: dict[str, Shape] = {
    "constructors": Shape("opt", ("Some(@Int) -> {v}", "None -> {v}")),
    "missing_constructor": Shape(
        "opt", ("Some(@Int) -> {v}",), verdict=(("E311", "error"),)),
    "nested_literal": Shape(
        "opt", ("Some(1) -> {v}", "Some(_) -> {v}", "None -> {v}")),
    "literals_and_wildcard": Shape(
        "int", ("1 -> {v}", "_ -> {v}"), catch_all=True),
    "literals_only": Shape(
        "int", ("1 -> {v}", "2 -> {v}"), verdict=(("E313", "error"),)),
    "true_false": Shape("bool", ("true -> {v}", "false -> {v}")),
    "true_only": Shape(
        "bool", ("true -> {v}",), verdict=(("E312", "error"),)),
    "wildcard": Shape("opt", ("_ -> {v}",), catch_all=True),
    "after_wildcard": Shape(
        "opt", ("_ -> {v}", "None -> {v}"), verdict=(("E310", "warning"),),
        arms_alone=(("E310", "warning"),), catch_all=True),
    "another_type": Shape(
        "opt", ("true -> {v}", "false -> {v}"),
        verdict=(("E314", "error"), ("E314", "error"), ("E311", "error"))),
    "error_in_arm": Shape(
        "opt", ("Some(@Int) -> @String.0", "None -> {v}"),
        verdict=(("E130", "error"),), arms_alone=(("E130", "error"),)),
}


@dataclass(frozen=True)
class Kind:
    """A way of writing a scrutinee: in error (*wrong*) and correctly
    (*right*), by the type it is written to have (``None`` for every type),
    the codes its own error is reported with, the positions it can be
    written in, and a declaration it needs."""

    codes: tuple[str, ...]
    wrong: dict[str | None, str]
    right: dict[str, str]
    positions: tuple[str, ...] = ("body", "ensures", "where")
    prelude: str = ""

    def written(self, forms: dict[str | None, str], ty: str) -> str | None:
        return forms.get(ty, forms.get(None))


def _by_type(form: str) -> dict[str | None, str]:
    """*form* for each type, ``{t}`` standing for the type's name."""
    return {ty: form.format(t=name) for ty, name in _TYPES.items()}


_RIGHT_CALL = {"opt": "make_opt(@Int.0)", "bool": "make_bool(@Int.0)",
               "int": "make_int(@Int.0)"}

#: A scrutinee the check types `Unknown` after an error.
KINDS: dict[str, Kind] = {
    "slot": Kind(("E130",), _by_type("@{t}.1"), _by_type("@{t}.0")),
    "call": Kind(("E200",), {None: "missing(@Int.0)"}, _RIGHT_CALL),
    "result": Kind(
        ("E163",),
        {"opt": "@Option<Bool>.result", "bool": "@Int.result",
         "int": "@Nat.result"},
        _by_type("@{t}.result"), positions=("ensures",)),
    "result_outside": Kind(
        ("E131",), _by_type("@{t}.result"), {}, positions=("body", "where")),
    "constructor": Kind(
        ("E210",), {None: "Sme(@Int.0)"}, {"opt": "Some(@Int.0)"}),
    "index": Kind(("E161",), _by_type("@{t}.0[0]"), _by_type("[@{t}.0][0]")),
    "block": Kind(("E130",), _by_type("{{ @{t}.1 }}"),
                  _by_type("{{ @{t}.0 }}")),
    "if_branches": Kind(
        ("E130", "E200"),
        _by_type("if @Int.0 > 0 then {{ @{t}.1 }} else {{ missing(@Int.0) }}"),
        {ty: f"if @Int.0 > 0 then {{ @{name}.0 }} else {{ {_RIGHT_CALL[ty]} }}"
         for ty, name in _TYPES.items()}),
    # The removed alias's error carries no code.
    "let_removed_alias": Kind(
        ("",), {None: "{ let @Float = 0.0; @Float.0 }"}, {}),
    # The error is placed at the declaration, not at the scrutinee.
    "refused_declaration": Kind(
        ("E158",), {None: "Wrap(@Int.0)"}, {},
        prelude="private data String { Wrap(Int) }\n\n"),
}

#: A scrutinee whose error leaves it a type, so its match is judged.
NEIGHBOURS: dict[str, Kind] = {
    "wrong_arity": Kind(
        ("E201",), {}, {ty: call.replace("(@Int.0)", "(@Int.0, @Int.0)")
                        for ty, call in _RIGHT_CALL.items()}),
    "let_initialiser": Kind(
        ("E200",), {},
        _by_type("{{ let @{t} = missing(@Int.0); @{t}.0 }}")),
    "if_one_branch": Kind(
        ("E130",), {},
        _by_type("if @Int.0 > 0 then {{ @{t}.1 }} else {{ @{t}.0 }}")),
}

_HELPERS = """private fn make_opt(@Int -> @Option<Int>)
  requires(true)
  ensures(true)
  effects(pure)
{
  Some(@Int.0)
}

private fn make_bool(@Int -> @Bool)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Int.0 > 0
}

private fn make_int(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Int.0
}

"""

_PARAMS = "@Option<Int>, @Bool, @Int"


def _program(position: str, scrutinee: str, shape: Shape,
             prelude: str = "") -> str:
    """A program whose `match` over *scrutinee* is written at *position*."""
    value = "true" if position == "ensures" else "1"
    indent = "      " if position == "where" else "    "
    arms = f",\n{indent}".join(arm.format(v=value) for arm in shape.arms)
    head = prelude + _HELPERS
    if position == "ensures":
        ret = _TYPES[shape.ty]
        return (f"{head}public fn f({_PARAMS} -> @{ret})\n  requires(true)\n"
                f"  ensures(match {scrutinee} {{\n    {arms}\n  }})\n"
                f"  effects(pure)\n{{\n  @{ret}.0\n}}\n")
    match = f"match {scrutinee} {{\n{indent}{arms}\n{indent[:-2]}}}"
    if position == "body":
        return (f"{head}public fn f({_PARAMS} -> @Int)\n  requires(true)\n"
                f"  ensures(true)\n  effects(pure)\n{{\n  {match}\n}}\n")
    return (f"{head}public fn f({_PARAMS} -> @Int)\n  requires(true)\n"
            f"  ensures(true)\n  effects(pure)\n{{\n"
            f"  g(@Option<Int>.0, @Bool.0, @Int.0)\n}}\nwhere {{\n"
            f"  fn g({_PARAMS} -> @Int)\n    requires(true)\n"
            f"    ensures(true)\n    effects(pure)\n  {{\n    {match}\n"
            f"  }}\n}}\n")


def _cells(kinds: dict[str, Kind], side: str) -> list[tuple[str, str, str]]:
    return [(kind_name, shape_name, position)
            for kind_name, kind in kinds.items()
            for shape_name, shape in SHAPES.items()
            for position in kind.positions
            if kind.written(getattr(kind, side), shape.ty) is not None]


@pytest.mark.parametrize(("kind", "shape", "position"),
                         _cells(KINDS, "wrong"))
def test_a_match_over_a_scrutinee_in_error_reports_its_error(
        kind: str, shape: str, position: str) -> None:
    """Exactly the scrutinee's codes, then what the arms report whatever
    the scrutinee: never a verdict on coverage."""
    k, s = KINDS[kind], SHAPES[shape]
    scrutinee = k.written(k.wrong, s.ty)
    assert scrutinee is not None
    checked = pipeline.check(_program(position, scrutinee, s, k.prelude))
    assert _report(checked) == _errors(*k.codes) + list(s.arms_alone), (
        checked.diagnostics)


@pytest.mark.parametrize(("kind", "shape", "position"),
                         _cells(KINDS, "right"))
def test_the_same_match_over_the_scrutinee_written_correctly_keeps_its_verdict(
        kind: str, shape: str, position: str) -> None:
    """The arms' verdict over a scrutinee of their type, and where they draw
    none, a program that verifies with every obligation proved."""
    k, s = KINDS[kind], SHAPES[shape]
    scrutinee = k.written(k.right, s.ty)
    assert scrutinee is not None
    source = _program(position, scrutinee, s, k.prelude)
    checked = pipeline.check(source)
    assert _report(checked) == list(s.verdict), checked.diagnostics
    if not s.verdict:
        verified = pipeline.verify(source)
        assert verified.ok, verified.diagnostics
        assert {o.status for o in verified.obligations} == {"verified"}


@pytest.mark.parametrize(("kind", "shape", "position"),
                         _cells(NEIGHBOURS, "right"))
def test_a_scrutinee_whose_error_leaves_it_a_type_is_judged(
        kind: str, shape: str, position: str) -> None:
    """Its own codes, then the arms' verdict over a scrutinee of their
    type."""
    k, s = NEIGHBOURS[kind], SHAPES[shape]
    scrutinee = k.written(k.right, s.ty)
    assert scrutinee is not None
    checked = pipeline.check(_program(position, scrutinee, s))
    assert _report(checked) == _errors(*k.codes) + list(s.verdict), (
        checked.diagnostics)


@pytest.mark.parametrize("shape", list(SHAPES))
def test_an_unknown_scrutinee_with_no_error_is_judged_as_unknown(
        shape: str) -> None:
    """With no error reported, `Unknown` is judged as it always was: what
    the arms report, then E313 unless a catch-all makes coverage moot."""
    s = SHAPES[shape]
    arms = ",\n    ".join(arm.format(v="1") for arm in s.arms)
    checked = pipeline.check(_GENERIC.format(arms=arms))
    expected = list(s.arms_alone) + ([] if s.catch_all else _errors("E313"))
    assert _report(checked) == expected, checked.diagnostics
