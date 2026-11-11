"""A join is recorded at the facts its arms share (#1716).

THE MECHANISM.  The checker's join of two types (`CallsMixin._join`, the
walk `_Join._walk`) answers with its second type, each open position filled
from the first, and keeps the second's refinements whatever the first
states; `is_subtype` admits a base where its refinement is expected.  So an
`if` was recorded at its else branch's type, a `match` at its first value
arm's and an `Exn` handler at its body's: `if c then { @Int.0 } else
{ @PosInt.0 }` was a `PosInt`, and with its branches swapped an `Int`.
Every reader of the recorded type inherited the claim: the type argument a
generic is instantiated at (`idg(<that if>)` instantiated `T` at `PosInt`,
so `idg`'s declared return proved what the `Int` branch never had) and
`_narrows_into_refined` deciding a guarded binder's post-fact.

THE RULE.  A value join is recorded at the facts its arms share, position by
position: a refinement both state, kept; one stated by one arm and not the
other, or two different predicates, dropped to the base there; a `Nat`
beside an `Int` an `Int` (at the head under spec §4.8's static-literal
exception); a `Never` arm takes no part, and an open position is filled from
the other side.  The result does not depend on the order of the arms.
"""

from __future__ import annotations

import itertools
import sys
from dataclasses import dataclass
from pathlib import Path

import pytest

from tests import pipeline
from vera import ast, fold, narrowing
from vera.types import (AdtType, FunctionType, PrimitiveType, RefinedType,
                        Type, TypeVar, UnknownType)

pytestmark = pytest.mark.matrix(decides=["vera/checker/control.py"])

FILE = "join_recorded_type.vera"

_HEAD = """\
type PosInt = { @Int | @Int.0 > 0 };
type NegInt = { @Int | @Int.0 < 0 };
type IntFn = fn(Int -> Int) effects(pure);
type PosFn = fn(PosInt -> Int) effects(pure);
type IntToPos = fn(Int -> PosInt) effects(pure);

"""


# =====================================================================
# The two open lines of the issue, each against `vera run`
# =====================================================================

_GENERIC = """\
type PosInt = {{ @Int | @Int.0 > 0 }};

public fn f(@Bool, @Int, @PosInt -> @Int)
  requires(true)
  ensures(@Int.result > 0)
  effects(pure)
{{
  idg(if @Bool.0 then {{ {first} }} else {{ {second} }})
}}

private forall<T> fn idg(@T -> @T)
  requires(true)
  ensures(true)
  effects(pure)
{{
  @T.0
}}

public fn t(@Bool, @Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{{
  f(@Bool.0, @Int.0, 3)
}}
"""


@pytest.mark.parametrize("order", ["int first", "posint first"])
def test_repro_1716_a_generic_is_instantiated_at_the_join_of_its_arms(
        order: str) -> None:
    """`idg(if c then { @Int.0 } else { @PosInt.0 })` instantiates `T` at
    `Int` in either order, so `f`'s `ensures(@Int.result > 0)` is not
    proved (`tier3`, E522: the call's result is a value `idg`'s contract
    states nothing of, so no counterexample stands) and is checked at run
    time, and no narrowing into a `PosInt` is obligated at the argument;
    the run at the `Int` arm with -5 breaks the postcondition.  At base the
    order decided: `Int` first instantiated `T` at `PosInt`, recorded the
    `ensures` `verified` and refused the argument (E505); `PosInt` first
    instantiated it at `Int`."""
    first, second = (("@Int.0", "@PosInt.0") if order == "int first"
                     else ("@PosInt.0", "@Int.0"))
    source = _GENERIC.format(first=first, second=second)
    verified = pipeline.verify(source, file=FILE)
    f_rows = [(o.kind, o.status, o.error_code) for o in verified.obligations
              if o.fn_name == "f"]
    assert [r for r in f_rows if r[0] == "ensures"] == [
        ("ensures", "tier3", "E522")], f_rows
    assert [r for r in f_rows if r[0] == "refine_bind"
            and r[1] != "verified"] == [], f_rows
    assert verified.errors == (), [(d.error_code, d.description[:80])
                                   for d in verified.errors]
    int_arm = order == "int first"
    ran = pipeline.run(source, "t", [1 if int_arm else 0, -5], file=FILE)
    assert ran.trap is not None
    assert "Postcondition violation" in str(ran.trap), str(ran.trap)


_GUARDED_LET = """\
type PosInt = {{ @Int | @Int.0 > 0 }};

public fn f(@Bool, @Int, @PosInt -> @Int)
  requires(true)
  ensures(@Int.result > 0)
  effects(pure)
{{
  let @PosInt = if @Bool.0 then {{ {first} }} else {{ {second} }};
  @PosInt.0
}}

public fn t(@Bool, @Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{{
  f(@Bool.0, @Int.0, 3)
}}
"""


@pytest.mark.parametrize("order", ["int first", "posint first"])
def test_repro_1716_a_guarded_let_binder_keeps_its_post_fact(
        order: str) -> None:
    """`let @PosInt = if c then { @Int.0 } else { @PosInt.0 }` is a
    narrowing (E505: the `Int` arm can break it) whose binder holds
    `PosInt` after the bind, so `ensures(@Int.result > 0)` over it is
    `verified` in either order; the run at -5 traps at the bind's guard.
    At base the `Int`-first order recorded the join `PosInt`, minted no
    post-fact, and refuted the `ensures` (E500) with a counterexample the
    guard traps before."""
    first, second = (("@Int.0", "@PosInt.0") if order == "int first"
                     else ("@PosInt.0", "@Int.0"))
    source = _GUARDED_LET.format(first=first, second=second)
    verified = pipeline.verify(source, file=FILE)
    f_rows = [(o.kind, o.status) for o in verified.obligations
              if o.fn_name == "f"]
    assert ("ensures", "verified") in f_rows, f_rows
    assert {d.error_code for d in verified.errors} == {"E505"}, [
        (d.error_code, d.description[:80]) for d in verified.errors]
    int_arm = order == "int first"
    ran = pipeline.run(source, "t", [1 if int_arm else 0, -5], file=FILE)
    assert ran.trap is not None
    assert "Refinement violation in let binding" in str(ran.trap)
    held = pipeline.run(source, "t", [1 if int_arm else 0, 4], file=FILE)
    assert held.value == 4


# =====================================================================
# The recorded type of a join, in both orders of its arms
# =====================================================================


def _show(t: Type | None) -> str:
    """*t* with each refinement written by its alias-free predicate's
    position: `{Int|PosInt}` where the predicate is `PosInt`'s."""
    if isinstance(t, RefinedType):
        names = [name for pred, name in _PREDS if pred == t.predicate]
        return "{" + _show(t.base) + "|" + (names[0] if names else "?") + "}"
    if isinstance(t, AdtType):
        if not t.type_args:
            return t.name
        return t.name + "<" + ", ".join(_show(a) for a in t.type_args) + ">"
    if isinstance(t, FunctionType):
        return ("fn(" + ", ".join(_show(p) for p in t.params) + " -> "
                + _show(t.return_type) + ")")
    if isinstance(t, PrimitiveType):
        return t.name
    if isinstance(t, TypeVar):
        return "'" + t.name
    if isinstance(t, UnknownType):
        return "?"
    return repr(t)


#: Each refinement alias's predicate and name, as the program declares them.
_PREDS: list[tuple[ast.Expr, str]] = []


def _learn_predicates(checked: pipeline.Checked) -> None:
    _PREDS.clear()
    for tl in checked.program.declarations:
        decl = getattr(tl, "decl", tl)
        if isinstance(decl, ast.TypeAliasDecl) and isinstance(
                decl.type_expr, ast.RefinementType):
            _PREDS.append((decl.type_expr.predicate, decl.name))


#: (the function's parameters, its return, arm one, arm two, the join's
#: recorded type in either order).
JOINS = [
    ("@Int, @PosInt", "@Int", "@Int.0", "@PosInt.0", "Int"),
    ("@PosInt, @PosInt", "@Int", "@PosInt.0", "@PosInt.1", "{Int|PosInt}"),
    ("@PosInt, @NegInt", "@Int", "@PosInt.0", "@NegInt.0", "Int"),
    ("@Option<Int>, @Option<PosInt>", "@Option<Int>", "@Option<Int>.0",
     "@Option<PosInt>.0", "Option<Int>"),
    ("@Tuple<Int, Int>, @Tuple<PosInt, Int>", "@Tuple<Int, Int>",
     "@Tuple<Int, Int>.0", "@Tuple<PosInt, Int>.0", "Tuple<Int, Int>"),
    ("@Option<Option<Int>>, @Option<Option<PosInt>>",
     "@Option<Option<Int>>", "@Option<Option<Int>>.0",
     "@Option<Option<PosInt>>.0", "Option<Option<Int>>"),
    ("@Option<Int>, @Option<Nat>", "@Option<Int>", "@Option<Int>.0",
     "@Option<Nat>.0", "Option<Int>"),
    ("@Int, @Nat", "@Int", "@Int.0", "@Nat.0", "Int"),
    ("@PosInt", "@Int", "1", "@PosInt.0", "Int"),
    ("@PosInt", "@Int", "0", "@PosInt.0", "Int"),
    ("@Option<PosInt>", "@Option<PosInt>", "None", "@Option<PosInt>.0",
     "Option<{Int|PosInt}>"),
    ("@PosFn, @IntFn", "@IntFn", "@PosFn.0", "@IntFn.0", "fn(Int -> Int)"),
    ("@IntFn, @IntToPos", "@IntFn", "@IntFn.0", "@IntToPos.0",
     "fn(Int -> Int)"),
    ("@Tuple<PosInt, Int>, @Tuple<PosInt, Nat>", "@Tuple<PosInt, Int>",
     "@Tuple<PosInt, Int>.0", "@Tuple<PosInt, Nat>.0",
     "Tuple<{Int|PosInt}, Int>"),
    ("@Nat", "@Nat", "3", "@Nat.0", "Nat"),
    ("@Int", "@Int", "@Int.0", "@Int.0 + 1", "Int"),
]


def _join_program(params: str, ret: str, body: str) -> str:
    return (_HEAD + f"private fn j(@Bool, {params} -> {ret})\n"
            "  requires(true)\n  ensures(true)\n  effects(pure)\n{\n"
            f"  {body}\n}}\n")


def _recorded(source: str, kind: type[ast.Expr]) -> list[str]:
    checked = pipeline.check(source, file=FILE)
    assert checked.ok, [(d.error_code, d.description[:90])
                        for d in checked.errors]
    _learn_predicates(checked)
    types = checked.artifacts.node_semantic_types
    out = []
    for tl in checked.program.declarations:
        decl = getattr(tl, "decl", tl)
        if isinstance(decl, ast.FnDecl):
            for node in fold.walk(decl.body):
                if isinstance(node, kind):
                    out.append(_show(types.get(node.node_id)))
    return out


@pytest.mark.parametrize("params,ret,a,b,expected", JOINS)
@pytest.mark.parametrize("swap", [False, True], ids=["ab", "ba"])
def test_an_if_is_recorded_at_the_facts_its_branches_share(
        params: str, ret: str, a: str, b: str, expected: str,
        swap: bool) -> None:
    first, second = (b, a) if swap else (a, b)
    source = _join_program(
        params, ret, f"if @Bool.0 then {{ {first} }} else {{ {second} }}")
    assert _recorded(source, ast.IfExpr) == [expected]


@pytest.mark.parametrize("params,ret,a,b,expected", JOINS)
@pytest.mark.parametrize("swap", [False, True], ids=["ab", "ba"])
def test_a_match_is_recorded_at_the_facts_its_arms_share(
        params: str, ret: str, a: str, b: str, expected: str,
        swap: bool) -> None:
    first, second = (b, a) if swap else (a, b)
    source = _join_program(
        params, ret,
        f"match @Bool.0 {{\n    true -> {first},\n    false -> {second}\n  }}")
    assert _recorded(source, ast.MatchExpr) == [expected]


#: An `Exn` handler over a body and a clause, each an arm, in both orders.
HANDLED = [
    ("@Int, @PosInt", "@Int", "@Int.0", "@PosInt.0", "Int"),
    ("@Option<Int>, @Option<PosInt>", "@Option<Int>", "@Option<Int>.0",
     "@Option<PosInt>.0", "Option<Int>"),
    ("@Int, @Nat", "@Int", "@Int.0", "@Nat.0", "Int"),
    ("@PosInt", "@Int", "1", "@PosInt.0", "Int"),
    ("@PosInt, @PosInt", "@Int", "@PosInt.0", "@PosInt.1", "{Int|PosInt}"),
]


def _handled(body: str, clause: str) -> str:
    return (f"handle[Exn<String>] {{\n    throw(@String) -> {{ {clause} }}\n"
            f"  }} in {{\n    if @Bool.0 then {{ {body} }} else "
            '{ throw("x") }\n  }')


@pytest.mark.parametrize("params,ret,a,b,expected", HANDLED)
@pytest.mark.parametrize("swap", [False, True], ids=["ab", "ba"])
def test_a_handler_is_recorded_at_the_facts_its_body_and_clause_share(
        params: str, ret: str, a: str, b: str, expected: str,
        swap: bool) -> None:
    body, clause = (b, a) if swap else (a, b)
    source = _join_program(params, ret, _handled(body, clause))
    assert _recorded(source, ast.HandleExpr) == [expected]


# =====================================================================
# Permutations: one record and one verdict whatever the arms' order
# =====================================================================

#: Three arms: an `Int`, two `PosInt`s; or a `Nat` and an `Int` beside a
#: `Nat`; or three `PosInt`s; the join's record in every order.
THREE = [
    ("@Int, @PosInt, @PosInt", ("@Int.0", "@PosInt.0", "@PosInt.1"), "Int"),
    ("@Int, @Nat, @Nat", ("@Int.0", "@Nat.0", "@Nat.1"), "Int"),
    ("@PosInt, @PosInt, @PosInt", ("@PosInt.0", "@PosInt.1", "@PosInt.2"),
     "{Int|PosInt}"),
]

_PERMUTATIONS = list(itertools.permutations(range(3)))

_THREE_PROGRAM = """\
type PosInt = {{ @Int | @Int.0 > 0 }};

public fn f(@Bool, @Int, {params} -> @Int)
  requires(true)
  ensures(@Int.result > 0)
  effects(pure)
{{
  idg({join})
}}

private forall<T> fn idg(@T -> @T)
  requires(true)
  ensures(true)
  effects(pure)
{{
  @T.0
}}
"""


def _three(form: str, arms: tuple[str, str, str]) -> str:
    if form == "match":
        return (f"match @Int.{_THREE_SELECTOR} {{\n    0 -> {arms[0]},\n"
                f"    1 -> {arms[1]},\n    _ -> {arms[2]}\n  }}")
    # a handler: the body joins two arms, the clause is the third
    return (f"handle[Exn<String>] {{\n    throw(@String) -> {{ {arms[2]} }}\n"
            f"  }} in {{\n    if @Bool.0 then {{ {arms[0]} }} else {{ "
            f"if @Int.{_THREE_SELECTOR} == 0 then {{ {arms[1]} }} else "
            '{ throw("x") } }\n  }')


#: The selector `@Int` sits before the arms' parameters, so its index is
#: past every `@Int` arm parameter.
_THREE_SELECTOR = "SEL"


def _three_program(params: str, form: str, arms: tuple[str, str, str]) -> str:
    sel = str(params.count("@Int,") + params.count("@Int ")
              + (1 if params.endswith("@Int") else 0))
    join = _three(form, arms).replace(_THREE_SELECTOR, sel)
    return _THREE_PROGRAM.format(params=params, join=join)


def _verdict(verified: pipeline.Verified) -> tuple[object, ...]:
    """What a verification says, read independently of where it says it:
    the verdict, the error codes and each function's rows by kind and
    status."""
    rows = sorted((o.fn_name, o.kind, o.status, o.error_code)
                  for o in verified.obligations) if verified.ran else []
    return (verified.ok, sorted(d.error_code for d in verified.errors),
            rows)


@pytest.mark.parametrize("params,arms,expected", THREE)
@pytest.mark.parametrize("form", ["match", "handler"])
def test_every_order_of_three_arms_gives_one_record_and_one_verdict(
        params: str, arms: tuple[str, str, str], expected: str,
        form: str) -> None:
    records = set()
    verdicts = set()
    for order in _PERMUTATIONS:
        source = _three_program(params, form, tuple(arms[i] for i in order))
        kind = ast.MatchExpr if form == "match" else ast.HandleExpr
        records.add(tuple(_recorded(source, kind)))
        verdicts.add(repr(_verdict(pipeline.verify(source, file=FILE))))
    assert records == {(expected,)}
    assert len(verdicts) == 1, verdicts


# =====================================================================
# Function types: a parameter or a return the arms differ by
# =====================================================================

_FN_PROGRAM = """\
type PosInt = {{ @Int | @Int.0 > 0 }};
type IF = fn(Int -> Int) effects(pure);

private fn pick(@Bool -> @IF)
  requires(true)
  ensures(true)
  effects(pure)
{{
  if @Bool.0 then {{
    {first}
  }} else {{
    {second}
  }}
}}

public fn t(@Bool, @Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{{
  apply_fn(pick(@Bool.0), @Int.0)
}}
"""

_POS_PARAM = "fn(@PosInt -> @Int) effects(pure) {\n      @PosInt.0\n    }"
_INT_PARAM = "fn(@Int -> @Int) effects(pure) {\n      1\n    }"


@pytest.mark.parametrize("swap", [False, True], ids=["pos first", "int first"])
def test_a_parameter_refinement_the_arms_differ_by_drops_to_the_base(
        swap: bool) -> None:
    """`fn(PosInt -> Int)` beside `fn(Int -> Int)` is recorded
    `fn(Int -> Int)` in either order: the relaxation `is_subtype` already
    admits (rule 9 with rule 7), the closure's entry check holding its
    parameter, so the run at 0 through the `PosInt` closure traps there."""
    first, second = (_INT_PARAM, _POS_PARAM) if swap else (
        _POS_PARAM, _INT_PARAM)
    source = _FN_PROGRAM.format(first=first, second=second)
    assert _recorded(source, ast.IfExpr) == ["fn(Int -> Int)"]
    verified = pipeline.verify(source, file=FILE)
    assert verified.ok, [(d.error_code, d.description[:80])
                         for d in verified.errors]
    assert ("pick", "refine_bind") in {(o.fn_name, o.kind)
                                       for o in verified.obligations}
    ran = pipeline.run(source, "t", [0 if swap else 1, 0], file=FILE)
    assert ran.trap is not None
    assert "Refinement violation in fn(@PosInt -> @Int)" in str(ran.trap)
    held = pipeline.run(source, "t", [1 if swap else 0, 0], file=FILE)
    assert held.value == 1


_POS_RETURN = "fn(@Int -> @PosInt) effects(pure) {\n      5\n    }"
_INT_RETURN = "fn(@Int -> @Int) effects(pure) {\n      @Int.0\n    }"

_RETURN_PROGRAM = """\
type PosInt = {{ @Int | @Int.0 > 0 }};
type IF = fn(Int -> Int) effects(pure);

public fn f(@Bool, @Int -> @Int)
  requires(true)
  ensures(@Int.result > 0)
  effects(pure)
{{
  apply_fn(if @Bool.0 then {{
    {first}
  }} else {{
    {second}
  }}, @Int.0)
}}
"""


@pytest.mark.parametrize("swap", [False, True], ids=["pos first", "int first"])
def test_a_return_refinement_the_arms_differ_by_is_not_a_fact(
        swap: bool) -> None:
    """`fn(Int -> PosInt)` beside `fn(Int -> Int)` is `fn(Int -> Int)`
    in either order, so a caller's `> 0` over its application is not
    proved; the run through the `Int` closure at -5 breaks it."""
    first, second = (_INT_RETURN, _POS_RETURN) if swap else (
        _POS_RETURN, _INT_RETURN)
    source = _RETURN_PROGRAM.format(first=first, second=second)
    assert _recorded(source, ast.IfExpr) == ["fn(Int -> Int)"]
    verified = pipeline.verify(source, file=FILE)
    statuses = [o.status for o in verified.obligations
                if o.fn_name == "f" and o.kind == "ensures"]
    assert statuses and "verified" not in statuses, statuses
    ran = pipeline.run(source, "f", [1 if swap else 0, -5], file=FILE)
    assert ran.trap is not None
    assert "Postcondition violation" in str(ran.trap)


# =====================================================================
# The matrix: join form x position x the arms' mix x the reader
# =====================================================================
#
# Each cell is a program `f` whose join of two arms, `a` (the arm under
# test) and `b` (a refined arm), is handed to a reader that expects the
# refined type `R` at a position; `t(@Bool, @V)` builds the arguments and
# calls `f`, the `@Bool` choosing the arm.  Three differentials per cell:
#
# * breaking: `a` breaks `R` at the input; the run at the arm traps, and the
#   verification is not every record `verified` on a clean verdict (a
#   `verified` record whose run traps is the defect);
# * holding: `a` replaced by an arm that holds `R`; the program verifies
#   clean and runs to a value that holds at both arms;
# * order: `a` and `b` swapped give one verdict, breaking and holding.

#: position -> (the type at it, given the type at the head; a value at it,
#: given one at the head; the reader's pattern match taking the head value
#: out of a slot of type at it, given the head type name).
POSITIONS = {
    "head": ("{t}", "{x}"),
    "argument": ("Option<{t}>", "Some({x})"),
    "tuple": ("Tuple<{t}, Bool>", "Tuple({x}, true)"),
    "two levels": ("Option<Option<{t}>>", "Some(Some({x}))"),
}


def _at(position: str, t: str) -> str:
    return POSITIONS[position][0].format(t=t)


def _value(position: str, x: str) -> str:
    return POSITIONS[position][1].format(x=x)


def _take(position: str, r: str) -> str:
    """The body of `xtr`, taking the `@R` value out of `@<position R>.0`."""
    slot = f"@{_at(position, r)}.0"
    if position == "head":
        return slot
    if position == "argument":
        return f"match {slot} {{\n    Some(@{r}) -> @{r}.0,\n    None -> 1\n  }}"
    if position == "tuple":
        return f"match {slot} {{\n    Tuple(@{r}, @Bool) -> @{r}.0\n  }}"
    return (f"match {slot} {{\n    Some(@Option<{r}>) -> match "
            f"@Option<{r}>.0 {{\n      Some(@{r}) -> @{r}.0,\n"
            f"      None -> 1\n    }},\n    None -> 1\n  }}")


@dataclass(frozen=True)
class Mix:
    """The arms' mix: the refined type `R` and its `ensures` bound, the
    arm under test's parameter type (`None`: a value written in place),
    the breaking arm and the holding one, the refined arm, and the head
    value `t` passes for the arm under test."""

    name: str
    refined: str
    bound: str
    breaking: str
    holding: str
    tested_type: str | None
    input: int


MIXES = [
    Mix("base beside refined", "PosInt", "> 0", "@{at_V}.0", "@{at_R}.1",
        "Int", -5),
    Mix("two predicates", "PosInt", "> 0", "@{at_V}.0", "@{at_R}.1",
        "NegInt", -5),
    Mix("Nat beside Int", "Nat", ">= 0", "@{at_V}.0", "@{at_R}.1",
        "Int", -5),
    Mix("literal beside refined", "PosInt", "> 0", "{lit0}", "{lit1}",
        None, 4),
]

FORMS = ("if", "match", "nested if", "handler")
READERS = ("return", "argument", "let", "generic")


def _join(form: str, first: str, second: str) -> str:
    if form == "if":
        return f"if @Bool.0 then {{\n    {first}\n  }} else {{\n    {second}\n  }}"
    if form == "match":
        return f"match @Bool.0 {{\n    true -> {first},\n    false -> {second}\n  }}"
    if form == "nested if":
        # a join of joins, each arm in both: the first is taken on true
        inner = (f"if @Bool.0 then {{\n      {first}\n    }} else {{\n"
                 f"      {second}\n    }}")
        return (f"if @Bool.0 then {{\n    {inner}\n  }} else {{\n"
                f"    {inner}\n  }}")
    return (f"handle[Exn<String>] {{\n    throw(@String) -> {{\n      {second}\n"
            f"    }}\n  }} in {{\n    if @Bool.0 then {{\n      {first}\n"
            '    } else {\n      throw("x")\n    }\n  }')


def matrix_program(form: str, position: str, mix: Mix, reader: str,
                   *, holds: bool, swap: bool) -> str:
    r = mix.refined
    at_r = _at(position, r)
    v = mix.tested_type
    at_v = _at(position, v) if v is not None else None
    tested = (mix.holding if holds else mix.breaking).format(
        at_V=at_v, at_R=at_r, lit0=_value(position, "0"),
        lit1=_value(position, "1"))
    refined_arm = f"@{at_r}.0"
    first, second = (refined_arm, tested) if swap else (tested, refined_arm)
    join = _join(form, first, second)
    params = ["@Bool"] + ([f"@{at_v}"] if at_v is not None else []) + [
        f"@{at_r}", f"@{at_r}"]
    sig = ", ".join(params)
    if reader == "return":
        ret, ensures, body = f"@{at_r}", "true", join
    elif reader == "argument":
        ret, ensures, body = "@Int", f"@Int.result {mix.bound}", f"xtr({join})"
    elif reader == "let":
        ret, ensures, body = ("@Int", f"@Int.result {mix.bound}",
                              f"let @{at_r} = {join};\n  xtr(@{at_r}.0)")
    else:
        ret, ensures, body = ("@Int", f"@Int.result {mix.bound}",
                              f"xtr(idg({join}))")
    head_v = "Int" if v in (None, "Int") else v
    args = ["@Bool.0"] + ([_value(position, f"@{head_v}.0")]
                          if at_v is not None else []) + [
        _value(position, "3"), _value(position, "3")]
    call = f"f({', '.join(args)})"
    if reader == "return":
        call = f"xtr({call})"
    return f"""\
type PosInt = {{ @Int | @Int.0 > 0 }};
type NegInt = {{ @Int | @Int.0 < 0 }};

public fn f({sig} -> {ret})
  requires(true)
  ensures({ensures})
  effects(pure)
{{
  {body}
}}

private fn xtr(@{at_r} -> @Int)
  requires(true)
  ensures(@Int.result {mix.bound})
  effects(pure)
{{
  {_take(position, r)}
}}

private forall<T> fn idg(@T -> @T)
  requires(true)
  ensures(true)
  effects(pure)
{{
  @T.0
}}

public fn t(@Bool, @{head_v} -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{{
  {call}
}}
"""


CELLS = [
    pytest.param(form, position, mix, reader,
                 id=f"{form}-{position}-{mix.name}-{reader}")
    for form in FORMS for position in POSITIONS for mix in MIXES
    for reader in READERS
]


def _picks(swap: bool) -> int:
    """The `@Bool` that takes the arm under test: the first arm on true."""
    return 0 if swap else 1


@pytest.mark.parametrize("form,position,mix,reader", CELLS)
def test_a_join_handed_to_a_refined_reader_is_never_proved_by_one_arm(
        form: str, position: str, mix: Mix, reader: str) -> None:
    verdicts: dict[tuple[bool, bool], tuple[object, ...]] = {}
    for swap in (False, True):
        for holds in (False, True):
            source = matrix_program(form, position, mix, reader,
                                    holds=holds, swap=swap)
            verified = pipeline.verify(source, file=FILE)
            assert verified.checked.ok, (
                [(d.error_code, d.description[:90])
                 for d in verified.checked.errors], source)
            verdicts[(swap, holds)] = _verdict(verified)
            if holds:
                assert verified.ok, (
                    [(d.error_code, d.description[:90])
                     for d in verified.errors], source)
                for pick in (0, 1):
                    ran = pipeline.run(source, "t", [pick, mix.input],
                                       file=FILE)
                    assert ran.trap is None, (str(ran.trap), source)
                continue
            ran = pipeline.run(source, "t", [_picks(swap), mix.input],
                               file=FILE)
            assert ran.trap is not None, ("the breaking arm must trap",
                                          source)
            assert not (verified.ok and all(
                o.status == "verified" for o in verified.obligations)), (
                "every record verified, and the run traps", source)
    assert verdicts[(False, False)] == verdicts[(True, False)]
    assert verdicts[(False, True)] == verdicts[(True, True)]


#: A refined arm beside an arm open at the position (`None`), which holds:
#: the join keeps the refinement, and the program verifies clean.
@pytest.mark.parametrize("position", ["argument", "two levels"])
@pytest.mark.parametrize("form", FORMS)
@pytest.mark.parametrize("reader", READERS)
def test_a_refined_arm_beside_an_open_one_keeps_its_refinement(
        position: str, form: str, reader: str) -> None:
    mix = Mix("open beside refined", "PosInt", "> 0", "None", "None", None, 4)
    sources = [matrix_program(form, position, mix, reader, holds=True,
                              swap=swap) for swap in (False, True)]
    verdicts = []
    for source in sources:
        verified = pipeline.verify(source, file=FILE)
        assert verified.ok, ([(d.error_code, d.description[:90])
                              for d in verified.errors], source)
        verdicts.append(_verdict(verified))
        for pick in (0, 1):
            assert pipeline.run(source, "t", [pick, 4], file=FILE).trap is None
    assert verdicts[0] == verdicts[1]


# =====================================================================
# The invariant: every fact a join's record states, every arm states
# =====================================================================


def _chain(t: Type) -> tuple[Type, tuple[ast.Expr, ...]]:
    preds: list[ast.Expr] = []
    while isinstance(t, RefinedType):
        preds.append(t.predicate)
        t = t.base
    return t, tuple(reversed(preds))


def _unstated(record: Type, arm: Type | None,
              path: tuple[object, ...] = ()) -> list[tuple[object, ...]]:
    """The positions where *record* states a refinement or a `Nat` that
    *arm* does not: none where the arm is open, unknown or `Never`."""
    if arm is None:
        return []
    rb, rp = _chain(record)
    ab, ap = _chain(arm)
    if isinstance(ab, (TypeVar, UnknownType)) or (
            isinstance(ab, PrimitiveType) and ab.name == "Never"):
        return []
    out: list[tuple[object, ...]] = []
    if ap[:len(rp)] != rp:
        out.append((*path, "refinement"))
    if (isinstance(rb, PrimitiveType) and rb.name == "Nat"
            and isinstance(ab, PrimitiveType) and ab.name == "Int"):
        out.append((*path, "Nat"))
    if isinstance(rb, AdtType) and isinstance(ab, AdtType):
        for i, (x, y) in enumerate(zip(rb.type_args, ab.type_args)):
            out += _unstated(x, y, (*path, i))
    if isinstance(rb, FunctionType) and isinstance(ab, FunctionType):
        for i, (x, y) in enumerate(zip(rb.params, ab.params)):
            out += _unstated(x, y, (*path, "param", i))
        out += _unstated(rb.return_type, ab.return_type, (*path, "result"))
    return out


def _no_call(_call: ast.Expr) -> str | None:
    return None


def violations(checked: pipeline.Checked) -> list[str]:
    """Each join of *checked*'s program whose record states a fact one of
    its value arms does not, as `line:column`."""
    types = checked.artifacts.node_semantic_types
    out = []
    for tl in checked.program.declarations:
        decl = getattr(tl, "decl", tl)
        if not isinstance(decl, ast.FnDecl):
            continue
        roots = [decl.body] + [w.body for w in decl.where_fns or ()]
        for node in (n for root in roots for n in fold.walk(root)):
            if not isinstance(node, (ast.IfExpr, ast.MatchExpr,
                                     ast.HandleExpr)):
                continue
            record = types.get(node.node_id)
            if record is None:
                continue
            for leaf in narrowing.value_leaves(node):
                found = _unstated(record, types.get(leaf.node_id))
                if narrowing.is_static_nat_typed(leaf, _no_call):
                    found = [f for f in found if f != ("Nat",)]
                if found:
                    out.append(f"{node.span.line}:{node.span.column}")
                    break
    return out


ROOT = Path(__file__).resolve().parent.parent

#: The joins whose record stated a fact an arm does not at f71c401c, the
#: base this rule was measured against: each now records what its arms
#: share.
BASE_VIOLATORS = {
    "examples/maximum_syntax.vera": ["182:14"],
    "spec/09-standard-library.md:109": ["6:3"],
    "seed104": ["89:14"], "seed183": ["27:14"], "seed191": ["52:14"],
    "seed197": ["106:3"], "seed266": ["24:3", "27:5"],
    "seed277": ["39:15", "40:5"], "seed363": ["52:15", "57:5"],
    "seed369": ["25:3", "28:5"], "seed418": ["27:14", "34:5"],
    "seed430": ["55:3"], "seed500": ["18:15"], "seed581": ["92:3"],
    "seed626": ["45:3"], "seed905": ["39:3"],
}

_CORPUS = sorted((ROOT / "examples").glob("*.vera")) + sorted(
    (ROOT / "tests" / "conformance").glob("*.vera"))


def _doc_blocks() -> list[tuple[str, str]]:
    sys.path.insert(0, str(ROOT / "scripts"))
    import check_doc_examples as cde
    from doc_annotations import strip_annotations

    out: list[tuple[str, str]] = []
    for pattern in cde.DOC_GATES:
        for path in sorted(ROOT.glob(pattern)):
            blocks, _problems = cde.scan_document(path)
            for block in blocks:
                if cde.selects(block):
                    out.append((f"{path.relative_to(ROOT).as_posix()}:"
                                f"{block.line}",
                                strip_annotations(block.content)))
    return out


def test_every_corpus_join_records_only_what_its_arms_share() -> None:
    found = {}
    for path in _CORPUS:
        checked = pipeline.check(path)
        if checked.ok:
            bad = violations(checked)
            if bad:
                found[path.relative_to(ROOT).as_posix()] = bad
    assert found == {}


def test_every_documented_join_records_only_what_its_arms_share() -> None:
    found = {}
    for name, source in _doc_blocks():
        checked = pipeline.check(source, file="doc.vera")
        if checked.ok:
            bad = violations(checked)
            if bad:
                found[name] = bad
    assert found == {}


@pytest.mark.parametrize("seed", range(1000), ids=[f"seed{s}" for s in range(1000)])
def test_every_generated_join_records_only_what_its_arms_share(
        seed: int, tmp_path: Path) -> None:
    from tests import program_generator as gen

    for name, text in gen.generate(seed).files().items():
        (tmp_path / name).write_text(text, encoding="utf-8")
    checked = pipeline.check(tmp_path / gen.ENTRY)
    assert checked.ok, [d.error_code for d in checked.errors]
    assert violations(checked) == []


@pytest.mark.parametrize("seed", sorted(
    int(k[4:]) for k in BASE_VIOLATORS if k.startswith("seed")))
def test_repro_1716_the_generated_joins_that_stated_an_arms_fact(
        seed: int, tmp_path: Path) -> None:
    """The generator's joins whose record stated, at f71c401c, a
    refinement one of their arms does not (`BASE_VIOLATORS`)."""
    test_every_generated_join_records_only_what_its_arms_share(seed, tmp_path)
