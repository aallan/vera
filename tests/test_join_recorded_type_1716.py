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

THE INSTRUMENT.
* The two open lines of the issue against `vera run`, in both orders.
* The record: an `if`, a `match` and an `Exn` handler over each mix of arm
  types (a base and a refinement, two predicates, a refinement beside an
  open `None`, `Nat` beside `Int`, a literal beside a refinement, function
  types differing by a parameter or a result) at the head, a type argument,
  a tuple component and two levels down, in both orders; three arms in all
  six orders.
* The matrix: join form x position x mix x reader (a return, an argument
  into a refined formal, a `let` at the refined type under an `ensures`, a
  generic's type argument), each cell a differential: the breaking arm's run
  traps and the verification is not all `verified`, the holding variant
  verifies clean and runs, and the two orders give one verdict.
* One row per narrowing: a join under a target lists its arms' rows, once,
  as at base, with its guards and a clean reconciliation.
* The invariant over every join of the corpus, the documented blocks and the
  generator's seeds 0 to 999, with the joins that broke it at base named.
"""

from __future__ import annotations

import itertools
import sys
from dataclasses import dataclass
from pathlib import Path

import pytest

from tests import pipeline
from vera import ast, fold, narrowing
from vera.types import (INT, AdtType, ConcreteEffectRow,
                        FunctionType, PrimitiveType, RefinedType,
                        Type, TypeVar, UnknownType)

pytestmark = pytest.mark.matrix(decides=[
    "vera/checker/control.py", "vera/narrowing.py", "vera/smt.py",
    "vera/verifier.py"])

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
    ("@PosFn, @IntFn", "@IntFn", "@PosFn.0", "@IntFn.0",
     "fn({Int|PosInt} -> Int)"),
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
def test_a_parameter_refinement_one_arm_states_is_what_the_join_accepts(
        swap: bool) -> None:
    """`fn(PosInt -> Int)` beside `fn(Int -> Int)` is recorded
    `fn(PosInt -> Int)` in either order, what both closures accept.
    Returned as an `fn(Int -> Int)` it is the relaxation `is_subtype`
    already admits (rule 9 with rule 7), the closure's entry check holding
    its parameter, so the run at 0 through the `PosInt` closure traps
    there."""
    first, second = (_INT_PARAM, _POS_PARAM) if swap else (
        _POS_PARAM, _INT_PARAM)
    source = _FN_PROGRAM.format(first=first, second=second)
    assert _recorded(source, ast.IfExpr) == ["fn({Int|PosInt} -> Int)"]
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
    if isinstance(ab, TypeVar) and not (
            isinstance(rb, TypeVar) and rb.name == ab.name):
        return []  # open: filled from another arm
    if isinstance(ab, UnknownType) or (
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
                if (narrowing.is_static_nat_typed(leaf, _no_call)
                        and not narrowing.has_underflow_leaf(
                            leaf, lambda _sub: False)):
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
    # a `0 - 1` arm beside a `Nat` arm, read as a `Nat` (review round 1)
    "tests/conformance/ch09_base64.vera": ["24:3", "46:3"],
    "tests/conformance/ch09_html.vera": ["13:3", "74:3"],
    "tests/conformance/ch09_url_encoding.vera": ["32:3", "54:3"],
    "spec/09-standard-library.md:109": ["6:3"],
    "seed104": ["89:14"], "seed177": ["28:14"], "seed551": ["72:14"], "seed183": ["27:14"], "seed191": ["52:14"],
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


# =====================================================================
# One row per narrowing: a join under a target lists its arms' rows
# =====================================================================
#
# A join whose arms are each checked against the type it is bound at is
# the ordinary shape (`if .. then { Ok(@Int.0) } else { Err(..) }` returned
# at `Result<Nat, String>`).  Its record is now the arms' shared type, not
# the target, where at base it was the target: the table lists the rows of
# the join's value by its leaves, so nothing is obligated or guarded twice.
# Each cell pins the rows (bar `requires` and `ensures`), the compiled
# module's trap count and a clean reconciliation, as measured at f71c401c,
# in both orders of the arms and at a return, a `let` and an argument.

#: shape -> (parameters, target, arm a, arm b, the rows at base by position);
#: `JOIN` in a row's text stands for the join as the program writes it.
ROW_SHAPES: dict[str, tuple[str, str, str, str, dict[str, list[tuple[str, str, str]]]]] = {
    "a construction checked at the target": (
        "@Bool, @Int", "Result<Nat, String>", "Ok(@Int.0)", 'Err("no")',
        dict.fromkeys(("return", "let", "argument"),
                      [("nat_bind", "violated", "@Int.0")])),
    "a slot beside an open arm": (
        "@Bool, @Option<Int>", "Option<Nat>", "@Option<Int>.0", "None",
        dict.fromkeys(("return", "let", "argument"),
                      [("nat_bind", "tier3", "@Option<Int>.0 [Some.0]")])),
    "a slot beside a slot": (
        "@Bool, @Option<Int>, @Option<Nat>", "Option<Nat>", "@Option<Int>.0",
        "@Option<Nat>.0",
        dict.fromkeys(("return", "let", "argument"),
                      [("nat_bind", "tier3", "@Option<Int>.0 [Some.0]")])),
    "a literal construction": (
        "@Bool, @Option<Int>", "Option<Nat>", "Some(3)", "@Option<Int>.0",
        dict.fromkeys(("return", "let", "argument"),
                      [("nat_bind", "tier3", "@Option<Int>.0 [Some.0]")])),
    "a literal beside a refined slot": (
        "@Bool, @PosInt", "PosInt", "1", "@PosInt.0",
        {"return": [("refine_bind", "verified", "{ JOIN }"),
                    ("refine_bind", "verified", "@PosInt")],
         "let": [("refine_bind", "verified", "JOIN"),
                 ("refine_bind", "verified", "@PosInt")],
         "argument": [("refine_bind", "verified", "JOIN"),
                      ("refine_bind", "verified", "@PosInt"),
                      ("refine_bind", "verified", "@PosInt")]}),
    "a join inside a join": (
        "@Bool, @Option<Int>, @Option<Nat>", "Option<Nat>",
        "if @Bool.0 then { @Option<Int>.0 } else { None }", "@Option<Nat>.0",
        dict.fromkeys(("return", "let", "argument"),
                      [("nat_bind", "tier3", "@Option<Int>.0 [Some.0]")])),
}

#: The compiled module's `unreachable` count at base, by shape and position.
ROW_TRAPS = {
    "a construction checked at the target": {"return": 12, "let": 12, "argument": 11},
    "a slot beside an open arm": {"return": 11, "let": 11, "argument": 10},
    "a slot beside a slot": {"return": 1, "let": 9, "argument": 1},
    "a literal construction": {"return": 11, "let": 11, "argument": 10},
    "a literal beside a refined slot": {"return": 2, "let": 2, "argument": 2},
    "a join inside a join": {"return": 13, "let": 13, "argument": 12},
}


def _row_program(params: str, target: str, first: str, second: str,
                 position: str) -> str:
    join = f"if @Bool.0 then {{ {first} }} else {{ {second} }}"
    extra = ""
    if position == "return":
        body, ret = join, f"@{target}"
    elif position == "let":
        body, ret = f"let @{target} = {join};\n  0", "@Int"
    else:
        body, ret = f"g({join})", "@Int"
        extra = (f"\nprivate fn g(@{target} -> @Int)\n  requires(true)\n"
                 "  ensures(true)\n  effects(pure)\n{\n  0\n}\n")
    return ("type PosInt = { @Int | @Int.0 > 0 };\n\n"
            f"public fn f({params} -> {ret})\n  requires(true)\n"
            f"  ensures(true)\n  effects(pure)\n{{\n  {body}\n}}\n" + extra)


@pytest.mark.parametrize("swap", [False, True], ids=["ab", "ba"])
@pytest.mark.parametrize("position", ["return", "let", "argument"])
@pytest.mark.parametrize("shape", list(ROW_SHAPES))
def test_a_join_under_a_target_lists_its_arms_rows_once(
        shape: str, position: str, swap: bool) -> None:
    params, target, a, b, rows = ROW_SHAPES[shape]
    first, second = (b, a) if swap else (a, b)
    source = _row_program(params, target, first, second, position)
    verified = pipeline.verify(source, file=FILE, reconcile=True)
    got = sorted((o.kind, o.status, o.expr_text) for o in verified.obligations
                 if o.kind not in ("requires", "ensures"))
    join = f"if @Bool.0 then {{ {first} }} else {{ {second} }}"
    assert got == sorted((kind, status, text.replace("JOIN", join))
                         for kind, status, text in rows[position]), source
    assert verified.reconciled is not None
    report = verified.reconciled.report()
    assert not report.get("mismatches"), report
    assert {d.error_code for d in verified.diagnostics} & {
        "W004", "E541"} == set()
    compiled = pipeline.compile(source, file=FILE)
    assert compiled.wat.count("unreachable") == ROW_TRAPS[shape][position]


def test_a_never_arm_takes_no_part_in_a_match() -> None:
    """A `match` arm that throws (`Never`) states nothing, so a `PosInt`
    arm beside it keeps its refinement, in either order."""
    for arms in (("throw(0)", "@PosInt.0"), ("@PosInt.0", "throw(0)")):
        source = (_HEAD + "private fn j(@Bool, @PosInt -> @Int)\n"
                  "  requires(true)\n  ensures(true)\n  effects(<Exn<Int>>)\n"
                  f"{{\n  match @Bool.0 {{\n    true -> {arms[0]},\n"
                  f"    false -> {arms[1]}\n  }}\n}}\n")
        assert _recorded(source, ast.MatchExpr) == ["{Int|PosInt}"]


#: An arm open at a position, beside a refined arm, where no expected type
#: reaches the join: an empty array literal (its element unknown), and a
#: `None` inside a generic call's argument (its payload a type variable).
OPEN_ARMS = [
    ("@Array<PosInt>", "@Array<PosInt>", "[]", "@Array<PosInt>.0",
     "Array<{Int|PosInt}>"),
    ("@Option<PosInt>", "@Option<PosInt>", "None", "@Option<PosInt>.0",
     "Option<{Int|PosInt}>"),
]


@pytest.mark.parametrize("params,ret,a,b,expected", OPEN_ARMS)
@pytest.mark.parametrize("swap", [False, True], ids=["ab", "ba"])
@pytest.mark.parametrize("form", ["if", "match"])
def test_an_open_arm_states_nothing_where_it_is_open(
        params: str, ret: str, a: str, b: str, expected: str, swap: bool,
        form: str) -> None:
    first, second = (b, a) if swap else (a, b)
    join = (f"if @Bool.0 then {{ {first} }} else {{ {second} }}"
            if form == "if" else
            f"match @Bool.0 {{\n    true -> {first},\n    false -> {second}\n  }}")
    source = (_join_program(params, ret, f"idg({join})")
              + "\nprivate forall<T> fn idg(@T -> @T)\n  requires(true)\n"
              "  ensures(true)\n  effects(pure)\n{\n  @T.0\n}\n")
    kind = ast.IfExpr if form == "if" else ast.MatchExpr
    assert _recorded(source, kind) == [expected]


#: A subtraction among non-negative values beside a `@Nat` (spec §4.8): it
#: can be negative, so the join is an `@Int`, in either order.
SUBTRACTIONS = [
    "@Nat.0 - 1", "0 - 1",
    # a subtraction in a nested join's arm, and behind a `let` in a block
    "if @Nat.0 == 0 then { @Nat.0 - 1 } else { 2 }",
    "let @Int = @Nat.0 - 1;\n    @Int.0",
]


@pytest.mark.parametrize("swap", [False, True], ids=["ab", "ba"])
@pytest.mark.parametrize("form", SUBTRACTIONS)
def test_a_subtraction_beside_a_nat_is_an_int(form: str, swap: bool) -> None:
    first, second = ("@Nat.0", form) if swap else (form, "@Nat.0")
    source = _join_program(
        "@Nat", "@Int", f"if @Bool.0 then {{ {first} }} else {{ {second} }}")
    assert _recorded(source, ast.IfExpr)[0] == "Int"


_SUBTRACTING_HANDLER = """\
public fn f(@Bool, @Nat -> @Int)
  requires(true)
  ensures(@Int.result >= 0)
  effects(pure)
{{
  handle[Exn<Int>] {{
    throw(@Int) -> {{ {clause} }}
  }} in {{
    if @Bool.0 then {{ {body} }} else {{ throw(0) }}
  }}
}}
"""


@pytest.mark.parametrize("swap", [False, True], ids=["body", "clause"])
@pytest.mark.parametrize("form", SUBTRACTIONS)
def test_repro_1716_a_handler_over_a_subtraction_proves_no_nat(
        form: str, swap: bool) -> None:
    """An `Exn` handler joining `@Nat.0` and a subtraction among
    non-negative values, in the body or the clause: its stand-in carries
    no `>= 0`, so `ensures(@Int.result >= 0)` is not proved, and the run at
    the subtraction's arm with `@Nat.0 = 0` breaks it.  At f71c401c the
    clause-subtraction order was recorded `Nat` and proved the `ensures`."""
    body, clause = ("@Nat.0", form) if swap else (form, "@Nat.0")
    source = _SUBTRACTING_HANDLER.format(body=body, clause=clause)
    verified = pipeline.verify(source, file=FILE)
    statuses = [o.status for o in verified.obligations
                if o.fn_name == "f" and o.kind == "ensures"]
    assert statuses and "verified" not in statuses, statuses
    ran = pipeline.run(source, "f", [0 if swap else 1, 0], file=FILE)
    assert ran.trap is not None
    assert "Postcondition violation" in str(ran.trap)


# =====================================================================
# Silent members measured in review at f71c401c: each proved its
# `ensures` at Tier 1 there, and the run at the arm that lacks the
# refinement breaks it
# =====================================================================

_IDG = ("private forall<T> fn idg(@T -> @T)\n  requires(true)\n"
        "  ensures(true)\n  effects(pure)\n{\n  @T.0\n}\n\n")
_REFS = ("type PosInt = { @Int | @Int.0 > 0 };\n"
         "type NegInt = { @Int | @Int.0 < 0 };\n\n")

#: name -> (source, the function whose `ensures` is at stake, the call
#: that breaks it).
SILENT = {
    "a data type's argument through a generic": (
        _REFS + "private data Box<T> { MkBox(T) }\n\n" + _IDG
        + "public fn f(@Bool, @Int, @PosInt -> @Int)\n  requires(true)\n"
        "  ensures(@Int.result > 0)\n  effects(pure)\n{\n"
        "  let @Box<Int> = MkBox(@Int.0);\n"
        "  let @Box<PosInt> = MkBox(@PosInt.0);\n"
        "  match idg(if @Bool.0 then { @Box<Int>.0 } else { @Box<PosInt>.0 }) {\n"
        "    MkBox(@Int) -> @Int.0\n  }\n}\n",
        "f", ["f", [1, -5, 3]]),
    "a join of joins with a NegInt arm": (
        _REFS + _IDG
        + "public fn f(@Int, @PosInt, @NegInt -> @Int)\n  requires(true)\n"
        "  ensures(@Int.result > 0)\n  effects(pure)\n{\n"
        "  idg(if @Int.0 > 5 then { if @Int.0 > 2 then { @NegInt.0 } else "
        "{ @PosInt.0 } } else { @PosInt.0 })\n}\n",
        "f", ["f", [9, 5, -3]]),
    "a State handler inside an Exn handler": (
        _REFS + _IDG
        + "private fn risky(@Int -> @PosInt)\n  requires(true)\n"
        "  ensures(true)\n  effects(<Exn<Int>>)\n{\n"
        "  if @Int.0 > 0 then { @Int.0 } else { Exn.throw(@Int.0) }\n}\n\n"
        "public fn f(@Int, @PosInt -> @Int)\n  requires(true)\n"
        "  ensures(@Int.result > 0)\n  effects(pure)\n{\n"
        "  idg(handle[Exn<Int>] {\n    throw(@Int) -> { @Int.0 }\n  } in {\n"
        "    handle[State<Int>](@Int = 0) {\n"
        "      get(@Unit) -> { resume(@Int.0) },\n"
        "      put(@Int) -> { resume(()) }\n"
        "    } in {\n      risky(@Int.0)\n    }\n  })\n}\n",
        "f", ["f", [-4, 3]]),
    "Result<PosInt, NegInt> beside Result<Int, Int>": (
        _REFS + _IDG
        + "public fn f(@Bool, @Result<PosInt, NegInt>, @Result<Int, Int> -> @Int)\n"
        "  requires(true)\n  ensures(@Int.result != 0)\n  effects(pure)\n{\n"
        "  match idg(if @Bool.0 then { @Result<Int, Int>.0 } else "
        "{ @Result<PosInt, NegInt>.0 }) {\n"
        "    Ok(@Int) -> @Int.0,\n    Err(@Int) -> @Int.0\n  }\n}\n\n"
        "public fn t(@Bool, @Int -> @Int)\n  requires(true)\n  ensures(true)\n"
        "  effects(pure)\n{\n  f(@Bool.0, Ok(5), Ok(@Int.0))\n}\n",
        "f", ["t", [1, 0]]),
    "Err(@Int.0) beside a Result<PosInt, NegInt>": (
        _REFS + _IDG
        + "public fn f(@Bool, @Result<PosInt, NegInt>, @Int -> @Int)\n"
        "  requires(true)\n  ensures(@Int.result != 0)\n  effects(pure)\n{\n"
        "  match idg(if @Bool.0 then { Err(@Int.0) } else "
        "{ @Result<PosInt, NegInt>.0 }) {\n"
        "    Ok(@Int) -> @Int.0,\n    Err(@Int) -> @Int.0\n  }\n}\n\n"
        "public fn t(@Bool, @Int -> @Int)\n  requires(true)\n  ensures(true)\n"
        "  effects(pure)\n{\n  f(@Bool.0, Ok(5), @Int.0)\n}\n",
        "f", ["t", [1, 0]]),
    "Tuple<Int, Option<PosInt>> two levels down": (
        _REFS + _IDG
        + "public fn f(@Bool, @Tuple<Int, Option<PosInt>>, "
        "@Tuple<Int, Option<Int>> -> @Int)\n"
        "  requires(true)\n  ensures(@Int.result > 0)\n  effects(pure)\n{\n"
        "  match idg(if @Bool.0 then { @Tuple<Int, Option<Int>>.0 } else "
        "{ @Tuple<Int, Option<PosInt>>.0 }) {\n"
        "    Tuple(@Int, Some(@Int)) -> @Int.0,\n"
        "    Tuple(@Int, None) -> 1\n  }\n}\n\n"
        "public fn t(@Bool, @Int -> @Int)\n  requires(true)\n  ensures(true)\n"
        "  effects(pure)\n{\n  f(@Bool.0, Tuple(1, Some(5)), Tuple(1, Some(@Int.0)))\n}\n",
        "f", ["t", [1, -5]]),
}


@pytest.mark.parametrize("name", list(SILENT))
def test_repro_1716_a_join_proves_no_refinement_one_arm_lacks(name: str) -> None:
    source, fn, (entry, args) = SILENT[name]
    verified = pipeline.verify(source, file=FILE)
    assert verified.checked.ok, [(d.error_code, d.description[:90])
                                 for d in verified.checked.errors]
    statuses = [o.status for o in verified.obligations
                if o.fn_name == fn and o.kind == "ensures"]
    assert statuses and "verified" not in statuses, statuses
    ran = pipeline.run(source, entry, args, file=FILE)
    assert ran.trap is not None, source
    assert "Postcondition violation" in str(ran.trap), str(ran.trap)


_LITERAL_COST = _REFS + _IDG + """\
public fn f(@Option<PosInt> -> @Int)
  requires(true)
  ensures(@Int.result > 0)
  effects(pure)
{
  BODY
}
"""


def test_repro_1716_the_cost_a_literal_arm_through_a_generic() -> None:
    """The rule's cost: a literal arm beside a refined arm, handed to a
    generic with no expected type, is instantiated at the base, so a
    `let @PosInt` of the call is a run-time check (`tier3`, E506) where at
    f71c401c it read `verified`; bound at the refined type first and then
    passed, the join keeps its proof."""
    through = _LITERAL_COST.replace("BODY", (
        "let @PosInt = idg(match @Option<PosInt>.0 {\n"
        "    Some(@PosInt) -> @PosInt.0,\n    None -> 1\n  });\n  @PosInt.0"))
    verified = pipeline.verify(through, file=FILE)
    rows = sorted((o.kind, o.status, o.error_code) for o in verified.obligations
                  if o.fn_name == "f" and o.kind in ("refine_bind", "ensures"))
    assert ("refine_bind", "tier3", "E506") in rows, rows
    assert ("ensures", "verified", "") in rows, rows
    bound_first = _LITERAL_COST.replace("BODY", (
        "let @PosInt = match @Option<PosInt>.0 {\n"
        "    Some(@PosInt) -> @PosInt.0,\n    None -> 1\n  };\n"
        "  idg(@PosInt.0)"))
    verified = pipeline.verify(bound_first, file=FILE)
    assert verified.ok, [(d.error_code, d.description[:90])
                         for d in verified.errors]
    rows = sorted((o.kind, o.status, o.expr_text) for o in verified.obligations
                  if o.fn_name == "f" and o.kind in ("refine_bind", "ensures"))
    # the binder's own row is the sub-pattern's guard, as at f71c401c
    assert rows == [("ensures", "verified", "@Int.result > 0"),
                    ("refine_bind", "tier3", "@PosInt"),
                    ("refine_bind", "verified",
                     "match @Option<PosInt>.0 { Some(@PosInt) -> @PosInt.0, "
                     "None -> 1 }")], rows


def test_a_handler_whose_body_is_refused_has_its_clauses_type() -> None:
    """A handler whose body the check refused (`Unknown`) has its clause's
    type, so a `let` of another type still reports the mismatch (E170)."""
    source = ("public fn f(@Int -> @Int)\n  requires(true)\n  ensures(true)\n"
              "  effects(pure)\n{\n  let @Int = handle[Exn<Int>] {\n"
              '    throw(@Int) -> { "s" }\n  } in {\n    @Bool.0\n  };\n'
              "  @Int.0\n}\n")
    checked = pipeline.check(source, file=FILE)
    assert [d.error_code for d in checked.errors] == ["E130", "E170"]
    assert "value has type String" in checked.errors[1].description


#: Each branch of the `Exn` handler's join, unparametrised so every pull
#: request runs it: (the function's parameters and return, the clause's
#: value, the handled body, the handler's record).
HANDLER_BRANCHES = [
    # the clause a subtype of the body: the facts both state
    ("@Int, @PosInt -> @Int", "@PosInt.0", "@Int.0", "Int"),
    ("@PosInt -> @Int", "@PosInt.0", "@PosInt.0", "{Int|PosInt}"),
    # the body always throws: the clause's type
    ("@PosInt -> @Int", "@PosInt.0", 'throw("x")', "{Int|PosInt}"),
    # the clause throws again: the body's type
    ("@PosInt -> @Int", 'throw("y")', "@PosInt.0", "{Int|PosInt}"),
    # an open position on either side, filled from the other
    ("@PosInt -> @Option<PosInt>", "None", "Some(@PosInt.0)",
     "Option<{Int|PosInt}>"),
    ("@PosInt -> @Option<PosInt>", "Some(@PosInt.0)", "None",
     "Option<{Int|PosInt}>"),
]


def test_repro_1716_every_branch_of_the_handler_join() -> None:
    for signature, clause, body, expected in HANDLER_BRANCHES:
        params, ret = signature.split(" -> ")
        source = (_HEAD + f"private fn j({params} -> {ret})\n"
                  "  requires(true)\n  ensures(true)\n"
                  "  effects(<Exn<String>>)\n{\n"
                  f"  handle[Exn<String>] {{\n    throw(@String) -> {{ {clause} }}\n"
                  f"  }} in {{\n    {body}\n  }}\n}}\n")
        assert _recorded(source, ast.HandleExpr) == [expected], (
            signature, clause, body)


def test_repro_1716_a_handler_clause_the_check_refused_takes_no_part() -> None:
    """A clause whose value the check refused (`Unknown`) leaves the
    handler at its body's type, so a `let` of another type reports the
    mismatch against the body (E170 naming `String`)."""
    source = ("public fn f(@Int -> @Int)\n  requires(true)\n  ensures(true)\n"
              "  effects(pure)\n{\n  let @Int = handle[Exn<Int>] {\n"
              "    throw(@Int) -> { @Bool.0 }\n  } in {\n"
              '    "s"\n  };\n  @Int.0\n}\n')
    checked = pipeline.check(source, file=FILE)
    assert [d.error_code for d in checked.errors] == ["E130", "E170"]
    assert "value has type String" in checked.errors[1].description


def test_a_refused_clause_beside_a_throwing_body_reports_what_it_did() -> None:
    """A clause the check refused beside a body that always throws makes
    the handler the checker's unknown (at f71c401c it stayed `Never`):
    either silences what follows, so the program reports the clause's own
    error and nothing more, as it did there."""
    source = ("public fn f(@Int -> @Int)\n  requires(true)\n  ensures(true)\n"
              "  effects(pure)\n{\n  let @String = handle[Exn<Int>] {\n"
              "    throw(@Int) -> { @Bool.0 }\n  } in {\n    throw(1)\n  };\n"
              "  @Int.0\n}\n")
    checked = pipeline.check(source, file=FILE)
    assert [d.error_code for d in checked.errors] == ["E130"]


def test_repro_1716_a_clause_no_position_reconciles_is_refused_whole() -> None:
    """A clause whose value no position of the body's type reconciles is
    refused at the clause (E341), every field of the diagnostic as at
    f71c401c."""
    source = ("public fn f(@Int -> @Result<Int, Int>)\n  requires(true)\n"
              "  ensures(true)\n  effects(pure)\n{\n  handle[Exn<Int>] {\n"
              "    throw(@Int) -> { Some(5) }\n  } in {\n    Ok(@Int.0)\n"
              "  }\n}\n")
    checked = pipeline.check(source, file=FILE)
    (found,) = [d for d in checked.errors if d.error_code == "E341"]
    assert (found.location.line, found.location.column) == (7, 22)
    assert found.description == (
        "The 'throw' clause's value has type Option<Int>, but the "
        "handler's value is Result<Int, ?>.")
    assert found.rationale == (
        "An Exn handler's value is its handled body's, or, when the body "
        "throws, the clause's: the two are one value, so they have one "
        "type, as the branches of an if do.")
    assert found.fix == (
        "Make the clause's value the handled body's type, Result<Int, ?>: "
        "replace 'Some(5)' with 'Ok(0)', or give the handled body the "
        "clause's type.")
    assert found.spec_ref == 'Chapter 7, Section 7.5.2 "Handler Semantics"'


_RIGID = """\
type Kept<T> = {{ @T | true }};

private forall<T> fn j(@Bool, @T, @Kept<T> -> @T)
  requires(true)
  ensures(true)
  effects(pure)
{{
  if @Bool.0 then {{ {first} }} else {{ {second} }}
}}
"""


@pytest.mark.parametrize("swap", [False, True], ids=["bare first", "refined first"])
def test_repro_1716_a_rigid_type_variable_states_its_own_refinements(
        swap: bool) -> None:
    """The enclosing function's own type variable is no open position: a
    bare `@T` arm beside a refined `@Kept<T>` arm states no refinement, so
    the join is a bare `T` in either order (at review round 4's head the
    refined arm second kept its refinement)."""
    first, second = (("@Kept<T>.0", "@T.0") if swap
                     else ("@T.0", "@Kept<T>.0"))
    source = _RIGID.format(first=first, second=second)
    assert _recorded(source, ast.IfExpr) == ["'T"]


_EFFECT_FORMS = {
    "if": "if @Bool.0 then {{\n    {first}\n  }} else {{\n    {second}\n  }}",
    "match": ("match @Bool.0 {{\n    true -> {first},\n"
              "    false -> {second}\n  }}"),
    "handler": ("handle[Exn<String>] {{\n    throw(@String) -> {{ {second} }}\n"
                "  }} in {{\n    if @Bool.0 then {{ {first} }} else "
                "{{ throw(\"x\") }}\n  }}"),
}

_CLOSURE = "fn(@Int -> @Int) effects({row}) {{ @Int.0 }}"


def _recorded_type(source: str, kind: type[ast.Expr]) -> Type | None:
    checked = pipeline.check(source, file=FILE)
    assert checked.ok, [(d.error_code, d.description[:90])
                        for d in checked.errors]
    types = checked.artifacts.node_semantic_types
    for tl in checked.program.declarations:
        decl = getattr(tl, "decl", tl)
        if isinstance(decl, ast.FnDecl):
            for node in fold.walk(decl.body):
                if isinstance(node, kind):
                    return types.get(node.node_id)
    return None


@pytest.mark.parametrize("form", list(_EFFECT_FORMS))
@pytest.mark.parametrize("rows", [("pure", "<IO>"), ("<IO>", "pure")],
                         ids=["pure first", "io first"])
def test_repro_1716_function_arms_of_two_effect_rows_join_at_the_wider(
        form: str, rows: tuple[str, str]) -> None:
    """Function-typed arms whose effect rows differ: the walk joins in the
    direction a row widens, so the join is accepted with the `<IO>` row in
    either order (`_join_either`).  At review round 3's head the handler
    refused the wider clause (E341); at f71c401c a `match` with the pure
    arm first was recorded pure."""
    first, second = (_CLOSURE.format(row=r) for r in rows)
    body = _EFFECT_FORMS[form].format(first=first, second=second)
    source = ("type IOF = fn(Int -> Int) effects(<IO>);\n\n"
              "private fn j(@Bool -> @IOF)\n  requires(true)\n"
              "  ensures(true)\n  effects(pure)\n{\n  " + body + "\n}\n")
    kind = {"if": ast.IfExpr, "match": ast.MatchExpr,
            "handler": ast.HandleExpr}[form]
    recorded = _recorded_type(source, kind)
    assert isinstance(recorded, FunctionType), recorded
    assert isinstance(recorded.effect, ConcreteEffectRow), recorded
    assert {e.name for e in recorded.effect.effects} == {"IO"}, recorded


_HIGHER = """\
type PF = fn(Int -> Int) effects(pure);
type IOF = fn(Int -> Int) effects(<IO>);
type Wide = fn(PF -> IOF) effects(pure);
type Narrow = fn(IOF -> PF) effects(pure);

private fn j(@Bool, @Wide, @Narrow -> @Wide)
  requires(true)
  ensures(true)
  effects(<Exn<String>>)
{{
  {body}
}}
"""

_HIGHER_FORMS = {
    "if": "if @Bool.0 then {{ {first} }} else {{ {second} }}",
    "match": "match @Bool.0 {{\n    true -> {first},\n    false -> {second}\n  }}",
    "handler": ("handle[Exn<String>] {{\n    throw(@String) -> {{ {second} }}\n"
                "  }} in {{\n    if @Bool.0 then {{ {first} }} else "
                "{{ throw(\"x\") }}\n  }}"),
}


def _row_names(row: object) -> set[str]:
    if isinstance(row, ConcreteEffectRow):
        return {e.name for e in row.effects}
    return set()


@pytest.mark.parametrize("form", list(_HIGHER_FORMS))
@pytest.mark.parametrize("swap", [False, True], ids=["wide first", "narrow first"])
def test_repro_1716_a_join_the_walk_takes_neither_way_is_the_supertype(
        form: str, swap: bool) -> None:
    """`fn(PF -> IOF)` beside `fn(IOF -> PF)`: the second is a subtype of
    the first, and the walk joins neither way (a parameter's row is read
    contravariantly), so the join is the supertype, `fn(PF -> IOF)`, in
    either order.  At f71c401c a `match` with the subtype first was
    recorded at the subtype, whose result claims a pure function."""
    first, second = (("@Narrow.0", "@Wide.0") if swap
                     else ("@Wide.0", "@Narrow.0"))
    body = _HIGHER_FORMS[form].format(first=first, second=second)
    kind = {"if": ast.IfExpr, "match": ast.MatchExpr,
            "handler": ast.HandleExpr}[form]
    recorded = _recorded_type(_HIGHER.format(body=body), kind)
    assert isinstance(recorded, FunctionType), recorded
    (param,) = recorded.params
    assert isinstance(param, FunctionType) and isinstance(
        recorded.return_type, FunctionType), recorded
    assert _row_names(param.effect) == set(), recorded
    assert _row_names(recorded.return_type.effect) == {"IO"}, recorded


_EFFECT_LEAK = """\
type IOF = fn(Int -> Int) effects(<IO>);

private fn f(@Bool, @IOF, @Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  apply_fn(match @Bool.0 {
    true -> fn(@Int -> @Int) effects(pure) {
      @Int.0
    },
    false -> @IOF.0
  }, @Int.0)
}

public fn main(-> @Unit)
  requires(true)
  ensures(true)
  effects(<IO>)
{
  let @Int = f(false, fn(@Int -> @Int) effects(<IO>) {
    IO.print("leaked\\n");
    @Int.0
  }, 7);
  ()
}
"""


def test_repro_1716_a_pure_function_applies_no_io_arm_of_a_match() -> None:
    """A `match` whose pure-function arm comes first and whose other arm is
    an `<IO>` function has the `<IO>` row, so applying it in a function
    declared `effects(pure)` is refused (E125).  At f71c401c the `match`
    was recorded pure, `vera check` accepted the program, and `vera run`
    printed `leaked` from a pure function."""
    checked = pipeline.check(_EFFECT_LEAK, file=FILE)
    assert "E125" in [d.error_code for d in checked.errors], [
        (d.error_code, d.description[:80]) for d in checked.errors]


# =====================================================================
# The if's own joins, and the literal strengthening, one cell each
# =====================================================================

_THROWING_PAYLOAD = """\
private fn j(@Bool -> @Option<Int>)
  requires(true)
  ensures(true)
  effects(<Exn<Int>>)
{{
  if @Bool.0 then {{ {first} }} else {{ {second} }}
}}
"""


def test_repro_1716_a_branch_whose_payload_throws_joins_onto_the_other() -> None:
    """`Some(throw(1))` is an `Option<Never>`, a subtype of the `None`
    branch's `Option<Int>`: the then branch joined onto the else branch
    gives the `if` `Option<Int>`, in either order.  The else branch joined
    onto the then branch, the general path's first join, gives
    `Option<Never>`, a type whose payload no value has."""
    for first, second in (("Some(throw(1))", "None"),
                          ("None", "Some(throw(1))")):
        source = _THROWING_PAYLOAD.format(first=first, second=second)
        assert _recorded(source, ast.IfExpr) == ["Option<Int>"], first


_TWO_LOST = """\
private forall<T> fn first(@Array<T> -> @T)
  requires(array_length(@Array<T>.0) > 0)
  ensures(true)
  effects(pure)
{{
  @Array<T>.0[0]
}}

public fn f(@Bool -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{{
  array_length(if @Bool.0 then {{ {first} }} else {{ {second} }})
}}
"""


def test_repro_1716_two_lost_builtin_variables_take_the_then_branch() -> None:
    """Two built-ins' variables a failed substitution lost (`array_map`'s
    `B`, `map_values`'s `V` and `map_keys`'s `K` beside an argument nothing
    types): the join fills neither, the branches fit with each variable a
    wildcard, and the `if` is accepted at its then branch's type, as two
    open branches always gave."""
    for first, second, expected in (
            ("array_map([1], first([]))", "map_values(first([]))",
             "Array<'B#b>"),
            ("map_keys(first([]))", "array_map([1], first([]))",
             "Array<'K#b>")):
        source = _TWO_LOST.format(first=first, second=second)
        assert _recorded(source, ast.IfExpr) == [expected], first


def _int_gt_zero() -> RefinedType:
    return RefinedType(INT, ast.BinaryExpr(
        op=ast.BinOp.GT, left=ast.SlotRef(type_name="Int", type_args=None,
                                          index=0),
        right=ast.IntLit(value=0)))


def test_repro_1716_a_literal_before_a_refined_leaf_is_held_to_it() -> None:
    """A literal leaf ahead of a refined leaf: the strengthening reads every
    leaf, so the join is at the refined leaf's type, the literal asked of
    it once."""
    pos = _int_gt_zero()
    lit = ast.IntLit(value=1)
    slot = ast.SlotRef(type_name="PosInt", type_args=None, index=0)
    join = ast.IfExpr(condition=ast.BoolLit(value=True), then_branch=lit,
                      else_branch=slot)
    types: dict[int, Type] = {id(lit): INT, id(slot): pos, id(join): INT}
    asked: list[tuple[ast.Expr, Type]] = []

    def holds(leaf: ast.Expr, ty: Type) -> bool:
        asked.append((leaf, ty))
        return True

    got = narrowing.established_type(join, lambda e: types.get(id(e)), holds)
    assert got is pos, got
    assert asked == [(lit, pos)], asked


def test_repro_1716_a_literal_at_the_shared_type_is_asked_nothing() -> None:
    """A literal leaf whose own type is the other leaves' type shares it
    without a probe: the join is at that type, *holds* never asked."""
    lit = ast.IntLit(value=1)
    slot = ast.SlotRef(type_name="Int", type_args=None, index=0)
    join = ast.IfExpr(condition=ast.BoolLit(value=True), then_branch=lit,
                      else_branch=slot)
    types: dict[int, Type] = {id(lit): INT, id(slot): INT, id(join): INT}
    asked: list[tuple[ast.Expr, Type]] = []

    def holds(leaf: ast.Expr, ty: Type) -> bool:
        asked.append((leaf, ty))
        return False

    got = narrowing.established_type(join, lambda e: types.get(id(e)), holds)
    assert got == INT, got
    assert asked == [], asked


# =====================================================================
# A function type's parameter is what the join accepts
# =====================================================================

_ACCEPTING = """\
type IntToInt = fn(Int -> Int) effects(pure);
type NatToInt = fn(Nat -> Int) effects(pure);

private fn pick(@Bool, @IntToInt, @NatToInt, @Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{{
  apply_fn(if @Bool.0 then {{ {first} }} else {{ {second} }}, @Int.0)
}}

public fn f(@Bool, @Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{{
  let @IntToInt = fn(@Int -> @Int) effects(pure) {{ @Int.0 }};
  let @NatToInt = fn(@Nat -> @Int) effects(pure) {{ @Nat.0 }};
  pick(@Bool.0, @IntToInt.0, @NatToInt.0, @Int.0)
}}
"""


@pytest.mark.parametrize("swap", [False, True], ids=["int first", "nat first"])
def test_repro_1716_a_join_of_functions_accepts_what_every_arm_accepts(
        swap: bool) -> None:
    """`fn(Int -> Int)` beside `fn(Nat -> Int)`, applied to an `@Int`: the
    argument must suit whichever arm the join is, so the join's parameter
    is the `Nat` both accept, and binding the `@Int` into it is a `Nat`
    narrowing, refused (E503) where it can be negative, in either order.
    Read by the value rule (a `Nat` beside an `Int` is an `Int`) the join
    was `fn(Int -> Int)` with the `Int` arm first: no row, and
    `f(false, -5)` handed the `Nat` closure -5 and printed it."""
    first, second = (("@NatToInt.0", "@IntToInt.0") if swap
                     else ("@IntToInt.0", "@NatToInt.0"))
    source = _ACCEPTING.format(first=first, second=second)
    verified = pipeline.verify(source, file=FILE)
    rows = [(o.kind, o.status) for o in verified.obligations
            if o.fn_name == "pick" and o.kind == "nat_bind"]
    assert rows == [("nat_bind", "violated")], rows
    assert [d.error_code for d in verified.errors] == ["E503"], [
        (d.error_code, d.description[:80]) for d in verified.errors]
    ran = pipeline.run(source, "f", [1 if swap else 0, -5], file=FILE)
    assert ran.trap is not None, ran


_FN_FORMS = {
    "if": "if @Bool.0 then {{ {first} }} else {{ {second} }}",
    "match": ("match @Bool.0 {{\n    true -> {first},\n"
              "    false -> {second}\n  }}"),
    "handler": ("handle[Exn<String>] {{\n    throw(@String) -> {{ {second} }}\n"
                "  }} in {{\n    if @Bool.0 then {{ {first} }} else "
                "{{ throw(\"x\") }}\n  }}"),
}

_FN_ALIASES = """\
type Small = {{ @Int | @Int.0 < 10 }};
type Tiny = {{ @Small | @Small.0 > 0 }};
type Pos = {{ @Int | @Int.0 > 0 }};
type SmallNat = {{ @Nat | @Nat.0 < 10 }};
type NatF = fn(Nat -> Int) effects(pure);
type IntF = fn(Int -> Int) effects(pure);
type A = {a} effects(pure);
type B = {b} effects(pure);
type C = {c} effects(pure);

"""

#: (arm A's type, arm B's type, the join's type as written, its record in
#: either order)
_FN_POLARITY = [
    # a parameter accepts what every arm accepts
    ("fn(Int -> Int)", "fn(Nat -> Int)", "fn(Nat -> Int)", "fn(Nat -> Int)"),
    # a parameter's own parameter is a value again
    ("fn(NatF -> Int)", "fn(IntF -> Int)", "fn(IntF -> Int)",
     "fn(fn(Int -> Int) -> Int)"),
    # a data type's argument under a parameter keeps the parameter's side
    ("fn(Option<Int> -> Int)", "fn(Option<Nat> -> Int)",
     "fn(Option<Nat> -> Int)", "fn(Option<Nat> -> Int)"),
    # a return is a value: the facts both state
    ("fn(Int -> Nat)", "fn(Int -> Int)", "fn(Int -> Int)", "fn(Int -> Int)"),
    # a refined parameter beside its base: the refined one, both accept it
    ("fn(Int -> Int)", "fn(Small -> Int)", "fn(Small -> Int)",
     "fn({Int|Small} -> Int)"),
    # nested refinements: the longest chain, one arm's own
    ("fn(Small -> Int)", "fn(Tiny -> Int)", "fn(Tiny -> Int)",
     "fn({{Int|Small}|Tiny} -> Int)"),
    # a `Nat` beside a refined `Int`: a plain `Nat`, no chain moved onto
    # another base
    ("fn(Small -> Int)", "fn(Nat -> Int)", "fn(Nat -> Int)", "fn(Nat -> Int)"),
    # a refinement over `Nat` beside an `Int`: its own chain, on the `Nat`
    ("fn(SmallNat -> Int)", "fn(Int -> Int)", "fn(SmallNat -> Int)",
     "fn({Nat|SmallNat} -> Int)"),
    # two predicates at one level: no new chain, the base
    ("fn(Small -> Int)", "fn(Pos -> Int)", "fn(Int -> Int)", "fn(Int -> Int)"),
]


def _fn_join(form: str, row: tuple[str, str, str, str], swap: bool) -> str:
    a, b, c, _ = row
    first, second = ("@B.0", "@A.0") if swap else ("@A.0", "@B.0")
    body = _FN_FORMS[form].format(first=first, second=second)
    return (_FN_ALIASES.format(a=a, b=b, c=c)
            + "private fn j(@Bool, @A, @B -> @C)\n  requires(true)\n"
            "  ensures(true)\n  effects(<Exn<String>>)\n{\n"
            f"  {body}\n}}\n")


@pytest.mark.parametrize("form", list(_FN_FORMS))
@pytest.mark.parametrize("swap", [False, True], ids=["ab", "ba"])
@pytest.mark.parametrize("row", _FN_POLARITY, ids=[
    "param", "nested", "data", "return", "refined", "chain", "mixed",
    "smallnat", "not-nested"])
def test_a_function_join_reads_a_parameter_as_accepting(
        form: str, swap: bool, row: tuple[str, str, str, str]) -> None:
    kind = {"if": ast.IfExpr, "match": ast.MatchExpr,
            "handler": ast.HandleExpr}[form]
    assert _recorded(_fn_join(form, row, swap), kind) == [row[3]]


def test_repro_1716_the_join_s_parameter_polarity_every_cell() -> None:
    """Every polarity row of `test_a_function_join_reads_a_parameter_as_accepting`
    at the `if`, in both orders, unparametrised so every pull request runs
    it."""
    for row in _FN_POLARITY:
        for swap in (False, True):
            assert _recorded(_fn_join("if", row, swap), ast.IfExpr) == [
                row[3]], (row, swap)


_REFINED_ACCEPTING = """\
type Small = {{ @Int | @Int.0 < 10 }};
type Pos = {{ @Int | @Int.0 > 0 }};
type IntToInt = fn(Int -> Int) effects(pure);
type Other = fn({other} -> Int) effects(pure);

private fn pick(@Bool, @IntToInt, @Other, @Int -> @Int)
  requires({guard})
  ensures(true)
  effects(pure)
{{
  apply_fn(if @Bool.0 then {{ {first} }} else {{ {second} }}, @Int.0)
}}

public fn f(@Bool, @Int -> @Int)
  requires({guard})
  ensures(true)
  effects(pure)
{{
  let @IntToInt = fn(@Int -> @Int) effects(pure) {{ @Int.0 }};
  let @Other = fn(@{other} -> @Int) effects(pure) {{ 0 }};
  pick(@Bool.0, @IntToInt.0, @Other.0, @Int.0)
}}
"""


def _refined_accepting(other: str, guard: str, swap: bool) -> str:
    first, second = (("@Other.0", "@IntToInt.0") if swap
                     else ("@IntToInt.0", "@Other.0"))
    return _REFINED_ACCEPTING.format(other=other, guard=guard, first=first,
                                     second=second)


@pytest.mark.parametrize("swap", [False, True], ids=["int first", "small first"])
def test_repro_1716_a_join_of_functions_obligates_a_refined_parameter(
        swap: bool) -> None:
    """`fn(Int -> Int)` beside `fn(Small -> Int)` accepts a `Small`, so an
    `@Int` argument is a refinement narrowing at `apply_fn`: refused
    (E505) where nothing bounds it, `verified` under `requires(@Int.0 <
    10)`, in either order.  Read as the shared prefix the parameter was an
    `Int`: no row, and the argument 50 reached the `Small` closure's entry
    check at run time."""
    open_ = pipeline.verify(_refined_accepting("Small", "true", swap),
                            file=FILE)
    rows = [(o.kind, o.status) for o in open_.obligations
            if o.fn_name == "pick" and o.kind == "refine_bind"]
    assert rows == [("refine_bind", "violated")], rows
    assert [d.error_code for d in open_.errors] == ["E505"], [
        (d.error_code, d.description[:80]) for d in open_.errors]
    guarded = pipeline.verify(_refined_accepting("Small", "@Int.0 < 10", swap),
                              file=FILE)
    rows = [(o.kind, o.status) for o in guarded.obligations
            if o.fn_name == "pick" and o.kind == "refine_bind"]
    assert rows == [("refine_bind", "verified")], rows
    assert guarded.errors == (), [(d.error_code, d.description[:80])
                                  for d in guarded.errors]


_MIXED = """\
type Small = {{ @Int | @Int.0 < 10 }};
type SmallToInt = fn(Small -> Int) effects(pure);
type NatToInt = fn(Nat -> Int) effects(pure);

private fn pick(@Bool, @SmallToInt, @NatToInt, @Int -> @Int)
  requires({guard})
  ensures(true)
  effects(pure)
{{
  apply_fn(if @Bool.0 then {{ {first} }} else {{ {second} }}, @Int.0)
}}

public fn f(@Bool, @Int -> @Int)
  requires({guard})
  ensures(true)
  effects(pure)
{{
  let @SmallToInt = fn(@Small -> @Int) effects(pure) {{ @Small.0 }};
  let @NatToInt = fn(@Nat -> @Int) effects(pure) {{ @Nat.0 }};
  pick(@Bool.0, @SmallToInt.0, @NatToInt.0, @Int.0)
}}
"""


@pytest.mark.parametrize("swap", [False, True], ids=["small first", "nat first"])
def test_repro_1716_a_nat_parameter_beside_a_refined_int_is_a_plain_nat(
        swap: bool) -> None:
    """`fn(Small -> Int)` beside `fn(Nat -> Int)`: the parameter is a plain
    `Nat` (no chain moved onto another base), so an unconstrained `@Int`
    argument is refused (E503) in either order; under `requires(@Int.0 >=
    0)` it verifies, and 50 handed to the `Small` closure traps in its
    entry check."""
    first, second = (("@NatToInt.0", "@SmallToInt.0") if swap
                     else ("@SmallToInt.0", "@NatToInt.0"))
    open_ = pipeline.verify(_MIXED.format(guard="true", first=first,
                                          second=second), file=FILE)
    assert [d.error_code for d in open_.errors] == ["E503"], [
        (d.error_code, d.description[:80]) for d in open_.errors]
    guarded = _MIXED.format(guard="@Int.0 >= 0", first=first, second=second)
    verified = pipeline.verify(guarded, file=FILE)
    assert verified.errors == (), [(d.error_code, d.description[:80])
                                   for d in verified.errors]
    ran = pipeline.run(guarded, "f", [0 if swap else 1, 50], file=FILE)
    assert ran.trap is not None, ran
    assert "Refinement violation" in str(ran.trap), str(ran.trap)


_OVERFLOW_PREDICATE = """\
type Small = { @Int | @Int.0 * @Int.0 * @Int.0 * @Int.0 * @Int.0 < 100000 };
type SmallToInt = fn(Small -> Int) effects(pure);
type IntToInt = fn(Int -> Int) effects(pure);

private fn pick(@Bool, @SmallToInt, @IntToInt, @Int, @Int -> @Int)
  requires(@Int.1 >= 0 && @Int.1 < 5)
  ensures(true)
  effects(pure)
{
  apply_fn(if @Bool.0 then { @SmallToInt.0 } else { @IntToInt.0 }, @Int.1)
}

public fn f(@Bool, @Int -> @Int)
  requires(@Int.0 >= 0 && @Int.0 < 5)
  ensures(true)
  effects(pure)
{
  let @SmallToInt = fn(@Small -> @Int) effects(pure) { @Small.0 };
  let @IntToInt = fn(@Int -> @Int) effects(pure) { @Int.0 };
  pick(@Bool.0, @SmallToInt.0, @IntToInt.0, @Int.0, 1)
}
"""


@pytest.mark.xfail(strict=True, reason=(
    "#1861: apply_fn of a non-slot function value loses the checks of a "
    "refined parameter's arithmetic (E541)"))
@pytest.mark.parametrize("swap", [False, True], ids=["small first", "int first"])
def test_repro_1716_a_refined_parameter_join_reconciles_clean(
        swap: bool) -> None:
    """A join of a `Small`-taking and an `Int`-taking closure, applied to
    an argument the `requires` puts in range, verifies with a clean
    reconciliation (no E541), once issue #1861 is fixed: `apply_fn` of the
    join itself loses the checks of `Small`'s arithmetic, as it does where
    both arms are `Small`-taking; bound by a `let` first, the join
    reconciles."""
    source = _OVERFLOW_PREDICATE
    if swap:
        source = source.replace(
            "if @Bool.0 then { @SmallToInt.0 } else { @IntToInt.0 }",
            "if @Bool.0 then { @IntToInt.0 } else { @SmallToInt.0 }")
    verified = pipeline.verify(source, file=FILE, reconcile=True)
    assert verified.errors == (), [(d.error_code, d.description[:80])
                                   for d in verified.errors]
    assert {d.error_code for d in verified.diagnostics} & {
        "E541", "W004"} == set()


@pytest.mark.parametrize("swap", [False, True], ids=["small first", "pos first"])
def test_repro_1716_two_parameter_predicates_build_no_new_chain(
        swap: bool) -> None:
    """`fn(Small -> Int)` beside `fn(Pos -> Int)`: the predicates differ at
    one level, so the join's parameter is the base `Int`, no row is listed
    at the argument, and each closure's entry check holds its own
    predicate: 50 handed to the `Small` closure traps there (issue #1819
    revisits this remainder)."""
    source = _refined_accepting("Small", "true", swap).replace(
        "type IntToInt = fn(Int -> Int)", "type IntToInt = fn(Pos -> Int)"
    ).replace("fn(@Int -> @Int) effects(pure) { @Int.0 }",
              "fn(@Pos -> @Int) effects(pure) { @Pos.0 }")
    verified = pipeline.verify(source, file=FILE)
    assert verified.errors == (), [(d.error_code, d.description[:80])
                                   for d in verified.errors]
    rows = [(o.kind, o.status) for o in verified.obligations
            if o.fn_name == "pick" and o.kind == "refine_bind"]
    assert rows == [], rows
    ran = pipeline.run(source, "f", [1 if swap else 0, 50], file=FILE)
    assert ran.trap is not None, ran
    assert "Refinement violation" in str(ran.trap), str(ran.trap)


_ROW_JOIN = """\
type CbA = fn(Int -> Int) effects({ra});
type CbB = fn(Int -> Int) effects({rb});
type TakesA = fn(CbA -> Int) effects({ra});
type TakesB = fn(CbB -> Int) effects({rb});

private fn j(@Bool, @TakesA, @TakesB -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{{
  if @Bool.0 then {{ {first} }} else {{ {second} }};
  0
}}
"""

#: (callback row A, callback row B, the join's callback row in either order)
_ROWS = [
    ("pure", "<IO>", set()),
    ("<IO, State<Int>>", "<IO>", {"IO"}),
    ("<IO, State<Int>>", "pure", set()),
]


def test_repro_1716_a_callback_parameter_accepts_the_row_every_arm_accepts() -> None:
    """A function taking a callback of one row beside one taking a callback
    of another: the join's callback parameter has the effects both rows
    name, in either order (`pure` beside `<IO>` is `pure`;
    `<IO, State<Int>>` beside `<IO>`, `<IO>`; beside `pure`, `pure`)."""
    for ra, rb, expected in _ROWS:
        for first, second in (("@TakesA.0", "@TakesB.0"),
                              ("@TakesB.0", "@TakesA.0")):
            source = _ROW_JOIN.format(ra=ra, rb=rb, first=first,
                                      second=second)
            recorded = _recorded_type(source, ast.IfExpr)
            assert isinstance(recorded, FunctionType), recorded
            (param,) = recorded.params
            assert isinstance(param, FunctionType), recorded
            assert _row_names(param.effect) == expected, (ra, rb, first)
    # Two disjoint rows (`<IO>` beside `<State<Int>>`): neither function
    # type is a subtype of the other, so the join refuses the pair (E301)
    # before any fact is read, as at 918f95b6.
    disjoint = _ROW_JOIN.format(ra="<IO>", rb="<State<Int>>",
                                first="@TakesA.0", second="@TakesB.0")
    assert [d.error_code for d in pipeline.check(disjoint, file=FILE).errors
            ] == ["E301"]


_ROW_APPLY = """\
type PureCb = fn(Int -> Int) effects(pure);
type IoCb = fn(Int -> Int) effects(<IO>);
type TakesPure = fn(PureCb -> Int) effects(pure);
type TakesIo = fn(IoCb -> Int) effects(<IO>);

private fn pick(@Bool, @TakesPure, @TakesIo, @{cb} -> @Int)
  requires(true)
  ensures(true)
  effects(<IO>)
{{
  apply_fn(if @Bool.0 then {{ {first} }} else {{ {second} }}, @{cb}.0)
}}

public fn f(@Bool, @Int -> @Int)
  requires(true)
  ensures(true)
  effects(<IO>)
{{
  let @TakesPure = fn(@PureCb -> @Int) effects(pure) {{ apply_fn(@PureCb.0, 1) }};
  let @TakesIo = fn(@IoCb -> @Int) effects(<IO>) {{ apply_fn(@IoCb.0, 2) }};
  let @{cb} = fn(@Int -> @Int) effects({row}) {{ {body} }};
  pick(@Bool.0, @TakesPure.0, @TakesIo.0, @{cb}.0)
}}
"""


@pytest.mark.parametrize("swap", [False, True], ids=["pure first", "io first"])
def test_repro_1716_a_pure_function_is_handed_no_io_callback_through_a_join(
        swap: bool) -> None:
    """`fn(PureCb -> Int)` beside `fn(IoCb -> Int)` takes a `PureCb`, so
    `apply_fn` of the join to an `<IO>` callback is refused (E202) in
    either order, as it is passed to the pure function directly; a pure
    callback is accepted and runs.  At f71c401c, and at 918f95b6, both
    orders were accepted and the `effects(pure)` closure ran the `<IO>`
    callback, printing `io ran`."""
    first, second = (("@TakesIo.0", "@TakesPure.0") if swap
                     else ("@TakesPure.0", "@TakesIo.0"))
    io = _ROW_APPLY.format(cb="IoCb", row="<IO>", first=first, second=second,
                           body='IO.print("io ran\\n");\n    @Int.0')
    checked = pipeline.check(io, file=FILE)
    assert [d.error_code for d in checked.errors] == ["E202"], [
        (d.error_code, d.description[:80]) for d in checked.errors]
    pure = _ROW_APPLY.format(cb="PureCb", row="pure", first=first,
                             second=second, body="@Int.0 + 1")
    assert pipeline.check(pure, file=FILE).ok
    # the then branch runs: `TakesPure` applies the callback to 1,
    # `TakesIo` to 2
    ran = pipeline.run(pure, "f", [1, 4], file=FILE)
    assert ran.trap is None and ran.value == (3 if swap else 2), ran


_DOUBLE_FLIP = """\
type PureCb = fn(Int -> Int) effects(pure);
type IoCb = fn(Int -> Int) effects(<IO>);
type GivesPure = fn(PureCb -> Int) effects(pure);
type GivesIo = fn(IoCb -> Int) effects(pure);
type A = fn(GivesPure -> Int) effects(pure);
type B = fn(GivesIo -> Int) effects(pure);

private fn j(@Bool, @A, @B -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{{
  if @Bool.0 then {{ {first} }} else {{ {second} }};
  0
}}
"""


def test_repro_1716_a_callback_s_own_callback_keeps_the_wider_row() -> None:
    """Under two flips the position holds a value again: the parameter of
    the callback parameter has the join's row, the wider `<IO>`, in either
    order, so the callback the joined function is handed may be given an
    `<IO>` function."""
    for first, second in (("@A.0", "@B.0"), ("@B.0", "@A.0")):
        recorded = _recorded_type(
            _DOUBLE_FLIP.format(first=first, second=second), ast.IfExpr)
        assert isinstance(recorded, FunctionType), recorded
        (given,) = recorded.params
        assert isinstance(given, FunctionType), recorded
        (inner,) = given.params
        assert isinstance(inner, FunctionType), recorded
        assert _row_names(inner.effect) == {"IO"}, (first, recorded)


def test_repro_1716_an_open_row_keeps_its_variable_only_where_every_row_does() -> None:
    """An open row at an accepting position: the effects every row names,
    the row variable kept only where every row ends in that same variable,
    the row closed otherwise; the join's own row never stands in."""
    from vera.checker.control import _accepted_row
    from vera.types import ConcreteEffectRow, EffectInstance, PureEffectRow

    io_i = EffectInstance("IO", ())
    st = EffectInstance("State", (INT,))
    io = ConcreteEffectRow(frozenset({io_i}))
    io_e = ConcreteEffectRow(frozenset({io_i}), "E")
    io_st_e = ConcreteEffectRow(frozenset({io_i, st}), "E")
    io_f = ConcreteEffectRow(frozenset({io_i}), "F")
    # the same variable on every row: kept, with the shared effects
    assert _accepted_row([io_e, io_st_e], io_st_e) == io_e
    assert _accepted_row([io_e, io_e], io_e) is io_e
    # one row closed: closed at the shared effects
    assert _accepted_row([PureEffectRow(), io_e], io_e) == PureEffectRow()
    assert _accepted_row([io_e, io], io_e) == io
    # two different variables: closed
    assert _accepted_row([io_e, io_f], io_e) == io
    # no rows: the join's own
    assert _accepted_row([], io_e) is io_e


_ROW_VARIABLE = """\
type PureCb = fn(Int -> Int) effects(pure);
type IoCb = fn(Int -> Int) effects(<IO>);
type TakesPure = fn(PureCb -> Int) effects(pure);
type CbE<E> = fn(Int -> Int) effects(<IO, E>);
type TakesE<E> = fn(CbE<E> -> Int) effects(<IO, E>);
type TakesIo = fn(IoCb -> Int) effects(<IO>);

private forall<E> fn pick(@Bool, @TakesPure, @TakesE<E>, @CbE<E> -> @Int)
  requires(true)
  ensures(true)
  effects(<IO>)
{{
  apply_fn(if @Bool.0 then {{ {first} }} else {{ {second} }}, @CbE<E>.0)
}}

public fn f(@Bool, @Int -> @Int)
  requires(true)
  ensures(true)
  effects(<IO>)
{{
  let @TakesPure = fn(@PureCb -> @Int) effects(pure) {{ apply_fn(@PureCb.0, 1) }};
  let @IoCb = fn(@Int -> @Int) effects(<IO>) {{
    IO.print("io ran\\n");
    @Int.0
  }};
  let @TakesIo = fn(@IoCb -> @Int) effects(<IO>) {{ apply_fn(@IoCb.0, 2) }};
  pick(@Bool.0, @TakesPure.0, @TakesIo.0, @IoCb.0)
}}
"""


@pytest.mark.parametrize("swap", [False, True], ids=["pure first", "open first"])
def test_repro_1716_a_pure_function_is_handed_no_open_row_callback(
        swap: bool) -> None:
    """A function taking a `pure` callback beside one taking an `<IO, E>`
    callback takes a `pure` one, so `apply_fn` of the join to the
    `<IO, E>` callback is refused (E202) in either order, as passing it to
    the pure function directly is.  At f71c401c and at 291d66cd both
    orders were accepted and the `effects(pure)` function printed
    `io ran`."""
    first, second = (("@TakesE<E>.0", "@TakesPure.0") if swap
                     else ("@TakesPure.0", "@TakesE<E>.0"))
    checked = pipeline.check(_ROW_VARIABLE.format(first=first, second=second),
                             file=FILE)
    assert [d.error_code for d in checked.errors] == ["E202"], [
        (d.error_code, d.description[:80]) for d in checked.errors]


_CALLBACK_RESULT = """\
type PosInt = {{ @Int | @Int.0 > 0 }};
type IntF = fn(Int -> Int) effects(pure);
type PosF = fn(Int -> PosInt) effects(pure);
type A = fn(IntF -> Int) effects(pure);
type B = fn(PosF -> Int) effects(pure);

private fn pick(@Bool, @A, @B, @Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{{
  apply_fn(if @Bool.0 then {{ {first} }} else {{ {second} }},
    fn(@Int -> @Int) effects(pure) {{ @Int.0 }})
}}

public fn f(@Bool, @Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{{
  let @A = fn(@IntF -> @Int) effects(pure) {{ 0 }};
  let @B = fn(@PosF -> @Int) effects(pure) {{
    let @PosInt = apply_fn(@PosF.0, 0 - 5);
    @PosInt.0
  }};
  pick(@Bool.0, @A.0, @B.0, @Int.0)
}}
"""


@pytest.mark.parametrize("swap", [False, True], ids=["intf first", "posf first"])
def test_repro_1716_a_refined_callback_result_is_recorded_at_the_arm(
        swap: bool) -> None:
    """`fn(IntF -> Int)` beside `fn(PosF -> Int)` is recorded
    `fn(PosF -> Int)` in either order: the join states what both accept.
    The run still hands the `PosF` arm an `Int`-returning closure and
    prints -5 into its `@PosInt`, because the formal `PosF` admits a
    `fn(Int -> Int)` argument (rule 9 with rule 7): issue #1819's
    relaxation, which the same call made directly also takes."""
    first, second = (("@B.0", "@A.0") if swap else ("@A.0", "@B.0"))
    source = _CALLBACK_RESULT.format(first=first, second=second)
    checked = pipeline.check(source, file=FILE)
    _learn_predicates(checked)
    types = checked.artifacts.node_semantic_types
    (pick,) = [getattr(tl, "decl", tl) for tl in checked.program.declarations
               if getattr(getattr(tl, "decl", tl), "name", "") == "pick"]
    (join,) = [n for n in fold.walk(pick.body) if isinstance(n, ast.IfExpr)]
    assert _show(types.get(join.node_id)) == "fn(fn(Int -> {Int|PosInt}) -> Int)"
    ran = pipeline.run(source, "f", [1 if swap else 0, 0], file=FILE)
    assert ran.trap is None and ran.value == -5, ran
