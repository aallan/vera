"""A join of an `@Int` branch with a `@Nat` branch is an `@Int`, so binding it into a `@Nat` position is obligated (#1756).

The checker joined an `if`'s or a `match`'s branch types through the relaxed
`Int <: Nat` subtype rule, which hands the first type to the second: an `if`
whose then-branch is an `@Int` (a negated literal, literal arithmetic, an
`@Int` slot) and whose else-branch is a `@Nat` was typed `@Nat`, and so was a
`match` whose later arm is the `@Int`.  The verifier reads that type, saw no
narrowing where the join is bound into a `@Nat` `let`, argument or field, and
recorded no `nat_bind` obligation, while code generation's static rule read
the `@Int` branch and planted the guard: `vera verify` passed
`let @Nat = if @Bool.0 then { -1 } else { @Nat.0 };`, and the run trapped.

The matrix holds the rule over the class: each value form (a literal, a
negated literal, literal arithmetic, a negated `@Nat`, an `@Int` slot and a
sum over it) joined with a `@Nat` in each join (`if`, `match`, a nested `if`),
in each order, at each `@Nat` position (`let`, argument, return, constructor
field).  A cell verifies with the verdict the value's sign decides (E503 where
the form can be negative), records the narrowing it checks, and the
reconciliation reports no guard without a record.  The negative space joins
into `@Int` positions, and joins of two `@Nat` branches, which the base
already accepts with no narrowing, and still does.
"""

from __future__ import annotations

from dataclasses import dataclass

import pytest

from tests import pipeline
from vera.reconcile import join

pytestmark = pytest.mark.matrix(decides=["vera/checker/control.py"])

LABEL = "join_1756.vera"

#: (form, whether it can be negative): each written where a branch of the
#: join stands, in a function holding `@Bool`, `@Int` and `@Nat` parameters.
FORMS: dict[str, bool] = {
    "-1": True,
    "-(1)": True,
    "-1 * -3": False,
    "1 - 2": True,
    "0 - 1": True,
    "-0": False,
    "3": False,
    "-@Nat.0": True,
    "@Int.0": True,
    "@Int.0 + 1": True,
}

ORDERS = ("form first", "form last", "both the form")
JOINS = ("if", "match", "nested if")
POSITIONS = ("let", "argument", "return", "field")

#: The `@Nat` side of a join: a `@Nat` slot, or a `@Pos` parameter, `Pos`
#: a refinement of `@Nat`, whose join with an `@Int` the relaxed subtype
#: rule types `Pos`.  Beside a refinement the forms are those the join
#: demotes to an `@Int`: `3` is a non-negative constant, its join keeps
#: `Pos`, and code generation's static rule, which reads no refinement,
#: guards that binding with no record, which is #1695's class.
REFINED = "@Pos.0"
REFINED_FORMS = tuple(form for form in FORMS if form != "3")


def _branches(form: str, order: str, nat: str = "@Nat.0") -> tuple[str, str]:
    if order == "form first":
        return form, nat
    if order == "form last":
        return nat, form
    return form, form


def _join(kind: str, first: str, second: str, ind: str) -> str:
    """The join, laid out as `vera fmt` writes it, starting at *ind*."""
    inner = ind + "  "
    if kind == "if":
        return (f"if @Bool.0 then {{\n{inner}{first}\n{ind}}} else {{\n"
                f"{inner}{second}\n{ind}}}")
    if kind == "match":
        return (f"match @Bool.0 {{\n{inner}true -> {first},\n"
                f"{inner}false -> {second}\n{ind}}}")
    deeper = inner + "  "
    return (f"if @Bool.0 then {{\n{inner}if @Bool.0 then {{\n{deeper}{first}\n"
            f"{inner}}} else {{\n{deeper}{second}\n{inner}}}\n{ind}}} else {{\n"
            f"{inner}{second}\n{ind}}}")


_HEAD = """\
private data Box {
  Wrap(Nat),
  Plain(Int)
}

private fn keep(@Nat -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Nat.0
}

private fn keep_int(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Int.0
}

"""


_POS = "type Pos = { @Nat | @Nat.0 > 0 };\n\n"


def _program(position: str, joined: str, ty: str = "Nat") -> str:
    """A function placing *joined* (written from column three) at
    *position*, typed *ty*; a join that reads `@Pos.0` has a `@Pos`
    parameter, and the program declares `Pos`."""
    refined = REFINED in joined
    ret = "@Nat" if position == "return" and ty == "Nat" else "@Int"
    if position == "let":
        body = f"  let @{ty} = {joined};\n  0"
    elif position == "argument":
        callee = "keep" if ty == "Nat" else "keep_int"
        body = f"  {callee}({joined})"
    elif position == "return":
        body = f"  {joined}"
    else:
        ctor = "Wrap" if ty == "Nat" else "Plain"
        body = f"  let @Box = {ctor}({joined});\n  0"
    params = "@Bool, @Int, @Nat, @Pos" if refined else "@Bool, @Int, @Nat"
    return (_POS if refined else "") + _HEAD + (
        f"public fn f({params} -> {ret})\n"
        f"  requires(true)\n  ensures(true)\n  effects(pure)\n{{\n{body}\n}}\n")


@dataclass(frozen=True)
class Outcome:
    errors: tuple[str, ...]
    nat_binds: tuple[str, ...]
    unrecorded: tuple[str, ...]


def _outcome(source: str) -> Outcome:
    """The verdict, the narrowings recorded in `f`, and the guards with no
    record.  A `@Pos` parameter's entry guard is one of #1695's, a guard on
    a value already of the refined type, and is left out."""
    verified = pipeline.verify(source, file=LABEL)
    assert verified.checked.ok, "\n".join(
        d.format() for d in verified.checked.errors)
    compiled = pipeline.compile(source, file=LABEL)
    assert compiled.ok, compiled.diagnostics
    checked = verified.checked
    joined = join(verified.result, compiled.result, program=checked.program,
                  file=checked.file, resolved_modules=checked.resolved or ())
    return Outcome(
        errors=tuple(d.error_code or "" for d in verified.errors),
        nat_binds=tuple(o.status for o in verified.obligations
                        if o.kind == "nat_bind" and o.fn_name == "f"),
        unrecorded=tuple(
            f"{m.obligation} at {m.line}:{m.column}"
            for m in joined.mismatches if m.kind == "guarded_unrecorded"
            and not (REFINED in source and m.obligation == "refine_bind")),
    )


def _cells() -> list[object]:
    cells = [
        pytest.param(form, kind, order, position, "@Nat.0",
                     id=f"{form} {order} {kind} {position}")
        for form in FORMS for kind in JOINS for order in ORDERS
        for position in POSITIONS
    ]
    cells += [
        pytest.param(form, kind, order, position, REFINED,
                     id=f"{form} {order} {kind} {position} beside a refined Nat")
        for form in REFINED_FORMS for kind in JOINS for order in ORDERS[:2]
        for position in POSITIONS
    ]
    return cells


@pytest.mark.parametrize("form, kind, order, position, nat", _cells())
def test_a_join_into_a_nat_position_is_obligated(
    form: str, kind: str, order: str, position: str, nat: str,
) -> None:
    """The verdict is the value's sign: E503 where the form can be negative,
    clean where it cannot; the narrowing is recorded wherever the module
    guards it, so the join reports no guard without a record.  The `@Nat`
    side is a `@Nat` slot or a slot of a refinement of `@Nat`."""
    first, second = _branches(form, order, nat)
    outcome = _outcome(_program(position, _join(kind, first, second, "  ")))
    negative = FORMS[form]
    assert ("E503" in outcome.errors) == negative, outcome
    assert set(outcome.errors) <= {"E503"}, outcome
    assert not outcome.unrecorded, outcome
    if negative:
        assert "violated" in outcome.nat_binds, outcome


def _negative_space() -> list[object]:
    cells = [
        pytest.param(form, kind, order, position, "Int", "@Nat.0",
                     id=f"{form} {order} {kind} {position} into Int")
        for form in FORMS for kind in JOINS for order in ORDERS
        for position in POSITIONS
    ]
    cells += [
        pytest.param(form, kind, order, position, "Int", REFINED,
                     id=f"{form} {order} {kind} {position} into Int beside a refined Nat")
        for form in FORMS for kind in JOINS for order in ORDERS[:2]
        for position in POSITIONS
    ]
    cells += [
        pytest.param("@Nat.0", kind, "both the form", position, "Nat", "@Nat.0",
                     id=f"two Nat branches {kind} {position}")
        for kind in JOINS for position in POSITIONS
    ]
    return cells


@pytest.mark.parametrize("form, kind, order, position, ty, nat", _negative_space())
def test_a_join_the_base_accepts_is_accepted(
    form: str, kind: str, order: str, position: str, ty: str, nat: str,
) -> None:
    """The neighbours the base accepts with no narrowing: the same joins
    into an `@Int` position, beside a `@Nat` slot or a refinement of one,
    and joins of two `@Nat` branches.  Each is accepted, records no
    narrowing and leaves no guard without a record, at the base and
    here."""
    first, second = _branches(form, order, nat)
    joined = _join(kind, first, second, "  ")
    outcome = _outcome(_program(position, joined, ty))
    assert outcome == Outcome((), (), ()), outcome


_REPRO = """\
public fn sentinel(@Bool, @Nat -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Nat = if @Bool.0 then {
    -1
  } else {
    @Nat.0
  };
  0
}

public fn through_a_call(@Bool, @Nat -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  keep(if @Bool.0 then {
    -1
  } else {
    @Nat.0
  })
}

private fn keep(@Nat -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Nat.0
}

public fn tripled(@Bool, @Nat -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Nat = if @Bool.0 then {
    -1 * -3
  } else {
    @Nat.0
  };
  0
}

public fn swapped(@Bool, @Nat -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Nat = if @Bool.0 then {
    @Nat.0
  } else {
    -1
  };
  0
}
"""


def test_the_reported_program_repro() -> None:
    """#1756's program: `sentinel` and `through_a_call` are refused as
    `swapped` is, and `tripled`'s narrowing is recorded and proved, so the
    reconciliation reports no guard without a record."""
    verified = pipeline.verify(_REPRO, file=LABEL)
    refused = sorted({
        o.fn_name for o in verified.obligations
        if o.kind == "nat_bind" and o.status == "violated"})
    assert refused == ["sentinel", "swapped", "through_a_call"], refused
    assert [d.error_code for d in verified.errors] == ["E503"] * 3
    assert [o.status for o in verified.obligations
            if o.kind == "nat_bind" and o.fn_name == "tripled"] == ["verified"]
    compiled = pipeline.compile(_REPRO, file=LABEL)
    checked = verified.checked
    joined = join(verified.result, compiled.result, program=checked.program,
                  file=checked.file, resolved_modules=checked.resolved or ())
    assert [m for m in joined.mismatches
            if m.kind == "guarded_unrecorded"] == [], joined.mismatches
    ran = pipeline.run(_REPRO, fn="tripled", args=[1, 3])
    assert ran.ok and ran.value == 0


def test_e503s_fix_clears_the_reported_program_repro() -> None:
    """E503's fix, applied as it reads: a precondition ruling out the input
    its counterexample names (`@Bool.0 = true`), and `sentinel` verifies."""
    sentinel = _REPRO.split("\n\npublic fn through_a_call")[0] + "\n"
    verified = pipeline.verify(sentinel, file=LABEL)
    [error] = verified.errors
    assert error.error_code == "E503", error.format()
    assert "Add a precondition ruling out the bad inputs" in (error.fix or "")
    assert "@Bool.0 = True" in error.description, error.description
    fixed = sentinel.replace("  requires(true)\n", "  requires(!@Bool.0)\n", 1)
    after = pipeline.verify(fixed, file=LABEL)
    assert after.ok, [d.format() for d in after.errors]
    assert [o.status for o in after.obligations if o.kind == "nat_bind"] == [
        "verified"]
