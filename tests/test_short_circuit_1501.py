"""`&&`, `||` and `==>` short-circuit, in compiled code and in the verifier (#1501).

Spec §4.6: the right operand is not evaluated if the left operand determines
the result.  Code generation lowered the three operators to an instruction
over two evaluated operands (`i32.and`, `i32.or`, and `i32.eqz` then `i32.or`
for `==>`), so a right operand that traps or performs an effect ran after the
left operand had decided the result: `@Int.0 != 0 && 10 / @Int.0 > 0` trapped
on `0`.  The verifier's walks matched that lowering and took no left operand
as a premise of its right, so the same guard was refused `E526`.

Both now follow §4.6.  The lowering is one function
(`OperatorsMixin._translate_binary`, which every position that compiles an
expression reaches through `translate_expr`), and the premise is held by
every walk that descends a binary expression's operands under path
conditions: the SMT translation (a call's precondition, a guarded binder's
fact, a callee's assumed `ensures`), the primitive-operation walk, the
binding-site narrowing walk and the `decreases` walk.  A left operand the
verifier cannot translate is stood for by a fresh Boolean, so a fact learned
in the right operand stays conditional on a value nothing states.

The class instrument crosses the position the operator stands in (a function
body, a `requires`, an `ensures` over `@result`, a refinement predicate
guarding a boundary, a `forall` predicate, a `where` helper's body, a
closure's body, an `assert`), the operator, and what the right operand holds
(a division, an index, a call whose `requires` the left establishes, an
`@Int` narrowed into a `@Nat` parameter, and an `IO.print`): 8 x 3 x 4 + 3 x
3 = 105 cells.  An effect stands only where one belongs by design (a body, a
`where` helper, a closure); a contract, a refinement predicate, a quantifier
predicate and an assertion are predicates, and §6.3.1 admits calls to `pure`
functions in them.

Every cell's expectation is §4.6's definition, stated as the `if` it means:
`a && b` is `if a then { b } else { false }`, `a || b` is `if a then { true }
else { b }`, and `a ==> b` is `if a then { b } else { true }`.  A cell builds
the operator's program and its `if` program, and holds the two to the same
obligation records and the same runs, beside literal premises that keep the
equality from passing two sides that are equally wrong: on the input where
the left operand decides, the right operand does not run (no trap of its own,
no output) and the result is §4.6's; on the input where it does not, the
right operand runs; and the right operand's obligation is `verified` wherever
the position's walk can state the left operand, which is every position bar
the fresh-scope ones (a closure's body and a quantifier's predicate are
walked with no slot bound, #779), where it is the runtime-checked Tier 3 the
same operation gets under an `if`.
"""

from __future__ import annotations

from dataclasses import dataclass

import pytest

from tests import pipeline

# A generated class instrument (tests/matrix_sample.py): a pull request runs a
# sample of its parametrised cells, and all of them when it changes this file
# or a module that decides its class: the one lowering of the three
# operators, and the translation and walks that take the left operand as a
# premise of the right.
pytestmark = pytest.mark.matrix(
    decides=["vera/wasm/operators.py", "vera/smt.py", "vera/verifier.py"],
)


# =====================================================================
# Helpers
# =====================================================================


def _verify(source: str) -> pipeline.Verified:
    """Verify *source*, which must type-check cleanly."""
    verified = pipeline.verify(source)
    errors = verified.checked.errors
    assert not errors, (
        "fixture must type-check cleanly, got: "
        f"{[(d.error_code, d.description[:80]) for d in errors]}"
    )
    return verified


def _at(source: str, needle: str, occurrence: int = 0) -> tuple[int, int]:
    """1-based (line, column) of the *occurrence*-th *needle* in *source*."""
    start = -1
    for _ in range(occurrence + 1):
        start = source.index(needle, start + 1)
    line = source.count("\n", 0, start) + 1
    column = start - (source.rfind("\n", 0, start) + 1) + 1
    return line, column


def _status(o: object) -> str:
    code = getattr(o, "error_code", None)
    status = getattr(o, "status")
    return f"{status}/{code}" if code else status


def _records_at(
    verified: pipeline.Verified, where: tuple[int, int],
) -> list[str]:
    """``kind:status[/code]`` of every obligation located at *where*."""
    return sorted(
        f"{o.kind}:{_status(o)}" for o in verified.obligations
        if (o.line, o.column) == where
    )


def _signature(verified: pipeline.Verified) -> list[str]:
    """Every obligation's ``kind:status[/code]``, and every diagnostic's
    code, located nowhere: what two spellings of one program share."""
    return sorted(
        [f"{o.kind}:{_status(o)}" for o in verified.obligations]
        + [f"{d.severity}:{d.error_code}" for d in verified.diagnostics]
    )


@dataclass(frozen=True)
class Outcome:
    """One call's outcome: a value, or a trap with its kind and message."""

    value: object | None
    trap_kind: str | None
    trap_message: str
    stdout: str


def _runs(source: str, fn: str, args: list[int]) -> list[Outcome]:
    """Compile *source* once and call *fn* with each of *args*."""
    compiled = pipeline.compile(source)
    assert compiled.ok, (
        "fixture must compile, got: "
        f"{[(d.error_code, d.description[:80]) for d in compiled.diagnostics]}"
    )
    outcomes = []
    for arg in args:
        ran = pipeline.run(compiled, fn, [arg])
        if ran.trap is not None:
            outcomes.append(Outcome(
                None, ran.trap.kind, str(ran.trap), ran.trap.stdout))
        else:
            outcomes.append(Outcome(ran.value, None, "", ran.stdout))
    return outcomes


def _shape(outcome: Outcome) -> tuple[object, ...]:
    """What two spellings of one call share: the value, the trap's kind and
    the function its message names, and what was printed."""
    named = outcome.trap_message.split("\n", 1)[0].split("(", 1)[0]
    return (outcome.value, outcome.trap_kind, named, outcome.stdout)


# =====================================================================
# The issue's programs, measured at fa958730
# =====================================================================


SC = """\
public fn safe_div(@Int -> @Bool)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Int.0 != 0 && 10 / @Int.0 > 0
}

public fn in_range(@Int -> @Bool)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Array<Int> = [10, 20, 30];
  @Int.0 >= 0 && @Int.0 < 3 && @Array<Int>.0[@Int.0] > 15
}

private fn say(@Unit -> @Bool)
  requires(true)
  ensures(true)
  effects(<IO>)
{
  IO.print("right operand evaluated\\n");
  true
}

public fn main(@Unit -> @Unit)
  requires(true)
  ensures(true)
  effects(<IO>)
{
  let @Bool = true || say(());
  let @Bool = false && say(());
  IO.print("done\\n")
}
"""


def test_repro_a_guarded_division_is_false_on_zero() -> None:
    (zero, five) = _runs(SC, "safe_div", [0, 5])
    assert zero == Outcome(0, None, "", "")
    assert five == Outcome(1, None, "", "")


def test_repro_a_guarded_index_is_false_out_of_range() -> None:
    (above, below, inside) = _runs(SC, "in_range", [5, -1, 1])
    assert above == Outcome(0, None, "", "")
    assert below == Outcome(0, None, "", "")
    assert inside == Outcome(1, None, "", "")


def test_repro_an_effect_in_a_decided_right_operand_does_not_run() -> None:
    compiled = pipeline.compile(SC)
    assert compiled.ok
    assert pipeline.run(compiled).stdout == "done\n"


def test_repro_the_guards_verify() -> None:
    v = _verify(SC)
    assert _records_at(v, _at(SC, "10 / @Int.0")) == ["div_zero:verified"]
    assert _records_at(v, _at(SC, "@Array<Int>.0[@Int.0]")) == [
        "index_bounds:verified"]
    assert v.ok, [(d.error_code, d.description[:80]) for d in v.errors]


#: Spec §5.2.2: several `requires` clauses mean one joined by `&&`.
NEED_POS = """\
private fn need_pos(@Int -> @Int)
  requires(@Int.0 > 0)
  ensures(@Int.result == @Int.0)
  effects(pure)
{
  @Int.0
}
"""

TWO_AND_ONE = NEED_POS + """
public fn two(@Int -> @Int)
  requires(@Int.0 >= 1)
  requires(need_pos(@Int.0) > 0)
  ensures(true)
  effects(pure)
{
  @Int.0
}

public fn one(@Int -> @Int)
  requires(@Int.0 >= 1 && need_pos(@Int.0) > 0)
  ensures(true)
  effects(pure)
{
  @Int.0
}
"""


def test_repro_one_requires_joined_by_and_verifies_as_two_do() -> None:
    v = _verify(TWO_AND_ONE)
    assert [o for o in v.obligations if o.kind == "call_pre"] == []
    assert v.ok, [(d.error_code, d.description[:80]) for d in v.errors]


def test_repro_one_requires_joined_by_and_fails_as_two_do() -> None:
    compiled = pipeline.compile(TWO_AND_ONE)
    assert compiled.ok
    for fn in ("two", "one"):
        ran = pipeline.run(compiled, fn, [0])
        assert ran.trap is not None and ran.trap.kind == "contract_violation"
        assert str(ran.trap).startswith(f"Precondition violation in {fn}("), (
            str(ran.trap))
        assert pipeline.run(compiled, fn, [3]).value == 3


# =====================================================================
# The class instrument
# =====================================================================


OPS = ("&&", "||", "==>")

#: The input on which every left operand below decides the result, and one on
#: which none does.
DECIDES, RUNS = 0, 2


@dataclass(frozen=True)
class Kind:
    """What a right operand holds, as a function of the slot it reads.

    *guard* maps an operator to the left operand that protects the right one:
    true where it may run for `&&` and `==>`, false for `||`.  *right* is true
    wherever it runs, so the value of the whole is the left operand's for
    `&&`, and `true` for `||` and `==>`.  *obligation* is the kind of the
    record the right operand's check is held to, located at *needle*,
    *offset* characters in; an effect is held to none.
    """

    name: str
    helpers: str
    guard: dict[str, str]
    right: str
    obligation: str | None
    needle: str
    offset: int = 0
    #: What the right operand prints when it runs.
    prints: str = ""


def _guards(when_runs: str, when_decides: str) -> dict[str, str]:
    return {"&&": when_runs, "==>": when_runs, "||": when_decides}


DIVISION = Kind(
    "division", "",
    _guards("{x} != 0", "{x} == 0"),
    "10 / {x} * 0 == 0", "div_zero", "10 / ")

INDEX = Kind(
    "index", "",
    _guards("{x} > 0 && {x} <= array_length(@Array<Int>.0)",
            "{x} <= 0 || {x} > array_length(@Array<Int>.0)"),
    "@Array<Int>.0[{x} - 1] * 0 == 0", "index_bounds", "@Array<Int>.0[")

CALL = Kind(
    "call", NEED_POS,
    _guards("{x} > 0", "{x} <= 0"),
    "need_pos({x}) > 0", "call_pre", "need_pos(")

NARROWING = Kind(
    "narrowing", """\
private fn nat_id(@Nat -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Nat.0
}
""",
    _guards("{x} > 0", "{x} <= 0"),
    "nat_id({x} - 1) >= 0", "nat_bind", "nat_id(", offset=len("nat_id("))

EFFECT = Kind(
    "effect", """\
private fn say(@Int -> @Bool)
  requires(true)
  ensures(true)
  effects(<IO>)
{
  IO.print("right\\n");
  true
}
""",
    _guards("{x} > 0", "{x} <= 0"),
    "say({x})", None, "say(", prints="right\n")

KINDS = (DIVISION, INDEX, CALL, NARROWING, EFFECT)

POSITIONS = (
    "body", "requires", "ensures", "refinement", "quantifier", "where",
    "closure", "assert",
)

#: The positions an effect belongs in by design.
EFFECT_POSITIONS = ("body", "where", "closure")

#: The positions walked with no slot bound (#779): neither operand's slot is
#: stated there, so an obligation that reads it is a runtime-checked Tier 3,
#: as it is under an `if`.
FRESH_SCOPE = ("closure", "quantifier")

#: A position whose value is a check: what the run shows when it is false.
OWN_FAILURE = {
    "requires": ("contract_violation", "Precondition violation in cell"),
    "ensures": ("contract_violation", "Postcondition violation in cell"),
    "refinement": ("contract_violation", "Refinement violation in cell"),
    "assert": ("assertion_failed", "Assertion failed"),
}


def _expression(kind: Kind, op: str, x: str, form: str) -> str:
    """The operator applied to *kind*'s operands over slot *x*, or (*form*
    ``"if"``) the `if` §4.6 defines it as."""
    left = kind.guard[op].replace("{x}", x)
    right = kind.right.replace("{x}", x)
    if form == "op":
        return f"({left}) {op} ({right})"
    if op == "&&":
        return f"if {left} then {{ {right} }} else {{ false }}"
    if op == "||":
        return f"if {left} then {{ true }} else {{ {right} }}"
    return f"if {left} then {{ {right} }} else {{ true }}"


def _fn(name: str, params: str, ret: str, body: str, *,
        requires: str = "true", ensures: str = "true",
        effects: str = "pure", visibility: str = "private ") -> str:
    return (f"{visibility}fn {name}({params} -> {ret})\n"
            f"  requires({requires})\n  ensures({ensures})\n"
            f"  effects({effects})\n{{\n  {body}\n}}\n")


def _program(position: str, kind: Kind, op: str, form: str) -> str:
    """The cell's program: a `cell` holding the operator at *position*, and
    a public `probe(@Int)` that calls it."""
    indexed = kind is INDEX
    params = "@Array<Int>, @Int" if indexed else "@Int"
    args = "[10, 20, 30], @Int.0" if indexed else "@Int.0"
    eff = "<IO>" if kind is EFFECT else "pure"
    e = _expression(kind, op, "@Int.0", form)
    probe = _fn("probe", "@Int", "@Bool", f"cell({args})",
                effects=eff, visibility="public ")
    if position == "body":
        cell = _fn("cell", params, "@Bool", e, effects=eff)
    elif position == "requires":
        cell = _fn("cell", params, "@Bool", "true", requires=e)
    elif position == "ensures":
        result = _expression(kind, op, "@Int.result", form)
        cell = _fn("cell", params, "@Int", "@Int.0", ensures=result)
        probe = _fn("probe", "@Int", "@Int", f"cell({args})",
                    visibility="public ")
    elif position == "refinement":
        if indexed:
            # The binder is the array, so its length is what the left
            # operand establishes: the decider is a one-element array.
            whole = Kind(
                "index", "",
                _guards("array_length(@Array<Int>.0) > 1",
                        "array_length(@Array<Int>.0) <= 1"),
                "@Array<Int>.0[1] * 0 == 0", "index_bounds",
                "@Array<Int>.0[")
            pred = _expression(whole, op, "", form)
            cell = (f"type Probe = {{ @Array<Int> | {pred} }};\n\n"
                    + _fn("cell", "@Probe", "@Int", "0"))
            arg = "if @Int.0 == 0 then { [10] } else { [10, 20, 30] }"
        else:
            cell = (f"type Probe = {{ @Int | {e} }};\n\n"
                    + _fn("cell", "@Probe", "@Int", "0"))
            arg = "@Int.0"
        probe = _fn("probe", "@Int", "@Int", f"cell({arg})",
                    visibility="public ")
    elif position == "quantifier":
        cell = _fn(
            "cell", params, "@Bool",
            f"forall(@Int, 3, fn(@Int -> @Bool) effects(pure) {{ {e} }})")
    elif position == "where":
        probe = (_fn("probe", "@Int", "@Bool", f"cell({args})",
                     effects=eff, visibility="public ")
                 + "where {\n"
                 + _fn("cell", params, "@Bool", e, effects=eff,
                       visibility="")
                 + "}\n")
        cell = ""
    elif position == "closure":
        cell = _fn(
            "cell", params, "@Bool",
            f"apply_fn(fn(@Int -> @Bool) effects({eff}) {{ {e} }}, @Int.0)",
            effects=eff)
    else:
        assert position == "assert"
        cell = _fn("cell", params, "@Bool", f"assert({e});\n  true")
    return "\n".join(part for part in (kind.helpers, cell, probe) if part)


def _observed(position: str, outcome: Outcome) -> bool:
    """The value the position's expression took on a run that ended as
    *outcome*: a check's own failure is a false one, and any other trap is
    the right operand's."""
    if outcome.trap_kind is None:
        return position in OWN_FAILURE or bool(outcome.value)
    own = OWN_FAILURE.get(position)
    assert own is not None and outcome.trap_kind == own[0] and (
        own[1] in outcome.trap_message), (
        f"the right operand ran: {outcome.trap_kind}: {outcome.trap_message}")
    return False


def _expected(position: str, op: str, arg: int) -> bool:
    """§4.6's value: the left operand's for `&&`, `true` for `||` and `==>`.
    A quantifier's domain holds the deciding index whatever the input."""
    if arg == DECIDES or position == "quantifier":
        return op != "&&"
    return True


def _right_operation(source: str, kind: Kind) -> list[tuple[int, int]]:
    """Where the right operand's operation stands in *source*: every
    occurrence of its needle after the helpers the program starts with."""
    first = kind.helpers.count(kind.needle)
    sites = []
    for n in range(first, source.count(kind.needle)):
        line, column = _at(source, kind.needle, n)
        sites.append((line, column + kind.offset))
    assert sites, (kind.name, source)
    return sites


CELLS = [
    pytest.param(position, kind, op, id=f"{position}-{kind.name}-{op}")
    for position in POSITIONS
    for kind in KINDS
    if kind is not EFFECT or position in EFFECT_POSITIONS
    for op in OPS
]


@pytest.mark.parametrize(("position", "kind", "op"), CELLS)
def test_the_operator_means_its_if(position: str, kind: Kind, op: str) -> None:
    source = _program(position, kind, op, "op")
    defined = _program(position, kind, op, "if")

    # The runs: the right operand does not run where the left decides, the
    # value is §4.6's, and the `if` runs the same.
    ran = _runs(source, "probe", [DECIDES, RUNS])
    for arg, outcome in zip((DECIDES, RUNS), ran):
        assert _observed(position, outcome) is _expected(position, op, arg), (
            arg, outcome)
    assert ran[0].stdout == "", ran[0]
    assert ran[1].stdout == kind.prints, ran[1]
    assert [_shape(o) for o in ran] == [
        _shape(o) for o in _runs(defined, "probe", [DECIDES, RUNS])]

    # The verdicts: the right operand's obligation is discharged under the
    # left one, as under the `if`, and nothing else in the program moves.
    v = _verify(source)
    w = _verify(defined)
    assert _signature(v) == _signature(w)
    if kind.obligation is None:
        return
    mine = _right_records(v, source, kind)
    assert mine == _right_records(w, defined, kind)
    if position in FRESH_SCOPE:
        # No slot is bound there, so neither operand is stated: the check is
        # the runtime-checked Tier 3 it is under the `if`.
        assert mine and all(
            r.split(":", 1)[1].startswith("tier3") for r in mine), mine
    elif kind is CALL:
        # A discharged precondition leaves no record; a refused one is E501.
        assert mine == [], mine
    else:
        assert mine and set(mine) == {f"{kind.obligation}:verified"}, mine


def _right_records(
    verified: pipeline.Verified, source: str, kind: Kind,
) -> list[str]:
    """The right operand's records of *kind*'s obligation in *source*."""
    return [r for site in _right_operation(source, kind)
            for r in _records_at(verified, site)
            if r.startswith(f"{kind.obligation}:")]


# =====================================================================
# Negative space: the premise holds for the right operand and nowhere else
# =====================================================================


def _after(op: str, shape: str) -> str:
    guard = DIVISION.guard[op].replace("{x}", "@Int.0")
    right = DIVISION.right.replace("{x}", "@Int.0")
    if shape == "let":
        body = f"let @Bool = ({guard}) {op} ({right});\n  10 / @Int.0"
    else:
        body = f"(({guard}) {op} ({right})) == (10 / @Int.0 == 0)"
    ret = "@Int" if shape == "let" else "@Bool"
    return _fn("probe", "@Int", ret, body, visibility="public ")


@pytest.mark.parametrize("op", OPS)
@pytest.mark.parametrize("shape", ["let", "operand"])
def test_an_operation_after_the_operator_is_not_under_its_premise(
        shape: str, op: str) -> None:
    """The right operand's division is discharged and the one after the
    operator is not: the premise is popped when the right operand ends."""
    source = _after(op, shape)
    v = _verify(source)
    inside, after = _at(source, "10 / "), _at(source, "10 / ", 1)
    assert "div_zero:verified" in _records_at(v, inside)
    assert "div_zero:violated/E526" in _records_at(v, after)


@pytest.mark.parametrize("op", OPS)
def test_an_operation_in_the_left_operand_is_under_no_premise(op: str) -> None:
    source = _fn("probe", "@Int", "@Bool",
                 f"(10 / @Int.0 * 0 == 0) {op} (@Int.0 != 0)",
                 visibility="public ")
    v = _verify(source)
    assert "div_zero:violated/E526" in _records_at(v, _at(source, "10 / "))
    (zero,) = _runs(source, "probe", [0])
    assert zero.trap_kind == "divide_by_zero"


FALSE_IMPLIES = _fn("probe", "@Int", "@Bool", "false ==> (1 / 0 == 0)",
                    visibility="public ")


def test_repro_false_implies_a_trap_is_true_and_clean() -> None:
    """Kills `==>` lowered as `&&`, which returns false here."""
    (zero,) = _runs(FALSE_IMPLIES, "probe", [0])
    assert zero == Outcome(1, None, "", "")
    v = _verify(FALSE_IMPLIES)
    assert _records_at(v, _at(FALSE_IMPLIES, "1 / 0")) == [
        "div_zero:verified"]
    assert v.ok, [(d.error_code, d.description[:80]) for d in v.errors]


OR_GUARD = _fn("probe", "@Int", "@Bool", "@Int.0 == 0 || 10 / @Int.0 > 0",
               visibility="public ")


def test_repro_an_or_guards_its_right_operand_with_its_negation() -> None:
    """Kills `||`'s premise pushed as the left operand rather than its
    negation, under which the division is refuted."""
    v = _verify(OR_GUARD)
    assert "div_zero:verified" in _records_at(v, _at(OR_GUARD, "10 / "))
    assert v.ok, [(d.error_code, d.description[:80]) for d in v.errors]


NARROWING_GUARD = NARROWING.helpers + "\n" + _fn(
    "probe", "@Int", "@Bool", "@Int.0 > 0 && nat_id(@Int.0 - 1) >= 0",
    visibility="public ")


def test_repro_a_narrowing_in_a_right_operand_is_under_the_premise() -> None:
    """Kills the binding-site narrowing walk taking no premise."""
    v = _verify(NARROWING_GUARD)
    # The subtraction's overflow is Tier 3 under an `if` with the same
    # condition too: only the narrowing is the premise's to discharge.
    where = _at(NARROWING_GUARD, "@Int.0 - 1")
    assert _records_at(v, where) == ["int_overflow:tier3",
                                     "nat_bind:verified"]
    assert v.ok, [(d.error_code, d.description[:80]) for d in v.errors]
    (zero,) = _runs(NARROWING_GUARD, "probe", [0])
    assert zero == Outcome(0, None, "", "")


#: The narrowing walk holds an `assert`'s fact in its own assumptions, not on
#: the path, so its translation of the left operand checks `need_pos`'s
#: precondition without the fact: kept, that outcome refuses a call every
#: other translation discharges.
ASSERTED_LEFT = NEED_POS + "\n" + NARROWING.helpers + "\n" + _fn(
    "probe", "@Int", "@Bool",
    "assert(@Int.0 > 0);\n  need_pos(@Int.0) > 0 && nat_id(@Int.0 - 1) >= 0",
    visibility="public ")


def test_a_premise_is_stated_without_obligating_its_calls_again() -> None:
    """Kills the premise's translation keeping its call-site outcomes."""
    v = _verify(ASSERTED_LEFT)
    assert [o for o in v.obligations if o.kind == "call_pre"] == []
    assert _records_at(v, _at(ASSERTED_LEFT, "@Int.0 - 1")) == [
        "int_overflow:tier3", "nat_bind:verified"]
    assert v.ok, [(d.error_code, d.description[:80]) for d in v.errors]


#: The recursive call is evaluated only where `@Nat.0` is below the length,
#: so the measure decreases there and the call's precondition holds.
ALL_POS = """\
public fn all_pos(@Array<Int>, @Nat -> @Bool)
  requires(@Nat.0 <= array_length(@Array<Int>.0))
  ensures(true)
  decreases(array_length(@Array<Int>.0) - @Nat.0)
  effects(pure)
{
  @Nat.0 >= array_length(@Array<Int>.0) || all_pos(@Array<Int>.0, @Nat.0 + 1)
}

public fn main(@Unit -> @Bool)
  requires(true)
  ensures(true)
  effects(pure)
{
  all_pos([1, 2, 3], 0)
}
"""


def test_repro_a_recursive_call_in_a_right_operand_terminates() -> None:
    """Kills the `decreases` walk taking no premise."""
    v = _verify(ALL_POS)
    assert _records_at(v, _at(ALL_POS, "decreases(")) == [
        "decreases:verified"]
    assert [o for o in v.obligations if o.kind == "call_pre"] == []
    compiled = pipeline.compile(ALL_POS)
    assert compiled.ok
    assert pipeline.run(compiled, "main").value == 1


# =====================================================================
# A left operand the verifier cannot translate
# =====================================================================


#: `apply_fn` does not translate.  The check in `check_pos` runs only where
#: the closure returns true, which it never does, so `f(0)` returns 0 and
#: fails its postcondition: the assumed `ensures(@Int.0 > 0)` of a call that
#: does not happen must not prove it.
UNSTATED_LEFT = """\
private fn check_pos(@Int -> @Bool)
  requires(true)
  ensures(@Int.0 > 0)
  effects(pure)
{
  assert(@Int.0 > 0);
  true
}

public fn f(@Int -> @Int)
  requires(true)
  ensures(@Int.result > 0)
  effects(pure)
{
  let @Bool = apply_fn(fn(@Int -> @Bool) effects(pure) { false }, @Int.0) && check_pos(@Int.0);
  @Int.0
}
"""


def test_repro_a_fact_from_a_right_operand_needs_its_left_operand() -> None:
    """Kills an untranslatable left operand pushing no premise, under which
    `check_pos`'s `ensures` is assumed on every run and proves `f`'s."""
    v = _verify(UNSTATED_LEFT)
    (ensures,) = [o for o in v.obligations
                  if o.kind == "ensures" and o.line == _at(
                      UNSTATED_LEFT, "ensures(@Int.result")[0]]
    assert ensures.status != "verified", ensures
    compiled = pipeline.compile(UNSTATED_LEFT)
    assert compiled.ok
    ran = pipeline.run(compiled, "f", [0])
    assert ran.trap is not None and str(ran.trap).startswith(
        "Postcondition violation in f("), ran.trap


@pytest.mark.parametrize("op", OPS)
def test_an_unstated_left_operand_protects_nothing(op: str) -> None:
    """The nearest neighbour of the fresh premise: the right operand's
    division is refused as it is under an `if` whose condition does not
    translate, so the stand-in states nothing about the divisor."""
    left = "apply_fn(fn(@Int -> @Bool) effects(pure) { @Int.0 != 0 }, @Int.0)"
    if op == "||":
        left = f"!{left}"
    body = f"{left} {op} (10 / @Int.0 * 0 == 0)"
    source = _fn("probe", "@Int", "@Bool", body, visibility="public ")
    branch = _expression(
        Kind("unstated", "", {o: left for o in OPS},
             "10 / @Int.0 * 0 == 0", "div_zero", "10 / "), op, "@Int.0",
        "if")
    defined = _fn("probe", "@Int", "@Bool", branch, visibility="public ")
    v, w = _verify(source), _verify(defined)
    assert _records_at(v, _at(source, "10 / ")) == _records_at(
        w, _at(defined, "10 / "))
    assert "div_zero:violated/E526" in _records_at(v, _at(source, "10 / "))
    assert _signature(v) == _signature(w)
