"""A contract predicate performs no effect, whatever its function's row names (#1708).

Spec §7.9.1 holds every contract predicate to purity: a `requires`,
`ensures` or `decreases` clause, an `assert` or an `assume`, and a
refinement type's predicate are evaluated by the compiled checks and
modelled by the verifier, where the program never asked for an effect.
Since #1702 an operation is held to the row in force, and a contract was
checked under its function's row, so an operation of an effect that row
names was permitted in it, and so was a call to a function whose row names
one, or an `apply_fn` of a closure that performs one.  A refinement
predicate checked where no row is in force was judged by nothing.
`requires(Random.random_int(1, 1) > 0)` under `effects(<Random>)` checked,
verified, and ran the operation in the compiled precondition.

Now each predicate is checked as pure, with one judgement (E187) at each
place in it that performs an effect: an operation, a call to a function
whose row names an effect, an `apply_fn` of a function value whose row names
one, and an anonymous function written in it that performs one.  The last
holds applied or not, since a row variable can carry the closure to an
application nothing refuses (#294), as a `pure` function is held to its
closures (#1702).  A handler written inside the predicate handles its effect
there, so an operation of that effect under it is pure.  An operation of a
user-declared effect is E340's (rule 6, #1699), as everywhere.  The
diagnostic names the predicate and what performs the effect, and its fix
moves the operation into the body: bind its value with `let` and check it
with `assert`.

The instrument crosses each predicate kind (the three clauses, `assert`,
`assume`, and a refinement predicate on an alias, a data field, a parameter
and a result) with each built-in effect's operation (qualified, and `get`
bare), a user-declared effect's operation, a call to a function whose row
names `IO`, and an `apply_fn` of a closure that performs `IO`.  The negative
space is each refused shape's nearest accepted neighbour: the predicate
pure, and the operation in the body, its value bound with `let` and checked
with `assert`.  Each neighbour has the verdict and obligation statuses it had
at the base.  So does an operation under a handler written inside the
predicate, `old` and `new` in an `ensures`, and a pure call, closure and
quantifier in a contract.
"""

from __future__ import annotations

import pytest

from tests import pipeline

# A class instrument (tests/matrix_sample.py): a pull request runs a sample
# of its parametrised cells, and all of them when it changes this file or a
# module that decides its class: the predicates' checking in the core, the
# operations' and calls' judgements in the call checker, and the closures',
# `assert`'s and `assume`'s in the expression checker.
pytestmark = pytest.mark.matrix(
    decides=[
        "vera/checker/core.py",
        "vera/checker/calls.py",
        "vera/checker/expressions.py",
    ],
)


# =====================================================================
# The programs
# =====================================================================

_COUNTER = "effect Counter {\n  op tick(Unit -> Int);\n}\n\n"
_G_IO = ("private fn g(@Int -> @Int)\n  requires(true)\n  ensures(true)\n"
         '  effects(<IO>)\n{\n  IO.print("g");\n  @Int.0\n}\n\n')

#: form -> (the effects clause that names its effect, a Bool expression
#: that performs it, the declarations it needs, and the text the refusal is
#: placed at).
_FORMS: dict[str, tuple[str, str, str, str]] = {
    "IO.time": ("<IO>", "IO.time(()) >= 0", "", "IO.time"),
    "Random.random_int": (
        "<Random>", "Random.random_int(1, 1) > 0", "", "Random.random_int"),
    "Random.random_bool": (
        "<Random>", "Random.random_bool(())", "", "Random.random_bool"),
    "Http.get": (
        "<Http>",
        'match Http.get("u") { Ok(@String) -> true, Err(@String) -> true }',
        "", "Http.get"),
    "DB.execute": (
        "<DB>",
        'match DB.execute("q", []) { Ok(@Int) -> true, Err(@String) -> true }',
        "", "DB.execute"),
    "Inference.complete": (
        "<Inference>",
        'match Inference.complete("p") { Ok(@String) -> true, '
        "Err(@String) -> true }",
        "", "Inference.complete"),
    "State.get": ("<State<Int>>", "State.get(()) >= 0", "", "State.get"),
    "get": ("<State<Int>>", "get(()) >= 0", "", "get(())"),
    "Exn.throw": (
        "<Exn<String>>", 'if true then { true } else { Exn.throw("x") }', "",
        "Exn.throw"),
    "Counter.tick": (
        "<Counter>", "Counter.tick(()) >= 0", _COUNTER, "Counter.tick"),
    "a call": ("<IO>", "g(1) > 0", _G_IO, "g(1)"),
    "apply_fn of a closure": (
        "<IO>",
        "apply_fn(fn(@Int -> @Bool) effects(<IO>) { IO.time(()) >= @Int.0 }, 0)",
        "", "fn(@Int -> @Bool)"),
}

#: predicate kind -> the program, PRED its predicate and EFF the function's
#: effects clause.
_KINDS: dict[str, str] = {
    "requires": ("public fn f(@Int -> @Int)\n  requires(PRED)\n  ensures(true)\n"
                 "  effects(EFF)\n{\n  @Int.0\n}\n"),
    "ensures": ("public fn f(@Int -> @Int)\n  requires(true)\n  ensures(PRED)\n"
                "  effects(EFF)\n{\n  @Int.0\n}\n"),
    "decreases": (
        "public fn f(@Nat -> @Nat)\n  requires(true)\n  ensures(true)\n"
        "  decreases(if PRED then { @Nat.0 } else { @Nat.0 })\n"
        "  effects(EFF)\n{\n"
        "  if @Nat.0 == 0 then { 0 } else { f(@Nat.0 - 1) }\n}\n"),
    "assert": ("public fn f(@Int -> @Int)\n  requires(true)\n  ensures(true)\n"
               "  effects(EFF)\n{\n  assert(PRED);\n  @Int.0\n}\n"),
    "assume": ("public fn f(@Int -> @Int)\n  requires(true)\n  ensures(true)\n"
               "  effects(EFF)\n{\n  assume(PRED);\n  @Int.0\n}\n"),
    "alias": ("type Odd = { @Int | PRED };\n\n"
              "public fn f(@Odd -> @Int)\n  requires(true)\n  ensures(true)\n"
              "  effects(EFF)\n{\n  @Odd.0\n}\n"),
    "field": ("private data Box {\n  Box({ @Int | PRED })\n}\n\n"
              "public fn f(@Box -> @Int)\n  requires(true)\n  ensures(true)\n"
              "  effects(EFF)\n{\n  match @Box.0 { Box(@Int) -> @Int.0 }\n}\n"),
    "parameter": ("public fn f(@{ @Int | PRED } -> @Int)\n  requires(true)\n"
                  "  ensures(true)\n  effects(EFF)\n{\n  0\n}\n"),
    "result": ("public fn f(@Int -> @{ @Int | PRED })\n  requires(true)\n"
               "  ensures(true)\n  effects(EFF)\n{\n  0\n}\n"),
}

#: Each kind made pure: its predicate, and the body that then performs the
#: operation, BODY the original body's last expression.
_PURE_PREDICATE: dict[str, str] = {
    "requires": "true", "ensures": "true", "decreases": "@Nat.0",
    "assert": "@Bool.0", "assume": "@Bool.0",
    "alias": "true", "field": "true", "parameter": "true", "result": "true",
}


def _program(kind: str, form: str) -> str:
    eff, pred, decls, _ = _FORMS[form]
    return decls + _KINDS[kind].replace("PRED", pred).replace("EFF", eff)


def _neighbour(kind: str, form: str) -> str:
    """The nearest accepted neighbour of the cell: the predicate pure, and
    the operation performed in the body, its value bound with `let` and
    checked with `assert` (an `assume`'s by `assume`)."""
    eff, pred, decls, _ = _FORMS[form]
    source = decls + _KINDS[kind].replace("EFF", eff)
    check = "assume" if kind == "assume" else "assert"
    bound = f"let @Bool = {pred};\n  {check}(@Bool.0);\n  "
    if kind == "decreases":
        source = source.replace(
            "decreases(if PRED then { @Nat.0 } else { @Nat.0 })",
            "decreases(@Nat.0)")
        return source.replace("{\n  if @Nat.0", "{\n  " + bound + "if @Nat.0")
    if kind in ("assert", "assume"):
        return source.replace(f"{kind}(PRED);\n  ", bound)
    source = source.replace("PRED", _PURE_PREDICATE[kind])
    body_start = source.rindex("{\n  ") + len("{\n  ")
    return source[:body_start] + bound + source[body_start:]


_PERFORMING = [f for f in _FORMS if f != "Counter.tick"]


# =====================================================================
# Helpers
# =====================================================================


def _locate(source: str, marker: str) -> tuple[int, int]:
    """1-based (line, column) of *marker*'s first match."""
    idx = source.index(marker)
    line = source.count("\n", 0, idx) + 1
    return line, idx - (source.rfind("\n", 0, idx) + 1) + 1


def _placed(checked: pipeline.Checked) -> list[tuple[str, int, int]]:
    return [(d.error_code, d.location.line, d.location.column)
            for d in checked.errors]


def _statuses(source: str) -> tuple[bool, tuple[tuple[str, str], ...]]:
    """The verify verdict and every obligation's kind and status."""
    verified = pipeline.verify(source)
    return verified.ok, tuple(sorted(
        (o.kind, o.status) for o in verified.obligations))


def _codes(checked: pipeline.Checked) -> tuple[str, ...]:
    return tuple(d.error_code for d in checked.errors)


#: Each neighbour's verify verdict and obligations at the base (c9235415),
#: by kind; a call's callee adds its own `requires` and `ensures`.
_BASE_NEIGHBOUR: dict[str, tuple[tuple[str, str], ...]] = {
    kind: (("assert", "tier3"), ("ensures", "verified"), ("requires", "verified"))
    for kind in ("requires", "ensures", "assert", "alias", "field", "parameter")
} | {
    "decreases": (("assert", "tier3"), ("decreases", "verified"),
                  ("ensures", "verified"), ("int_overflow", "verified"),
                  ("nat_bind", "verified"), ("requires", "verified")),
    "assume": (("ensures", "verified"), ("requires", "verified")),
    "result": (("assert", "tier3"), ("ensures", "verified"),
               ("refine_bind", "verified"), ("requires", "verified")),
}


def _base_neighbour(kind: str, form: str) -> tuple[tuple[str, str], ...]:
    statuses = _BASE_NEIGHBOUR[kind]
    if form == "a call":
        statuses = (*statuses, ("ensures", "verified"), ("requires", "verified"))
    return tuple(sorted(statuses))


# =====================================================================
# The matrix: every predicate kind by every form that performs an effect
# =====================================================================


@pytest.mark.parametrize("form", list(_FORMS))
@pytest.mark.parametrize("kind", list(_KINDS))
def test_cell(kind: str, form: str) -> None:
    """Refused at check where the effect is performed, once.  A
    user-declared effect's operation is E340's where it is written and
    where its row names it (rule 6, #1699), as at the base."""
    source = _program(kind, form)
    checked = pipeline.check(source)
    if form == "Counter.tick":
        assert set(_codes(checked)) == {"E340"}, (_codes(checked), source)
        return
    marker = _FORMS[form][3]
    assert _placed(checked) == [("E187", *_locate(source, marker))], (
        [(d.error_code, d.description) for d in checked.errors], source)


@pytest.mark.parametrize("form", _PERFORMING)
@pytest.mark.parametrize("kind", list(_KINDS))
def test_neighbour(kind: str, form: str) -> None:
    """The nearest accepted neighbour, the operation performed in the body
    and its value checked there, checks with no diagnostic and verifies as
    at the base."""
    source = _neighbour(kind, form)
    checked = pipeline.check(source)
    assert not checked.diagnostics, (
        [(d.error_code, d.description) for d in checked.diagnostics], source)
    assert _statuses(source) == (True, _base_neighbour(kind, form)), source


# =====================================================================
# The negative space: what a predicate may hold
# =====================================================================

#: An operation under a handler written inside the predicate: the handler
#: handles its effect there, so the predicate is pure.
_HANDLED: dict[str, str] = {
    "State": ("handle[State<Int>](@Int = 0) { get(@Unit) -> { resume(@Int.0) }, "
              "put(@Int) -> { resume(()) } } in { get(()) } >= 0"),
    "Exn": ('handle[Exn<String>] { throw(@String) -> { false } } in '
            '{ if true then { true } else { Exn.throw("x") } }'),
}

#: Their verify verdict's obligations at the base, by kind, the same for
#: both handlers.
_BASE_HANDLED: dict[str, tuple[tuple[str, str], ...]] = {
    "requires": (("ensures", "verified"), ("requires", "tier3")),
    "ensures": (("ensures", "tier3"), ("requires", "verified")),
    "decreases": (("decreases", "tier3"), ("ensures", "verified"),
                  ("int_overflow", "verified"), ("nat_bind", "verified"),
                  ("requires", "verified")),
    "assert": (("assert", "tier3"), ("ensures", "verified"),
               ("requires", "verified")),
    "result": (("ensures", "verified"), ("refine_bind", "tier3"),
               ("requires", "verified")),
} | {kind: (("ensures", "verified"), ("requires", "verified"))
     for kind in ("assume", "alias", "field", "parameter")}


@pytest.mark.parametrize("effect", list(_HANDLED))
@pytest.mark.parametrize("kind", list(_KINDS))
def test_an_operation_under_a_handler_in_the_predicate(
    kind: str, effect: str,
) -> None:
    """A `pure` function's predicate that performs an operation under a
    handler for its effect written inside the predicate is accepted, with
    the base's verdict: the handler handles the effect there, so nothing
    escapes the predicate."""
    source = _KINDS[kind].replace("PRED", _HANDLED[effect]).replace("EFF", "pure")
    checked = pipeline.check(source)
    assert not checked.diagnostics, (
        [(d.error_code, d.description) for d in checked.diagnostics], source)
    assert _statuses(source) == (True, tuple(sorted(_BASE_HANDLED[kind]))), source


#: What else a contract may hold, each with its verify verdict's obligations
#: at the base: contract-only state forms, and a pure call, closure and
#: quantifier.
_PURE_CONTRACTS: dict[str, tuple[str, tuple[tuple[str, str], ...]]] = {
    "old and new in an ensures": (
        "public fn f(@Unit -> @Int)\n  requires(true)\n"
        "  ensures(new(State<Int>) == old(State<Int>) + 1)\n"
        "  effects(<State<Int>>)\n{\n  let @Int = get(());\n"
        "  put(@Int.0 + 1);\n  @Int.0\n}\n",
        (("ensures", "tier3"), ("int_overflow", "tier3"),
         ("int_overflow", "tier3"), ("requires", "verified"))),
    "a pure call in a requires": (
        "private fn h(@Int -> @Int)\n  requires(true)\n"
        "  ensures(@Int.result == @Int.0)\n  effects(pure)\n{\n  @Int.0\n}\n\n"
        "public fn f(@Int -> @Int)\n  requires(h(@Int.0) >= 0)\n"
        "  ensures(true)\n  effects(<IO>)\n{\n  @Int.0\n}\n",
        (("ensures", "verified"), ("ensures", "verified"),
         ("requires", "verified"), ("requires", "verified"))),
    "apply_fn of a pure closure in a requires": (
        "public fn f(@Int -> @Int)\n"
        "  requires(apply_fn(fn(@Int -> @Bool) effects(pure) "
        "{ @Int.0 >= 0 }, @Int.0))\n"
        "  ensures(true)\n  effects(<IO>)\n{\n  @Int.0\n}\n",
        (("ensures", "verified"), ("requires", "tier3"))),
    "a pure quantifier in an ensures": (
        "public fn f(@Int -> @Int)\n  requires(true)\n"
        "  ensures(forall(@Nat, 3, fn(@Nat -> @Bool) effects(pure) "
        "{ @Nat.0 < 3 }))\n"
        "  effects(<IO>)\n{\n  @Int.0\n}\n",
        (("ensures", "tier3"), ("requires", "verified"))),
}


@pytest.mark.parametrize("name", list(_PURE_CONTRACTS))
def test_a_pure_contract_is_accepted(name: str) -> None:
    source, base = _PURE_CONTRACTS[name]
    checked = pipeline.check(source)
    assert not checked.diagnostics, (
        [(d.error_code, d.description) for d in checked.diagnostics], source)
    assert _statuses(source) == (True, tuple(sorted(base))), source


# =====================================================================
# The other places a predicate performs an effect
# =====================================================================


def test_a_closure_that_performs_io_written_in_a_requires_is_refused() -> None:
    """Applied or not: a row variable can carry a closure to an application
    nothing refuses (#294), so a predicate is held to the closures written
    in it, as a `pure` function is (#1702)."""
    source = ("public fn f(@Int -> @Int)\n"
              "  requires(array_length([fn(@Int -> @Bool) effects(<IO>) "
              "{ IO.time(()) >= 0 }]) == 1)\n"
              "  ensures(true)\n  effects(<IO>)\n{\n  @Int.0\n}\n")
    assert _placed(pipeline.check(source)) == [
        ("E187", *_locate(source, "fn(@Int -> @Bool)"))]


def test_a_quantifier_whose_predicate_performs_io_is_refused() -> None:
    """The quantifier applies its predicate where it is written, so an
    `ensures` holding one performs its effects: refused at the predicate,
    and the quantifier, under a row that does not permit them, draws no
    second code (mutant: the quantifier still held to the row, E125)."""
    source = ("public fn f(@Int -> @Int)\n  requires(true)\n"
              "  ensures(forall(@Nat, 3, fn(@Nat -> @Bool) effects(<IO>) "
              "{ IO.time(()) >= 0 }))\n"
              "  effects(pure)\n{\n  @Int.0\n}\n")
    assert _placed(pipeline.check(source)) == [
        ("E187", *_locate(source, "fn(@Nat -> @Bool)"))]


def test_apply_fn_of_a_function_value_that_performs_io_is_refused() -> None:
    source = ("type P = fn(Int -> Bool) effects(<IO>);\n\n"
              "public fn f(@Int, @P -> @Int)\n  requires(apply_fn(@P.0, @Int.0))\n"
              "  ensures(true)\n  effects(<IO>)\n{\n  @Int.0\n}\n")
    assert _placed(pipeline.check(source)) == [
        ("E187", *_locate(source, "apply_fn(@P.0"))]


def test_an_operation_in_a_body_refinement_is_refused() -> None:
    """A refinement predicate in a body is held to purity too, not to the
    function's row."""
    source = ("public fn f(@Int -> @Int)\n  requires(true)\n  ensures(true)\n"
              "  effects(<IO>)\n{\n  let @{ @Int | IO.time(()) >= 0 } = 5;\n"
              "  @Int.0\n}\n")
    assert _placed(pipeline.check(source)) == [
        ("E187", *_locate(source, "IO.time"))]


def test_an_operation_outside_the_function_s_row_draws_the_one_code() -> None:
    """Under a row that does not name the effect, the operation in a
    contract is E187, not E125: its fix is to move it, not to add the
    effect to the row (mutant: the row judged first)."""
    source = ("public fn f(@Int -> @Int)\n"
              "  requires(Random.random_int(1, 1) > 0)\n  ensures(true)\n"
              "  effects(<IO>)\n{\n  @Int.0\n}\n")
    assert _placed(pipeline.check(source)) == [
        ("E187", *_locate(source, "Random.random_int"))]


def test_a_pure_function_s_contract_draws_no_e122() -> None:
    """Under `pure`, the contract's operation is E187 at the operation, and
    the function, whose body performs nothing, draws no E122."""
    source = ("public fn f(@Int -> @Int)\n"
              "  requires(IO.time(()) >= 0)\n  ensures(true)\n"
              "  effects(pure)\n{\n  @Int.0\n}\n")
    assert _placed(pipeline.check(source)) == [
        ("E187", *_locate(source, "IO.time"))]


# =====================================================================
# The issue's program, its diagnostic, and its fix
# =====================================================================

_REPRO_1708 = """\
public fn f(@Int -> @Int)
  requires(Random.random_int(1, 1) > 0)
  ensures(true)
  effects(<Random>)
{
  @Int.0
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(<Random>)
{
  f(3)
}
"""


def test_repro_1708_the_issue_program_is_refused() -> None:
    """Checked, verified and ran at the base, printing 3 (mutant: the
    purity check dropped)."""
    checked = pipeline.check(_REPRO_1708)
    assert _placed(checked) == [
        ("E187", *_locate(_REPRO_1708, "Random.random_int"))]
    diagnostic = checked.errors[0]
    assert diagnostic.description == (
        "Effect operation 'Random.random_int' in the requires clause of "
        "'f' performs Random: a contract predicate must be pure.")
    assert diagnostic.spec_ref == 'Chapter 7, Section 7.9.1 "Pure Contracts"'


def test_repro_1708_the_fix_applied_literally_checks_clean() -> None:
    """E187's fix, applied to the reported program: the operation moved
    into the body, its value bound with `let` and checked with `assert`,
    and the requires clause written over the parameters alone."""
    fix = pipeline.check(_REPRO_1708).errors[0].fix
    assert fix == (
        "Perform 'Random.random_int' in the body of 'f' instead: bind its "
        "value with let there and check that value with assert, and write "
        "the requires clause over the parameters alone.")
    fixed = _REPRO_1708.replace(
        "  requires(Random.random_int(1, 1) > 0)\n", "  requires(true)\n"
    ).replace(
        "{\n  @Int.0\n}",
        "{\n  let @Int = Random.random_int(1, 1);\n  assert(@Int.0 > 0);\n"
        "  @Int.1\n}", 1)
    assert fixed != _REPRO_1708
    checked = pipeline.check(fixed)
    assert "E187" not in _codes(checked) and not checked.diagnostics, (
        [(d.error_code, d.description) for d in checked.diagnostics], fixed)


@pytest.mark.parametrize(("kind", "where"), [
    ("requires", "the requires clause of 'f'"),
    ("ensures", "the ensures clause of 'f'"),
    ("decreases", "the decreases clause of 'f'"),
    ("assert", "an assert in 'f'"),
    ("assume", "an assume in 'f'"),
    ("alias", "a refinement predicate"),
])
def test_the_diagnostic_names_the_predicate_and_the_operation(
    kind: str, where: str,
) -> None:
    errors = pipeline.check(_program(kind, "IO.time")).errors
    assert [d.description for d in errors] == [
        f"Effect operation 'IO.time' in {where} performs IO: a contract "
        f"predicate must be pure."]


def test_the_assert_fix_applied_literally_checks_clean() -> None:
    """For an `assert`, the fix binds the value before it and checks the
    bound value in it."""
    source = _program("assert", "IO.time")
    fix = pipeline.check(source).errors[0].fix
    assert fix == (
        "Bind the value of 'IO.time' with let before the assert, and check "
        "the bound value in it.")
    fixed = source.replace(
        "  assert(IO.time(()) >= 0);\n",
        "  let @Int = IO.time(());\n  assert(@Int.0 >= 0);\n")
    fixed = fixed.replace("  @Int.0\n}", "  @Int.1\n}")
    checked = pipeline.check(fixed)
    assert not checked.diagnostics, (
        [(d.error_code, d.description) for d in checked.diagnostics], fixed)


def test_the_refinement_fix_applied_literally_checks_clean() -> None:
    """For a refinement predicate, the fix moves the operation into the
    body and writes the predicate over its value alone."""
    source = _program("alias", "IO.time")
    fix = pipeline.check(source).errors[0].fix
    assert fix == (
        "Perform 'IO.time' in a function's body instead: bind its value with "
        "let there and check that value with assert, and write the "
        "refinement predicate over its own value alone.")
    fixed = source.replace("{ @Int | IO.time(()) >= 0 }", "{ @Int | true }")
    fixed = fixed.replace(
        "{\n  @Odd.0\n}",
        "{\n  let @Int = IO.time(());\n  assert(@Int.0 >= 0);\n  @Odd.0\n}")
    checked = pipeline.check(fixed)
    assert not checked.diagnostics, (
        [(d.error_code, d.description) for d in checked.diagnostics], fixed)


# =====================================================================
# A handler written inside the predicate handles its own instance alone
# =====================================================================
#
# `handle[State<Bool>]` inside a predicate does not handle the `State<Int>`
# a callee performs, nor `handle[Exn<String>]` an `Exn<Int>`: each place is
# judged by the instances it performs, and an effect is handled only by a
# handler of an equal instance written inside the predicate (PR #1762
# review: the names alone made the contract perform the caller's effect).

_BUMP = ("private fn bump(@Unit -> @Int)\n  requires(true)\n  ensures(true)\n"
         "  effects(<State<Int>>)\n{\n  put(get(()) + 1);\n  get(())\n}\n\n")
_RISKY = ("private fn risky(@Int -> @Int)\n  requires(true)\n  ensures(true)\n"
          "  effects(<Exn<Int>>)\n{\n"
          "  if @Int.0 > 0 then { Exn.throw(7) } else { 0 }\n}\n\n")

#: effect -> (the function's row, its declarations, the handler written in
#: the predicate at another instantiation, the one at the same, ROUTE the
#: place that performs the effect).
_INSTANCES: dict[str, tuple[str, str, str, str]] = {
    "State": (
        "<State<Int>>", _BUMP,
        "handle[State<Bool>](@Bool = true) { get(@Unit) -> { resume(@Bool.0) }, "
        "put(@Bool) -> { resume(()) } } in { ROUTE } >= 0",
        "handle[State<Int>](@Int = 0) { get(@Unit) -> { resume(@Int.0) }, "
        "put(@Int) -> { resume(()) } } in { ROUTE } >= 0"),
    "Exn": (
        "<Exn<Int>>", _RISKY,
        "handle[Exn<String>] { throw(@String) -> { false } } in { ROUTE >= 0 }",
        "handle[Exn<Int>] { throw(@Int) -> { false } } in { ROUTE >= 0 }"),
}

#: route -> effect -> (the place that performs it, the text E187 is placed
#: at).  A parameter's route needs a parameter, so it is written only in the
#: kinds whose function names one beside its `@Int`.
_ROUTES: dict[str, dict[str, tuple[str, str]]] = {
    "a call": {"State": ("bump(())", "bump(())"),
               "Exn": ("risky(1)", "risky(1)")},
    "apply_fn of a literal": {
        "State": ("apply_fn(fn(@Unit -> @Int) effects(<State<Int>>) "
                  "{ bump(()) }, ())", "fn(@Unit -> @Int)"),
        "Exn": ("apply_fn(fn(@Int -> @Int) effects(<Exn<Int>>) "
                "{ risky(@Int.0) }, 1)", "fn(@Int -> @Int)")},
    "an unapplied literal": {
        "State": ("array_length([fn(@Unit -> @Int) effects(<State<Int>>) "
                  "{ bump(()) }])", "fn(@Unit -> @Int)"),
        "Exn": ("array_length([fn(@Int -> @Int) effects(<Exn<Int>>) "
                "{ risky(@Int.0) }])", "fn(@Int -> @Int)")},
    "apply_fn of a parameter": {"State": ("apply_fn(@P.0, ())", "apply_fn(@P.0"),
                                "Exn": ("apply_fn(@P.0, 1)", "apply_fn(@P.0")},
}
_PARAMETER_TYPES = {"State": "type P = fn(Unit -> Int) effects(<State<Int>>);\n\n",
                    "Exn": "type P = fn(Int -> Int) effects(<Exn<Int>>);\n\n"}
_NAMING_A_PARAMETER = ("requires", "ensures", "assert", "assume")


def _instance_program(kind: str, effect: str, route: str, *, same: bool) -> str:
    row, decls, other, same_handler = _INSTANCES[effect]
    pred = (same_handler if same else other).replace(
        "ROUTE", _ROUTES[route][effect][0])
    source = _KINDS[kind].replace("PRED", pred).replace("EFF", row)
    if route == "apply_fn of a parameter":
        decls += _PARAMETER_TYPES[effect]
        source = source.replace("public fn f(@Int -> @Int)",
                                "public fn f(@Int, @P -> @Int)")
    return decls + source


_INSTANCE_CELLS = [
    (kind, effect, route)
    for route in _ROUTES for effect in _INSTANCES for kind in _KINDS
    if route != "apply_fn of a parameter" or kind in _NAMING_A_PARAMETER
]


@pytest.mark.parametrize(("kind", "effect", "route"), _INSTANCE_CELLS)
def test_a_handler_of_another_instantiation_does_not_handle(
    kind: str, effect: str, route: str,
) -> None:
    """Under a handler for another instantiation of the effect, written
    inside the predicate, the place still performs the function's instance:
    refused there, once."""
    source = _instance_program(kind, effect, route, same=False)
    checked = pipeline.check(source)
    marker = _ROUTES[route][effect][1]
    assert _placed(checked) == [("E187", *_locate(source, marker))], (
        [(d.error_code, d.description) for d in checked.errors], source)


#: The neighbour's verify obligations at the base (54b5034f), by kind: a
#: call under a handler of the same instantiation, which handles its effect
#: there.  The callee adds its own `requires` and `ensures`, and `bump` its
#: `get(()) + 1`'s overflow check.
_BASE_SAME_HANDLER: dict[str, tuple[tuple[str, str], ...]] = {
    "requires": (("requires", "tier3"), ("ensures", "verified")),
    "ensures": (("ensures", "tier3"), ("requires", "verified")),
    "decreases": (("decreases", "tier3"), ("ensures", "verified"),
                  ("int_overflow", "verified"), ("nat_bind", "verified"),
                  ("requires", "verified")),
    "assert": (("assert", "tier3"), ("ensures", "verified"),
               ("requires", "verified")),
    "result": (("refine_bind", "tier3"), ("ensures", "verified"),
               ("requires", "verified")),
} | {kind: (("ensures", "verified"), ("requires", "verified"))
     for kind in ("assume", "alias", "field", "parameter")}
_CALLEE = {"State": (("ensures", "verified"), ("requires", "verified"),
                     ("int_overflow", "tier3")),
           "Exn": (("ensures", "verified"), ("requires", "verified"))}


@pytest.mark.parametrize("effect", list(_INSTANCES))
@pytest.mark.parametrize("kind", list(_KINDS))
def test_a_handler_of_the_same_instantiation_handles(kind: str, effect: str) -> None:
    """The neighbour: the call under a handler of its own instantiation,
    written inside the predicate, is pure there, accepted with the base's
    verdict and statuses."""
    source = _instance_program(kind, effect, "a call", same=True)
    checked = pipeline.check(source)
    assert not checked.diagnostics, (
        [(d.error_code, d.description) for d in checked.diagnostics], source)
    base = tuple(sorted((*_BASE_SAME_HANDLER[kind], *_CALLEE[effect])))
    assert _statuses(source) == (True, base), source


# =====================================================================
# A handler written around the predicate handles nothing in it
# =====================================================================

#: effect -> (the handler written around the statement, the operation).
_AROUND: dict[str, tuple[str, str]] = {
    "State": ("handle[State<Int>](@Int = 0) {\n    get(@Unit) -> { resume(@Int.0) },\n"
              "    put(@Int) -> { resume(()) }\n  } in {\n    STMT\n    @Int.0\n  }",
              "get(()) >= 0"),
    "Exn": ("handle[Exn<String>] {\n    throw(@String) -> { 0 }\n  } in {\n"
            "    STMT\n    @Int.0\n  }",
            'if true then { true } else { Exn.throw("x") }'),
}
_AROUND_KINDS: dict[str, str] = {
    "assert": "assert(OP);",
    "assume": "assume(OP);",
    "let refinement": "let @{ @Int | OP } = 5;",
}
#: Each neighbour: the value bound before the predicate, under the same
#: handler, and the predicate over the bound value.
_AROUND_NEIGHBOURS: dict[str, str] = {
    "assert": "let @Bool = OP;\n    assert(@Bool.0);",
    "assume": "let @Bool = OP;\n    assume(@Bool.0);",
    "let refinement": "let @Bool = OP;\n    assert(@Bool.0);\n"
                      "    let @{ @Int | @Int.0 >= 0 } = 5;",
}


def _around(effect: str, stmt: str) -> str:
    handler, op = _AROUND[effect]
    return ("public fn f(@Int -> @Int)\n  requires(true)\n  ensures(true)\n"
            "  effects(pure)\n{\n  "
            + handler.replace("STMT", stmt.replace("OP", op)) + "\n}\n")


@pytest.mark.parametrize("effect", list(_AROUND))
@pytest.mark.parametrize("kind", list(_AROUND_KINDS))
def test_a_handler_around_the_predicate_handles_nothing_in_it(
    kind: str, effect: str,
) -> None:
    """A handler written around an `assert`, an `assume` or a `let`'s
    refinement is outside the predicate, so it handles nothing there: the
    operation is refused (mutant: every handler in force counted)."""
    source = _around(effect, _AROUND_KINDS[kind])
    marker = "get(())" if effect == "State" else "Exn.throw"
    assert _placed(pipeline.check(source)) == [
        ("E187", *_locate(source, marker))], source


#: The neighbours' verify obligations at the base.
_BASE_AROUND: dict[str, tuple[tuple[str, str], ...]] = {
    "assert": (("assert", "tier3"), ("ensures", "verified"), ("requires", "verified")),
    "assume": (("ensures", "verified"), ("requires", "verified")),
    "let refinement": (("assert", "tier3"), ("ensures", "verified"),
                       ("refine_bind", "verified"), ("requires", "verified")),
}


@pytest.mark.parametrize("effect", list(_AROUND))
@pytest.mark.parametrize("kind", list(_AROUND_NEIGHBOURS))
def test_a_value_bound_under_the_handler_before_the_predicate(
    kind: str, effect: str,
) -> None:
    source = _around(effect, _AROUND_NEIGHBOURS[kind])
    checked = pipeline.check(source)
    assert not checked.diagnostics, (
        [(d.error_code, d.description) for d in checked.diagnostics], source)
    assert _statuses(source) == (True, tuple(sorted(_BASE_AROUND[kind]))), source


# =====================================================================
# An application is judged by the type it applies
# =====================================================================


@pytest.mark.parametrize("row", ["<IO>", "<State<Int>>"])
def test_apply_fn_of_a_literal_whose_type_names_an_effect_is_refused(row: str) -> None:
    """The literal performs nothing, but its type names an effect, and the
    application is held to the type, as an `apply_fn` of any other value is
    and as a `pure` body holds it (E125): one code, at the application."""
    source = ("public fn f(@Int -> @Int)\n"
              f"  requires(apply_fn(fn(@Int -> @Bool) effects({row}) {{ true }}, 0))\n"
              "  ensures(true)\n  effects(pure)\n{\n  @Int.0\n}\n")
    assert _placed(pipeline.check(source)) == [
        ("E187", *_locate(source, "apply_fn("))]


def test_a_quantifier_whose_predicate_type_names_an_effect_is_refused() -> None:
    source = ("public fn f(@Int -> @Int)\n  requires(true)\n"
              "  ensures(forall(@Nat, 3, fn(@Nat -> @Bool) effects(<IO>) { true }))\n"
              "  effects(pure)\n{\n  @Int.0\n}\n")
    assert _placed(pipeline.check(source)) == [
        ("E187", *_locate(source, "forall("))]


def test_the_unapplied_closure_fix_applied_literally_checks_clean() -> None:
    """The fix for an anonymous function written in a predicate names no
    application, which an unapplied one does not have."""
    source = ("public fn f(@Int -> @Int)\n"
              "  requires(array_length([fn(@Int -> @Bool) effects(<IO>) "
              "{ IO.time(()) >= 0 }]) == 1)\n"
              "  ensures(true)\n  effects(<IO>)\n{\n  @Int.0\n}\n")
    fix = pipeline.check(source).errors[0].fix
    assert fix == (
        "Write the anonymous function in the body of 'f' instead, and write "
        "the requires clause over the parameters alone: a contract predicate "
        "may write only an anonymous function that performs no effect.")
    fixed = source.replace(
        "  requires(array_length([fn(@Int -> @Bool) effects(<IO>) "
        "{ IO.time(()) >= 0 }]) == 1)\n", "  requires(true)\n").replace(
        "{\n  @Int.0\n}",
        "{\n  let @Int = array_length([fn(@Int -> @Bool) effects(<IO>) "
        "{ IO.time(()) >= 0 }]);\n  @Int.1\n}")
    checked = pipeline.check(fixed)
    assert not checked.diagnostics, (
        [(d.error_code, d.description) for d in checked.diagnostics], fixed)
