"""An effect operation is held to the row in force, wherever it is performed (#1702).

A call to a function is held to the effect row in force where it is written:
a `<Random>` callee called under `<IO>` is E125.  An operation of a built-in
effect was not.  The checker compared the operations a body performs with
its row only when the row was `pure` (E122, at the declaration), so
`effects(<IO>)` performing `Random.random_int(3, 3)` checked, verified and
ran, and so did `IO.print` in a `handle[State<Int>]` body inside a `pure`
function, and a bare `throw` under `<IO>`, which code generation then
dropped.  A closure literal's body was checked under the row around it,
which the closure's own declared row did not replace: a closure declared
`effects(<E>)` performing `Random` inside an `<IO>` function ran (#294's
measured instance), and one declared `effects(pure)` performing `Random`
inside a `<Random>` function was given a pure type.

Two mechanisms, one judgement of the call (`_check_op_call`).  The row: where
a row is in force, an operation of a built-in effect is permitted where the
row names the effect, by name (`<State<Int>>` permits `put`; which instance
types the call is the operation's typing), and a row variable names no
effect, so `<IO, E>` permits `IO`'s operations and no others.  A handler's
body is checked under the row around it with the handled effect added, its
clauses under the row around it, and a closure's body under the closure's
own row, the operations it performs its own.  Under a row that is not
`pure`, an operation the row does not name is refused at the call (E125);
under `pure` the declaration that performs it is refused, as before (E122),
a closure at the closure, with no second code at the call.  The lowering,
`vera.lowering` rule 7: code generation compiles a closure as a function of
its own, with no `State` cell or `Exn` tag from its row, so a `State` or
`Exn` operation in a closure's body is refused at the call (E340) unless a
handler for its effect is written inside the closure, around it; a handler
around the closure does not count, since the closure can be applied outside
it.  A call rule 7 refuses is not also held to the row, nor counted by the
purity check.  A quantifier's predicate is a closure literal code
generation inlines into the function around the quantifier: its body is
under its own row, the quantifier is held to that row where it applies it
(E125, its effects counted for the purity check, as `apply_fn` is), and
rule 7 does not read it.  A function's signature, a `where` helper's
included, is checked where no row is in force, its body under its own row.
A refused call keeps the result type its signature fixes,
and a `get` no row entry or handler gives an instance to is typed unknown,
so a use of its result is no second error.  An operation of a user-declared
effect is E340's (rule 6, #1699), and a refinement predicate checked where
no function's row is in force is not judged.

The instrument crosses each built-in effect's operation, qualified and,
where the bare spelling has a route, bare, with the row in force (`pure`, one
naming the effect, one naming another, one naming both, and, where a row
variable may be written, an open row naming either) and where the operation
is written: a function's body, a `let` initialiser, an `if` arm, a `match`
arm, a `where` helper's body, a handler's body (for the operation's effect
and for another), a handler's clause, a closure's body inside a function
whose row is `pure`, names the effect or names another, a closure's body
inside a handler for the effect, and a closure with that handler written
inside it; and, in `test_quantifier_cell`, a quantifier's predicate whose
row is each declared row, under a function whose row is `pure`, names the
effect, or names both.  Each cell's expectation is the rule above, in
`Cell.expected` and the quantifier test's own statement of it: one code
for each judgement that refuses (an operation's, and a quantifier's
application of its predicate), where each is reported, and E122's and rule
7's messages.  The negative space is every cell the rules accept: it checks
with no diagnostic and verifies with every obligation proved, each accepted
closure compiles and runs, and each accepted quantifier compiles.  The
reported programs, rule 7's base instances, a helper's signature under a
`pure` and an `<IO>` parent, the fix each new refusal names and a killer
for each mechanism's mutant are unparametrised tests, or parametrised
within the sampler's floor, which every pull request runs.
"""

from __future__ import annotations

from dataclasses import dataclass

import pytest

from tests import pipeline
from vera.checker.registration import builtin_effect_names
from vera.environment import TypeEnv
from vera.lowering import HANDLED_EFFECTS

# A generated class instrument (tests/matrix_sample.py): a pull request runs a
# sample of its parametrised cells, and all of them when it changes this file
# or a module that decides its class: the operation judgement in the call
# checker, the closure's row in the expression checker, the function's row in
# the core, and rule 7 in the lowering rules.
pytestmark = pytest.mark.matrix(
    decides=[
        "vera/checker/calls.py",
        "vera/checker/expressions.py",
        "vera/checker/core.py",
        "vera/lowering.py",
    ],
)


# =====================================================================
# Helpers
# =====================================================================


def _locate(source: str, marker: str, occurrence: int = 0) -> tuple[int, int]:
    """1-based (line, column) of *marker*'s *occurrence*-th match."""
    idx = -1
    for _ in range(occurrence + 1):
        idx = source.index(marker, idx + 1)
    line = source.count("\n", 0, idx) + 1
    column = idx - (source.rfind("\n", 0, idx) + 1) + 1
    return line, column


def _placed(checked: pipeline.Checked) -> list[tuple[str, int, int]]:
    return [(d.error_code, d.location.line, d.location.column)
            for d in checked.errors]


def _codes(checked: pipeline.Checked) -> tuple[str, ...]:
    return tuple(d.error_code for d in checked.errors)


def _holds_clean(source: str) -> None:
    """The negative space: no diagnostic, and every obligation proved."""
    checked = pipeline.check(source)
    assert not checked.diagnostics, (
        [(d.error_code, d.description) for d in checked.diagnostics], source)
    verified = pipeline.verify(source)
    assert verified.ok, (verified.errors, source)
    assert {o.status for o in verified.obligations} <= {"verified"}, (
        [(o.kind, o.status) for o in verified.obligations], source)


def _fn(name: str, row: str, body: str, *, forall: str = "") -> str:
    """A public function of an `@Int` that returns an `@Int`."""
    head = f"public {forall}fn {name}" if forall else f"public fn {name}"
    return (f"{head}(@Int -> @Int)\n  requires(true)\n  ensures(true)\n"
            f"  effects({row})\n{{\n{body}\n}}\n")


# =====================================================================
# The reported programs
# =====================================================================

#: #1702: a built-in operation under a row that names another effect.
_REPRO_1702 = """\
public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(<IO>)
{
  Random.random_int(3, 3)
}
"""

#: #294's 2026-10-14 instance: the operation in a closure whose row is a row
#: variable, inside a function whose row names `IO`.
_REPRO_294 = """\
type F<E> = fn(Unit -> Int) effects(<E>);

private forall<E> fn f(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(<IO>)
{
  let @F<E> = fn(@Unit -> @Int) effects(<E>) { Random.random_int(1, 3) };
  apply_fn(@F<E>.0, ())
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(<IO>)
{
  f(())
}
"""

#: The `pure` function whose handler's body performed `IO`: the handler adds
#: `State<Int>` to the row its body is checked under, and that row was never
#: compared with the operations performed in it.
_REPRO_HANDLER_BODY = """\
public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Int>](@Int = 5) {
    get(@Unit) -> { resume(@Int.0) },
    put(@Int) -> { resume(()) }
  } in {
    IO.print("leak");
    get(())
  }
}
"""


def test_repro_1702_an_operation_under_a_row_that_does_not_name_it() -> None:
    """Accepted, verified and run at the base, printing 3."""
    checked = pipeline.check(_REPRO_1702)
    assert _placed(checked) == [
        ("E125", *_locate(_REPRO_1702, "Random.random_int"))], checked.errors
    error = checked.errors[0]
    assert error.description == (
        "Effect operation 'Random.random_int' requires effects(<Random>) but "
        "call site only allows effects(<IO>)."), error.description
    assert error.spec_ref == 'Chapter 7, Section 7.4 "Performing Effects"'


def test_repro_294_an_operation_in_a_closure_under_a_row_variable() -> None:
    """The closure's own row, `<E>`, names no `Random`: the tail is no
    licence, and the `<IO>` around the closure is not its row."""
    checked = pipeline.check(_REPRO_294)
    assert _placed(checked) == [
        ("E125", *_locate(_REPRO_294, "Random.random_int"))], checked.errors
    assert checked.errors[0].description == (
        "Effect operation 'Random.random_int' requires effects(<Random>) but "
        "call site only allows effects(<E>).")


def test_repro_an_operation_in_a_handler_body_in_a_pure_function() -> None:
    """Accepted and run at the base, printing `leak` from a `pure`
    function: the handler's body is checked under `<State<Int>>`."""
    checked = pipeline.check(_REPRO_HANDLER_BODY)
    assert _placed(checked) == [
        ("E125", *_locate(_REPRO_HANDLER_BODY, "IO.print"))], checked.errors
    assert checked.errors[0].description == (
        "Effect operation 'IO.print' requires effects(<IO>) but call site "
        "only allows effects(<State<Int>>).")


#: `vera.lowering` rule 7's base instances: a closure performing a `State`
#: or `Exn` operation with no handler for it written inside the closure,
#: under a row naming the effect, was accepted at check and refused by code
#: generation — bare with E602, qualified with a module that did not
#: assemble (an import the module does not declare).
_RULE_7_REPRO = """\
type F = fn(Int -> Int) effects(<ROW>);

public fn f(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(<ROW>)
{
  let @F = fn(@Int -> @Int) effects(<ROW>) {
    OP;
    @Int.0
  };
  apply_fn(@F.0, @Int.0)
}
"""


def _rule_7_repro(row: str, op: str) -> str:
    return _RULE_7_REPRO.replace("ROW", row).replace("OP", op)


def _codegen_refuses(source: str) -> list[str]:
    """What code generation reports for *source* past the check: its
    errors' codes, an uncoded one as "uncoded"."""
    result = pipeline.compile(source, past_check=True).result
    return [d.error_code or "uncoded" for d in result.diagnostics
            if d.severity == "error"
            or (d.error_code or "").startswith("E6")]


@pytest.mark.parametrize(("row", "op", "backend"), [
    ("State<Int>", "put(@Int.0)", "E602"),
    ("State<Int>", "State.put(@Int.0)", "uncoded"),
    ("Exn<Int>", "throw(@Int.0)", "E602"),
    ("Exn<Int>", "Exn.throw(@Int.0)", "uncoded"),
])
def test_repro_rule_7_a_cell_operation_in_a_closure(
    row: str, op: str, backend: str,
) -> None:
    """Accepted at the base under a row naming the effect, and refused by
    code generation: refused at check now, at the call, with E340."""
    source = _rule_7_repro(row, op)
    checked = pipeline.check(source)
    assert _placed(checked) == [("E340", *_locate(source, op))], (
        [(d.error_code, d.description) for d in checked.errors])
    assert backend in _codegen_refuses(source)


# =====================================================================
# The edges of each mechanism, and the mutants' killers
# =====================================================================
#
# The matrix is sampled on a pull request; these run in full on every one.


def test_a_bare_operation_is_judged() -> None:
    """Bare and qualified calls share one judgement (mutant: the
    qualified path's alone)."""
    source = _fn("f", "<IO>", "  put(@Int.0);\n  @Int.0")
    assert _codes(pipeline.check(source)) == ("E125",)


def test_any_instance_of_the_effect_permits_its_operation() -> None:
    """By name, not by instance: `<State<Int>>` permits `put` (mutant: the
    operation's effect compared as an instance)."""
    _holds_clean(_fn("f", "<State<Int>>", "  put(@Int.0);\n  @Int.0"))
    _holds_clean(_fn("f", "<Exn<Int>>", "  throw(@Int.0);\n  @Int.0"))


def test_an_open_row_permits_only_what_it_names() -> None:
    """A row variable names no effect (mutant: the tail as a licence)."""
    source = ("type F<E> = fn(Int -> Int) effects(<IO, E>);\n\n"
              + _fn("f", "<IO>", (
                  "  let @F<E> = fn(@Int -> @Int) effects(<IO, E>) {\n"
                  "    Random.random_int(1, 1)\n  };\n  @Int.0"),
                  forall="forall<E> "))
    assert _placed(pipeline.check(source)) == [
        ("E125", *_locate(source, "Random.random_int"))]


def test_a_closure_is_held_to_its_own_row() -> None:
    """The closure's row, not the function's (mutant: the closure's row
    not installed): `<Random>` inside `<IO>` permits `Random`, and `<IO>`
    inside `<Random>` does not."""
    def closure(row: str, outer: str) -> str:
        return (f"type F = fn(Int -> Int) effects(<{row}>);\n\n"
                + _fn("f", f"<{outer}>", (
                    f"  let @F = fn(@Int -> @Int) effects(<{row}>) {{\n"
                    f"    Random.random_int(1, 1)\n  }};\n  @Int.0")))
    _holds_clean(closure("Random", "IO"))
    refused = closure("IO", "Random")
    assert _placed(pipeline.check(refused)) == [
        ("E125", *_locate(refused, "Random.random_int"))]


def test_a_closure_s_effects_are_not_the_function_s() -> None:
    """A `pure` function that builds a closure performing `Random`, and
    does not apply it, performs nothing (mutant: the closure's effects
    counted for the function, as at the base, where this was E122)."""
    source = ("type F = fn(Int -> Int) effects(<Random>);\n\n"
              + _fn("f", "pure", (
                  "  let @F = fn(@Int -> @Int) effects(<Random>) {\n"
                  "    Random.random_int(1, 1)\n  };\n  @Int.0")))
    _holds_clean(source)
    ran = pipeline.run(source, fn="f", args=[4])
    assert ran.ok and ran.value == 4, ran


def test_a_pure_closure_that_performs_an_effect_is_refused() -> None:
    """E122 at the closure (mutant: no purity check for a closure): at the
    base a `pure` closure performing `Random` inside a `<Random>` function
    was accepted, with a `pure` type."""
    source = ("type F = fn(Int -> Int) effects(pure);\n\n"
              + _fn("f", "<Random>", (
                  "  let @F = fn(@Int -> @Int) effects(pure) {\n"
                  "    Random.random_int(1, 1)\n  };\n  apply_fn(@F.0, 4)")))
    checked = pipeline.check(source)
    assert _placed(checked) == [
        ("E122", *_locate(source, "fn(@Int -> @Int) effects(pure)"))]
    assert checked.errors[0].description == (
        "Pure anonymous function performs effect operations: Random.")


def test_a_pure_row_draws_one_code() -> None:
    """Under `pure` the declaration is refused (E122), and the call is not
    refused as well (mutant: the pure row judged at the call too)."""
    source = _fn("f", "pure", "  Random.random_int(1, 1)")
    assert _placed(pipeline.check(source)) == [
        ("E122", *_locate(source, "fn f("))]


def test_a_refused_get_draws_no_second_error() -> None:
    """No row entry or handler types a refused `get`, and its result is no
    second error (mutant: the result typed by the effect's parameter,
    which a `let @Int` refuses, E170)."""
    source = _fn("f", "<IO>", "  let @Int = get(());\n  @Int.0")
    assert _placed(pipeline.check(source)) == [
        ("E125", *_locate(source, "get(())"))]


def test_a_bare_operation_without_a_route_is_also_held_to_the_row() -> None:
    """A bare `random_int` outside a handler has no route (E217), and its
    row does not name `Random` (E125): two judgements, of the spelling and
    of the row, as under `pure` (E217 and the function's E122)."""
    source = _fn("f", "<IO>", "  random_int(1, 1)")
    assert _codes(pipeline.check(source)) == ("E217", "E125")
    pure = _fn("f", "pure", "  random_int(1, 1)")
    assert _codes(pipeline.check(pure)) == ("E217", "E122")


def test_a_contract_is_held_to_the_function_s_row() -> None:
    """A contract is checked under the function's row, so its operation
    is held to it."""
    source = ("public fn f(@Int -> @Int)\n"
              "  requires(Random.random_int(1, 1) > 0)\n  ensures(true)\n"
              "  effects(<IO>)\n{\n  @Int.0\n}\n")
    assert _placed(pipeline.check(source)) == [
        ("E125", *_locate(source, "Random.random_int"))]


def test_a_host_operation_in_a_closure_lowers() -> None:
    """Rule 7 holds `State` and `Exn` alone (mutant: a host effect's
    operation refused in a closure too)."""
    source = ("type F = fn(Int -> Int) effects(<IO>);\n\n"
              + _fn("f", "<IO>", (
                  '  let @F = fn(@Int -> @Int) effects(<IO>) {\n'
                  '    IO.print("x");\n    @Int.0\n  };\n'
                  "  apply_fn(@F.0, @Int.0)")))
    _holds_clean(source)
    ran = pipeline.run(source, fn="f", args=[4])
    assert ran.ok and ran.value == 4 and ran.stdout == "x", ran


def test_a_handler_in_the_closure_lowers_its_operation() -> None:
    """Rule 7 reads the handlers written inside the closure (mutant: blind
    to them): the handler's cell is the lifted closure's."""
    source = (
        "type F = fn(Int -> Int) effects(pure);\n\n"
        + _fn("f", "pure", (
            "  let @F = fn(@Int -> @Int) effects(pure) {\n"
            "    handle[State<Int>](@Int = 0) {\n"
            "      get(@Unit) -> { resume(@Int.0) },\n"
            "      put(@Int) -> { resume(()) }\n"
            "    } in {\n      put(@Int.0);\n      get(())\n    }\n"
            "  };\n  apply_fn(@F.0, @Int.0)")))
    _holds_clean(source)
    ran = pipeline.run(source, fn="f", args=[4])
    assert ran.ok and ran.value == 4, ran  # the cell's initial value is 0


def test_a_handler_around_a_closure_does_not_lower_its_operation() -> None:
    """Rule 7 reads only the handlers written inside the closure (mutant:
    every handler in force): the closure is compiled apart from the one
    around it.  `tests/probes/state_handlers/dispatch_paths/p20_*` is this
    shape, refused at the base for other reasons."""
    source = (
        "type F = fn(Int -> Int) effects(<State<Int>>);\n\n"
        + _fn("f", "pure", (
            "  handle[State<Int>](@Int = 0) {\n"
            "    get(@Unit) -> { resume(@Int.0) },\n"
            "    put(@Int) -> { resume(()) }\n"
            "  } in {\n"
            "    let @F = fn(@Int -> @Int) effects(<State<Int>>) {\n"
            "      put(@Int.0);\n      @Int.0\n    };\n"
            "    apply_fn(@F.0, @Int.0)\n  }")))
    assert _placed(pipeline.check(source)) == [
        ("E340", *_locate(source, "put(@Int.0)"))]
    assert "E602" in _codegen_refuses(source)


@pytest.mark.parametrize("row", ("pure", "<IO>"))
def test_rule_7_is_the_call_s_one_refusal(row: str) -> None:
    """A call rule 7 refuses is neither held to the closure's row (E125)
    nor counted by its purity check (E122)."""
    source = (f"type F = fn(Int -> Int) effects({row});\n\n"
              + _fn("f", "pure", (
                  f"  let @F = fn(@Int -> @Int) effects({row}) {{\n"
                  "    put(@Int.0);\n    @Int.0\n  };\n  @Int.0")))
    assert _placed(pipeline.check(source)) == [
        ("E340", *_locate(source, "put(@Int.0)"))]


_REFINED = "@{ @Int | Random.random_int(1, 1) > 0 }"


@pytest.mark.parametrize("row", ("pure", "<IO>"))
@pytest.mark.parametrize("position", ("parameter", "return"))
@pytest.mark.parametrize("body", ("clean", "performs"))
def test_a_helper_s_signature_is_held_to_no_row(
    row: str, position: str, body: str,
) -> None:
    """A `where` helper's signature is checked where no function's row is
    in force, as a top-level signature is, so an operation in its
    refinement predicate is held to no row under a `pure` parent and an
    `<IO>` one alike, while the helper's body is held to the helper's own
    row (PR #1703 review: the predicate was held to the parent's row, which
    named the parent in its fix)."""
    param = _REFINED if position == "parameter" else "@Int"
    result = _REFINED if position == "return" else "@Int"
    performed = "Random.random_int(1, 1);\n    " if body == "performs" else ""
    source = (
        _fn("f", row, "  h(@Int.0)").rstrip("\n")
        + f"\nwhere {{\n  fn h({param} -> {result})\n    requires(true)\n"
        f"    ensures(true)\n    effects({row})\n  {{\n    {performed}1\n"
        "  }\n}\n")
    checked = pipeline.check(source)
    if body == "clean":
        assert not checked.diagnostics, [
            (d.error_code, d.description) for d in checked.diagnostics]
        return
    if row == "pure":
        assert _placed(checked) == [("E122", *_locate(source, "fn h("))]
        return
    assert _placed(checked) == [
        ("E125", *_locate(source, "Random.random_int(1, 1);"))]
    assert "the effects clause of 'h'" in checked.errors[0].fix


def _quantified(outer: str, pred: str, body: str, *, lead: str = "") -> str:
    """A `forall` in a function whose row is *outer*, over a predicate
    whose row is *pred* and whose body is *body*, after the statement
    *lead*."""
    return ("public fn f(@Int -> @Bool)\n  requires(true)\n  ensures(true)\n"
            f"  effects({outer})\n{{\n{lead}"
            f"  forall(@Int, 3, fn(@Int -> @Bool) effects({pred}) {{\n"
            f"    {body}\n  }})\n}}\n")


def test_repro_a_quantifier_applies_its_predicate_where_it_is_written() -> None:
    """Code generation inlines a quantifier's predicate into the function
    around it, so the quantifier performs the predicate's effects there:
    it is held to the predicate's row as `apply_fn` is (E125, and the
    effects counted for the purity check).  At the base the predicate's
    operations were the function's, and this `pure` function was E122."""
    source = _quantified("pure", "<IO>", 'IO.print("x");\n    true')
    assert _placed(pipeline.check(source)) == [
        ("E125", *_locate(source, "forall(")),
        ("E122", *_locate(source, "fn f("))]
    lacking = _quantified("<Random>", "<IO>", 'IO.print("x");\n    true')
    checked = pipeline.check(lacking)
    assert _placed(checked) == [("E125", *_locate(lacking, "forall("))]
    assert checked.errors[0].description == (
        "forall: its predicate requires effects(<IO>) but call site only "
        "allows effects(<Random>).")


def test_a_quantifier_predicate_s_cell_operation_lowers() -> None:
    """Rule 7 reads lifted closures only: a quantifier's predicate is
    compiled with the function around it, whose cell its `get` reads (it
    ran at the base)."""
    source = _quantified("<State<Int>>", "<State<Int>>", "get(()) > @Int.0",
                         lead="  put(@Int.0);\n")
    _holds_clean(source)
    assert pipeline.run(source, fn="f", args=[5]).value in (1, True)
    assert pipeline.run(source, fn="f", args=[1]).value in (0, False)


# =====================================================================
# The fix each new refusal names compiles clean
# =====================================================================


def _only_fix(source: str, code: str) -> str:
    """The fix of *source*'s one error, which carries *code*."""
    errors = pipeline.check(source).errors
    assert [d.error_code for d in errors] == [code], [
        (d.error_code, d.description) for d in errors]
    return errors[0].fix


def _row_in(fix: str) -> str:
    """The `effects(...)` clause a fix ends with."""
    return fix[fix.rindex("effects("):fix.index(")", fix.rindex("effects("))
               + 1]


def test_the_fix_of_an_operation_outside_a_function_s_row() -> None:
    fix = _only_fix(_REPRO_1702, "E125")
    assert fix.startswith("Add Random to the effects clause of 'main': "), fix
    fixed = _REPRO_1702.replace("effects(<IO>)", _row_in(fix))
    assert _row_in(fix) == "effects(<IO, Random>)"
    _holds_clean(fixed)
    ran = pipeline.run(fixed, fn="main")
    assert ran.ok and ran.value == 3, ran


def test_the_fix_of_a_cell_operation_names_the_instance() -> None:
    source = _fn("f", "<IO>", "  put(@Int.0);\n  @Int.0")
    fix = _only_fix(source, "E125")
    assert _row_in(fix.split(".  Or ")[0]) == "effects(<IO, State<Int>>)", fix
    assert "Or perform it inside a handle[State<Int>] block" in fix, fix
    _holds_clean(source.replace(
        "effects(<IO>)", _row_in(fix.split(".  Or ")[0])))


def test_the_fix_of_an_operation_outside_a_closure_s_row() -> None:
    source = ("type F = fn(Int -> Int) effects(<IO>);\n\n"
              + _fn("f", "<IO, Random>", (
                  "  let @F = fn(@Int -> @Int) effects(<IO>) {\n"
                  "    Random.random_int(3, 3)\n  };\n"
                  "  apply_fn(@F.0, @Int.0)")))
    fix = _only_fix(source, "E125")
    assert "the anonymous function's effects clause and to the row of the "\
        "function type it is given" in fix, fix
    row = _row_in(fix)
    assert row == "effects(<IO, Random>)", fix
    fixed = source.replace("effects(<IO>)", row)
    _holds_clean(fixed)
    ran = pipeline.run(fixed, fn="f", args=[4])
    assert ran.ok and ran.value == 3, ran


def test_the_fix_of_a_quantifier_under_a_row_that_lacks_its_predicate_s() -> None:
    source = _quantified("<Random>", "<IO>", 'IO.print("x");\n    true')
    fix = _only_fix(source, "E125")
    assert fix.startswith("Add IO to the effects clause of 'f': "), fix
    row = _row_in(fix.split(".  Or ")[0])
    assert row == "effects(<IO, Random>)", fix
    _holds_clean(source.replace("effects(<Random>)", row))


def test_the_fix_of_a_pure_closure_that_performs_an_effect() -> None:
    source = ("type F = fn(Int -> Int) effects(pure);\n\n"
              + _fn("f", "<Random>", (
                  "  let @F = fn(@Int -> @Int) effects(pure) {\n"
                  "    Random.random_int(3, 3)\n  };\n"
                  "  apply_fn(@F.0, @Int.0)")))
    fix = _only_fix(source, "E122")
    row = _row_in(fix)
    assert row == "effects(<Random>)", fix
    fixed = source.replace("effects(pure)", row)
    _holds_clean(fixed)
    ran = pipeline.run(fixed, fn="f", args=[4])
    assert ran.ok and ran.value == 3, ran


def test_the_fix_of_a_cell_operation_in_a_closure() -> None:
    """Both ways out rule 7's fix names: the operation in the enclosing
    function, and the handler, whose code the fix carries, inside the
    closure."""
    source = _rule_7_repro("State<Int>", "put(@Int.0)")
    fix = _only_fix(source, "E340")
    assert "Perform 'put' in the enclosing function's body" in fix, fix
    handler = fix[fix.index("handle[State<Int>]"):fix.rindex(" in {")]
    assert handler == (
        "handle[State<Int>](@Int = <its initial value>) { get(@Unit) -> "
        "{ resume(@Int.0) }, put(@Int) -> { resume(()) } }"), fix
    inside = source.replace(
        "    put(@Int.0);\n    @Int.0\n",
        "    " + handler.replace("<its initial value>", "0")
        + " in { put(@Int.0); get(()) }\n")
    _holds_clean(inside)
    ran = pipeline.run(inside, fn="f", args=[4])
    assert ran.ok and ran.value == 4, ran
    outside = source.replace(
        "    put(@Int.0);\n    @Int.0\n", "    @Int.0\n").replace(
        "  apply_fn(@F.0, @Int.0)", "  put(@Int.0);\n  apply_fn(@F.0, @Int.0)")
    _holds_clean(outside)


# =====================================================================
# The class instrument
# =====================================================================


@dataclass(frozen=True)
class Op:
    """One built-in effect's operation, as a call written in a cell."""

    #: The effect, as `vera effects` lists it.
    effect: str
    #: The row entry that names it.
    entry: str
    #: The call, over the enclosing `@Int` where it takes an argument.
    call: str
    #: The type its result is bound at in a `let`; a `Unit` result is
    #: bound by none (E183), and its call is a statement of the initialiser.
    result: str
    #: "qualified" or "bare".
    spelling: str

    @property
    def label(self) -> str:
        return f"{self.effect}.{self.spelling}"


#: One operation per built-in effect that declares one, and the bare
#: spelling where it has a route without a handler (`put`, `throw`, §7.4).
_OPS: tuple[Op, ...] = (
    Op("IO", "IO", 'IO.print("x")', "Unit", "qualified"),
    Op("Random", "Random", "Random.random_int(1, 1)", "Int", "qualified"),
    Op("Http", "Http", 'Http.get("http://localhost")',
       "Result<String, String>", "qualified"),
    Op("DB", "DB", 'DB.execute("CREATE TABLE t (x INTEGER)", [])',
       "Result<Int, String>", "qualified"),
    Op("Inference", "Inference", 'Inference.complete("p")',
       "Result<String, String>", "qualified"),
    Op("State", "State<Int>", "State.put(@Int.0)", "Unit", "qualified"),
    Op("State", "State<Int>", "put(@Int.0)", "Unit", "bare"),
    Op("Exn", "Exn<Int>", "Exn.throw(@Int.0)", "Int", "qualified"),
    Op("Exn", "Exn<Int>", "throw(@Int.0)", "Int", "bare"),
)


def _other(op: Op) -> str:
    """An effect that is not *op*'s, for the rows that name another."""
    return "Random" if op.effect == "IO" else "IO"


#: The rows a function's own row may be: no row variable (`vera.lowering`
#: rule 6).  The label names the operation's effect X and the other Y.
_DECLARED_ROWS = ("pure", "<X>", "<Y>", "<X, Y>")
#: A closure's row may also be open.
_CLOSURE_ROWS = _DECLARED_ROWS + ("<Y, E>", "<X, E>")


def _row(label: str, op: Op) -> str:
    return (label.replace("X", op.entry).replace("Y", _other(op))
            if label != "pure" else "pure")


def _names(label: str) -> bool:
    """Whether the row a label writes names the operation's effect."""
    return "X" in label


#: A handler for each effect a handler lowers for, with the place its body
#: (BODY) and its operation's clause (CLAUSE) are written.
_HANDLERS: dict[str, str] = {
    "State": ("handle[State<Int>](@Int = 0) {\n"
              "    get(@Unit) -> { resume(@Int.0) },\n"
              "    put(@Int) -> { CLAUSE }\n"
              "  } in {\n    BODY\n  }"),
    "Exn": ("handle[Exn<Int>] {\n"
            "    throw(@Int) -> { CLAUSE }\n"
            "  } in {\n    BODY\n  }"),
}
#: What a clause does where no operation is written in it: `Exn`'s returns
#: a value no cell's operation returns, so a cell that runs the clause says
#: so.
_CLAUSE_TAIL = {"State": "resume(())", "Exn": "7"}


def _handler(effect: str, *, body: str = "@Int.0",
             clause: str | None = None) -> str:
    tail = _CLAUSE_TAIL[effect]
    return (_HANDLERS[effect].replace("BODY", body)
            .replace("CLAUSE", f"{clause};\n      {tail}"
                     if clause is not None else tail))


#: The closure sites: a closure with no handler, one inside a handler for
#: the operation's effect, and one with that handler written inside it,
#: around the operation (`vera.lowering` rule 7).
_CLOSURE_SITES = (
    "closure", "closure in a handler", "closure with a handler in it")


@dataclass(frozen=True)
class Cell:
    op: Op
    #: Where the operation is written.
    site: str
    #: The row of the declaration the site is in (a closure's, at a closure).
    row: str
    #: The handler of a handler site; the row of the function around a
    #: closure.
    around: str = ""

    @property
    def label(self) -> str:
        around = f"|{self.around}" if self.around else ""
        return f"{self.op.label}|{self.site}{around}|{self.row}"

    def source(self) -> str:
        op, row = self.op, _row(self.row, self.op)
        stmt = f"{op.call};\n  @Int.0"
        if self.site == "body":
            return _fn("f", row, f"  {stmt}")
        if self.site == "let":
            # A `Unit` is bound by no `let` (E183): its operation is the
            # initialiser's statement.
            init = (f"{{\n    {op.call};\n    1\n  }}" if op.result == "Unit"
                    else op.call)
            bound = "Int" if op.result == "Unit" else op.result
            return _fn("f", row, f"  let @{bound} = {init};\n  @Int.0")
        if self.site == "if arm":
            return _fn("f", row, (
                f"  if @Int.0 > 0 then {{\n    {op.call};\n    1\n"
                f"  }} else {{\n    0\n  }}"))
        if self.site == "match arm":
            return _fn("f", row, (
                f"  match @Int.0 {{\n    0 -> {{\n      {op.call};\n      1\n"
                f"    }},\n    _ -> 0\n  }}"))
        if self.site == "where helper":
            return (_fn("f", row, "  h(@Int.0)").rstrip("\n")
                    + f"\nwhere {{\n  fn h(@Int -> @Int)\n    requires(true)\n"
                    f"    ensures(true)\n    effects({row})\n  {{\n"
                    f"    {op.call};\n    @Int.0\n  }}\n}}\n")
        if self.site == "handler body":
            return _fn("f", row, "  " + _handler(
                self.around, body=f"{op.call};\n    @Int.0"))
        if self.site == "handler clause":
            return _fn("f", row, "  " + _handler(self.around, clause=op.call))
        if self.site in _CLOSURE_SITES:
            return self._closure(_row(self.around, op), row)
        raise AssertionError(self.site)  # pragma: no cover

    def _closure(self, outer: str, row: str) -> str:
        """A closure with row *row* in a function with row *outer*: bound
        and not applied, by itself or in a handler's body for the
        operation's effect, since the function is held to the closure's row
        only where the closure is applied; or, with the handler written
        inside it, applied, so the cell runs what the closure performs."""
        op = self.op
        generic = self.row.endswith(", E>")
        params = "<E>" if generic else ""
        closure = (f"fn(@Int -> @Int) effects({row}) {{\n"
                   f"    {op.call};\n    @Int.0\n  }}")
        binding = f"  let @F{params} = {closure};\n  @Int.0"
        if self.site == "closure in a handler":
            binding = "  " + _handler(op.effect, body=(
                f"let @F = {closure.replace(chr(10), chr(10) + '  ')};\n"
                f"    @Int.0"))
        elif self.site == "closure with a handler in it":
            # The handler's body reads the cell back, so a put that went
            # nowhere would show as its initial 0.
            tail = "get(())" if op.effect == "State" else "@Int.0"
            inner = _handler(op.effect, body=f"{op.call};\n    {tail}")
            binding = (f"  let @F = fn(@Int -> @Int) effects({row}) {{\n"
                       f"    {inner.replace(chr(10), chr(10) + '  ')}\n"
                       f"  }};\n  apply_fn(@F.0, @Int.0)")
        return (f"type F{params} = fn(Int -> Int) effects({row});\n\n"
                + _fn("f", outer, binding,
                      forall="forall<E> " if generic else ""))

    def lowers(self) -> bool:
        """`vera.lowering` rule 7: a `State` or `Exn` operation in a
        closure's body lowers under a handler written inside the closure."""
        return (self.op.effect not in _HANDLERS
                or self.site not in _CLOSURE_SITES
                or self.site == "closure with a handler in it")

    def expected(self) -> tuple[str, ...]:
        """THE rule: the codes the cell is refused with, one at most, none
        where the operation lowers and the row in force names its effect."""
        if not self.lowers():
            return ("E340",)
        # A handler adds its effect to the row its body is checked under.
        if self.site == "closure with a handler in it":
            return ()
        if self.site == "handler body" and self.around == self.op.effect:
            return ()
        if _names(self.row):
            return ()
        in_force_pure = self.row == "pure" and self.site != "handler body"
        return ("E122",) if in_force_pure else ("E125",)

    def refused_at(self, source: str) -> tuple[int, int]:
        """Where the refusal is reported: E125 and E340 at the call, E122
        at the declaration whose row is pure (the closure, at a closure)."""
        if self.expected() in (("E125",), ("E340",)):
            return _locate(source, self.op.call)
        if self.site in _CLOSURE_SITES:
            return _locate(source, "fn(@Int -> @Int) effects(")
        if self.site == "where helper":
            return _locate(source, "fn h(")
        return _locate(source, "fn f(")

    def purity_message(self) -> str:
        """E122's message, as the purity check words it."""
        if self.site in _CLOSURE_SITES:
            return (f"Pure anonymous function performs effect operations: "
                    f"{self.op.effect}.")
        name = "h" if self.site == "where helper" else "f"
        return (f"Pure function '{name}' performs effect operations: "
                f"{self.op.effect}.")

    def lowering_message(self) -> str:
        """Rule 7's E340, naming the closure and the operation."""
        written = self.op.call.split("(")[0]
        effect = self.op.effect
        return (f"Code generation cannot lower '{written}' in the body of an "
                f"anonymous function: a {effect} operation in a closure is "
                f"lowered only under a handler for {effect} written inside "
                f"the closure.")

    def runs_to(self) -> int | None:
        """What `f(4)` returns, for an accepted closure cell: the closure,
        bound and not applied, leaves the argument; applied, its handler
        reads back the `put` cell or runs the `throw` clause."""
        if self.site not in _CLOSURE_SITES:
            return None
        if self.site == "closure with a handler in it":
            return 4 if self.op.effect == "State" else 7
        return 4


#: The sites whose row is a declaration's own, a function's or a helper's.
_DECLARATION_SITES = ("body", "let", "if arm", "match arm", "where helper")


def _cells() -> list[Cell]:
    cells: list[Cell] = []
    for op in _OPS:
        for site in _DECLARATION_SITES:
            cells += [Cell(op, site, row) for row in _DECLARED_ROWS]
        for handled in _HANDLERS:
            cells += [Cell(op, "handler body", row, handled)
                      for row in _DECLARED_ROWS]
            # A clause's operation of the handler's own effect is the
            # enclosing context's (§7.5.2): E339 territory, not this one.
            if handled != op.effect:
                cells += [Cell(op, "handler clause", row, handled)
                          for row in _DECLARED_ROWS]
        for outer in ("pure", "<X>", "<Y>"):
            cells += [Cell(op, "closure", row, outer)
                      for row in _CLOSURE_ROWS]
        if op.effect in _HANDLERS:
            for outer in ("pure", "<X>"):
                cells += [Cell(op, "closure in a handler", row, outer)
                          for row in ("pure", "<Y>", "<X>")]
                # Applied, so a pure row the function can apply it under.
                cells.append(
                    Cell(op, "closure with a handler in it", "pure", outer))
    return cells


_CELLS = _cells()


class TestOperationRow:
    """Every built-in operation, every row in force, every place."""

    def test_every_registry_effect_with_an_operation_has_one(self) -> None:
        """The registry is the enumeration: an effect it gains with an
        operation is a cell the instrument lacks until it is added."""
        env = TypeEnv()
        with_ops = {name for name in builtin_effect_names()
                    if env.effects[name].operations}
        assert {op.effect for op in _OPS} == with_ops

    def test_every_bare_route_is_a_cell(self) -> None:
        """The bare spellings are the operations §7.4 routes without a
        handler, and each is crossed bare as well as qualified."""
        assert {op.call.split("(")[0] for op in _OPS
                if op.spelling == "bare"} == {"put", "throw"}

    def test_rule_7_covers_the_effects_a_handler_lowers_for(self) -> None:
        """The effects whose closure operations need a handler inside the
        closure are rule 1's, and each is crossed at every closure site."""
        assert set(_HANDLERS) == set(HANDLED_EFFECTS)
        sites = {(c.op.effect, c.site) for c in _CELLS}
        assert {(e, s) for e in HANDLED_EFFECTS
                for s in _CLOSURE_SITES} <= sites

    @pytest.mark.parametrize("outer", ("pure", "<X>", "<X, Y>"))
    @pytest.mark.parametrize("pred", _DECLARED_ROWS)
    @pytest.mark.parametrize("op", _OPS, ids=lambda o: o.label)
    def test_quantifier_cell(self, op: Op, pred: str, outer: str) -> None:
        """A quantifier's predicate, a closure literal code generation
        inlines: its operation is held to the predicate's own row (E125 at
        the call, E122 at a `pure` predicate), and the quantifier, which
        applies it in place, to that row (E125 at the quantifier, its
        effects counted for the function's purity check), each judgement
        one code; rule 7 does not read it, so an accepted cell's `State` or
        `Exn` operation compiles with the function's cell or tag."""
        source = _quantified(_row(outer, op), _row(pred, op),
                             f"{op.call};\n    true")
        entries = {"pure": set(), "<X>": {"X"}, "<Y>": {"Y"},
                   "<X, Y>": {"X", "Y"}}
        expected: list[tuple[str, int, int]] = []
        if not _names(pred):
            expected.append(
                ("E122", *_locate(source, "fn(@Int -> @Bool)"))
                if pred == "pure" else
                ("E125", *_locate(source, op.call)))
        if not entries[pred] <= entries[outer]:
            expected.append(("E125", *_locate(source, "forall(")))
        if outer == "pure" and entries[pred]:
            expected.append(("E122", *_locate(source, "fn f(")))
        if expected:
            assert _placed(pipeline.check(source)) == expected, source
            return
        _holds_clean(source)
        result = pipeline.compile(source).result
        assert not [d for d in result.diagnostics
                    if d.severity == "error"
                    or (d.error_code or "").startswith("E6")], (
            result.diagnostics, source)

    @pytest.mark.parametrize("cell", _CELLS, ids=lambda c: c.label)
    def test_cell(self, cell: Cell) -> None:
        source = cell.source()
        expected = cell.expected()
        if not expected:
            _holds_clean(source)
            value = cell.runs_to()
            if value is not None:
                # Accepted, so code generation builds it (rule 7's
                # negative space, and every closure the fix accepts).
                ran = pipeline.run(source, fn="f", args=[4])
                assert ran.ok and ran.value == value, (ran, source)
            return
        checked = pipeline.check(source)
        assert _placed(checked) == [
            (expected[0], *cell.refused_at(source))], (
            [(d.error_code, d.description) for d in checked.errors], source)
        if expected == ("E122",):
            assert checked.errors[0].description == cell.purity_message()
        if expected == ("E340",):
            assert checked.errors[0].description == cell.lowering_message()
