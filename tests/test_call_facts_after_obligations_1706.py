"""A call's facts are assumed only where its arguments fit the callee's parameters (#1706).

The SMT layer models a call to a user function by checking the callee's
`requires` against the arguments, then ASSUMING the callee's `ensures`, and
its refined return's predicate, about a fresh result
(`SmtContext._translate_call_with_info`).  Those facts went into the solver's
base context during the body's translation, conditioned on the path only, and
the binding-obligation walk (`_walk_for_nat_binding_obligations`) runs after
the body is translated.  So the obligation an argument owes its parameter (the
`>= 0` of an `@Int` passed to a `@Nat`, the predicate of a refined parameter,
the refinements written inside one) was discharged with the call's own
consequences among its premises: `nat_id(@Nat -> @Nat) ensures(@Nat.result ==
@Nat.0)` called as `nat_id(@Int.0)` assumed `ret == @Int.0` and `ret >= 0`,
which together are the `@Int.0 >= 0` the obligation was to establish.  The
program verified at Tier 1 and trapped at run time.

The mechanism reaches past the call's own argument.  The facts name the
argument's TERM, so they discharged any obligation over that term: a `let`
narrowing whose slot is the argument (`let @Nat = @Int.0; nat_id(@Nat.0)`),
and a constructor field inside the argument (`payload(Some(@Int.0))`, whose
field is obligated at the construction rather than at the call).  And they
came through a second door: translating a callee's `ensures` or `requires`
that matches on its parameter assumes each binder's declared-type fact about
the scrutinee, which inside the call is the argument's term, so a payload's
refinement was assumed of the argument whatever the contract said, and in a
`requires` it discharged the precondition it was part of as well.

THE RULE.  A call's facts about its result are assumed only under the facts
the callee's own proof assumed of its parameters, stated over the actual
arguments: for each parameter, `>= 0` for a `@Nat`, the refinement's
predicate, and the refinements nested inside its type.  The callee proved its
`ensures` from exactly those premises, so the guarded facts constrain the
arguments no further than the arguments' own facts do, and no obligation over
an argument can be discharged by the facts of the call it feeds.  A statically
`@Nat` argument's guard is a fact the solver holds already (a parameter, a
`@Nat` result, `@Nat.0 + 1`), so it costs nothing; it binds only where the
solver has no fact for the term, which is where the proof rested on the leak.
The facts a `match` in the callee's `requires` or `ensures` assumes are under
the same guard.  A call's result carries the refinements written inside its return
type beside its head refinement, through the disclosure gate, since a result
is the one producer of a nested-refined value the solver held no fact for.

The status move this makes is to `violated`, not to Tier 3: an unprovable
narrowing over a translatable value is an E503 (E505 for a refined parameter),
as `let @Nat = @Int.0` already is.  A program whose call-argument narrowing
was recorded verified only through the callee's postcondition now fails
`vera verify` at the call; its run is unchanged (it trapped before and traps
now).  A proof AFTER the call that used the callee's `ensures` keeps it
wherever the arguments are shown to fit, and loses it where they are not,
which is only in a program that already fails at the call.

THE INSTRUMENT.  The class spans what the formal is, what fact could re-derive
the narrowing, how the argument stands to the narrowing, and where the call
sits.  The generated matrix crosses:

* the formal: `@Nat`; `PosInt`, a refinement of `@Int`; `SmallNat`, a
  refinement of `@Nat`; `Option<PosInt>`, a refinement nested in the formal;
* the callee's facts: an `ensures` equating the result with the parameter;
  one bounding the parameter below by the result (`result <= param`); one
  bounding it above (`result >= param`, which entails nothing about the
  parameter's lower bound); a refined return of another type with an `ensures`
  relating it to the parameter (`result == param + 1`); and `ensures(true)`;
* the argument: the bare parameter; an expression over it (`@Int.0 - 1`, and
  for the nested formal the construction `Some(@Int.0 - 1)`, whose payload is
  obligated at its constructor field); the parameter under a `requires` that
  proves the narrowing; the parameter under an enclosing `if` that proves it;
* the position: the function's return expression; a `let` value; the argument
  of an outer call; an `if` condition's operand; a `match` arm.

4 x 5 x 4 x 5 = 400 cells, and 20 more crossing the argument and the position
for a callee whose `requires` matches on its `Option<PosInt>` parameter.
Every cell's expectation is the rule, stated, not
computed: an argument the program does not prove fits is `violated` with
E503 (`nat_bind`) or E505 (`refine_bind`) whatever the callee's facts, and the
run on a negative input traps with the formal's own guard text; an argument
the `requires` or the `if` proves is `verified`, and the run on a fitting
input returns.  The leaking cells (`equal`, `below`, `shifted`, bar
`SmallNat`'s `below`, whose `result <= param` bounds nothing above) were
`verified` before the fix, so they are the cells that move; the others pin
that the guard rejects nothing the program establishes.

The reported instance, each red-first pin and each mutant killer is an
unparametrised test below, which every pull request runs.
"""

from __future__ import annotations

import re
import textwrap
from dataclasses import dataclass

import pytest

from vera.reconcile import reconcile

from tests import pipeline

# A generated class instrument (tests/matrix_sample.py): a pull request runs a
# sample of the parametrised cells, and all of them when it changes this file
# or a module that decides the class: the call translation that assumes a
# callee's facts, and the walk whose argument targets the guard is built from.
pytestmark = pytest.mark.matrix(decides=["vera/smt.py", "vera/verifier.py"])


#: The name every program here is verified and compiled under, so the
#: reconciliation join can place a record and a check.
FILE = "call_facts_1706.vera"

#: The guard texts a negative argument meets.  A `@Nat` parameter (and a
#: refinement of `@Nat`, whose sign is checked at the call) is guarded at the
#: call site; a refined parameter's predicate at the callee's entry; a payload
#: refinement where the callee's pattern binds it.
NAT_TRAP = "Negative value bound into a @Nat slot"
REFINED_TRAP = "Refinement violation"

TYPES = textwrap.dedent("""\
    type PosInt = { @Int | @Int.0 > 0 };
    type SmallNat = { @Nat | @Nat.0 < 1000 };
    type Big = { @Int | @Int.0 > 1 };
    type Mid = { @Int | @Int.0 > 0 && @Int.0 < 1001 };
    """)


# =====================================================================
# Helpers
# =====================================================================


def _verify(source: str) -> pipeline.Verified:
    """Verify *source*, which must type-check cleanly."""
    verified = pipeline.verify(source, file=FILE)
    errors = verified.checked.errors
    assert not errors, (
        "fixture must type-check cleanly, got: "
        f"{[(d.error_code, d.description[:80]) for d in errors]}"
    )
    return verified


def _run(source: str, fn: str, args: list[int]) -> pipeline.Ran:
    """Compile and run *fn*; the fixture must compile."""
    ran = pipeline.run(source, fn, args, file=FILE)
    assert ran.compiled is not None and ran.compiled.ok, (
        "fixture must compile, got: "
        f"{[(d.error_code, d.description[:80]) for d in ran.compiled.errors]}"
        if ran.compiled is not None else "no compile")
    return ran


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


def _records(
    verified: pipeline.Verified, where: tuple[int, int], kind: str,
) -> list[str]:
    """``status[/code]`` of every *kind* obligation located at *where*."""
    return sorted(
        _status(o) for o in verified.obligations
        if o.kind == kind and (o.line, o.column) == where
    )


def _kinds(verified: pipeline.Verified, kind: str) -> list[str]:
    """``line:column:status[/code]`` of every *kind* obligation."""
    return sorted(
        f"{o.line}:{o.column}:{_status(o)}" for o in verified.obligations
        if o.kind == kind
    )


def _trap_text(ran: pipeline.Ran) -> str | None:
    """The trap's message, or None when the call returned."""
    return None if ran.trap is None else str(ran.trap)


# =====================================================================
# The reported instance and the shapes measured beside it
# =====================================================================

NAT_ID = textwrap.dedent("""\
    private fn nat_id(@Nat -> @Nat)
      requires(true)
      ensures(@Nat.result == @Nat.0)
      effects(pure)
    {
      @Nat.0
    }
    """)


def _caller(body: str, *, requires: str = "true",
            ensures: str = "true") -> str:
    return NAT_ID + "\n" + textwrap.dedent(f"""\
        public fn f(@Int -> @Int)
          requires({requires})
          ensures({ensures})
          effects(pure)
        {{
          {body}
        }}
        """)


ISSUE = _caller("nat_to_int(nat_id(@Int.0))")


def test_repro_issue_1706() -> None:
    """The issue's program: the argument's narrowing is refuted at the call,
    and the run still traps on the negative it was refuted for."""
    verified = _verify(ISSUE)
    site = _at(ISSUE, "@Int.0)")
    assert _records(verified, site, "nat_bind") == ["violated/E503"]
    assert not verified.ok
    assert NAT_TRAP in (_trap_text(_run(ISSUE, "f", [-1])) or "")
    assert _run(ISSUE, "f", [7]).value == 7


def test_repro_let_value() -> None:
    """The call as a `let` value: the same site, the same verdict."""
    source = _caller("let @Nat = nat_id(@Int.0);\n  nat_to_int(@Nat.0)")
    verified = _verify(source)
    assert _records(verified, _at(source, "@Int.0)"), "nat_bind") == [
        "violated/E503"]
    assert NAT_TRAP in (_trap_text(_run(source, "f", [-1])) or "")


def test_repro_two_calls_in_one_expression() -> None:
    """`nat_id(@Int.0 - 1)`'s facts entail `@Int.0 >= 1`, which discharged
    BOTH calls' narrowings; each is now refuted on its own."""
    source = _caller(
        "nat_to_int(nat_id(@Int.0)) + nat_to_int(nat_id(@Int.0 - 1))")
    verified = _verify(source)
    assert _records(verified, _at(source, "@Int.0)"), "nat_bind") == [
        "violated/E503"]
    assert _records(verified, _at(source, "@Int.0 - 1"), "nat_bind") == [
        "violated/E503"]
    assert NAT_TRAP in (_trap_text(_run(source, "f", [0])) or "")


POS_KEEP = TYPES + "\n" + textwrap.dedent("""\
    private fn keep(@PosInt -> @PosInt)
      requires(true)
      ensures(@PosInt.result == @PosInt.0)
      effects(pure)
    {
      @PosInt.0
    }

    public fn f(@Int -> @Int)
      requires(true)
      ensures(true)
      effects(pure)
    {
      keep(@Int.0)
    }
    """)


def test_repro_refined_parameter() -> None:
    """The refined twin: the predicate `keep`'s parameter places on its
    argument was discharged by `keep`'s own postcondition and refined
    return."""
    verified = _verify(POS_KEEP)
    site = _at(POS_KEEP, "@Int.0)")
    assert _records(verified, site, "refine_bind") == ["violated/E505"]
    assert REFINED_TRAP in (_trap_text(_run(POS_KEEP, "f", [-1])) or "")
    assert _run(POS_KEEP, "f", [4]).value == 4


PAYLOAD = TYPES + "\n" + textwrap.dedent("""\
    private fn payload(@Option<PosInt> -> @PosInt)
      requires(true)
      ensures(match @Option<PosInt>.0 {
        Some(@PosInt) -> @PosInt.result == @PosInt.0,
        None -> @PosInt.result == 1
      })
      effects(pure)
    {
      match @Option<PosInt>.0 {
        Some(@PosInt) -> @PosInt.0,
        None -> 1
      }
    }
    """)


def test_repro_nested_refinement() -> None:
    """A refinement written INSIDE the formal: `payload`'s `ensures` names
    the payload, so with its refined return it re-derived the payload
    refinement its own argument owed."""
    source = PAYLOAD + "\n" + textwrap.dedent("""\
        public fn f(@Option<Int> -> @Int)
          requires(true)
          ensures(true)
          effects(pure)
        {
          payload(@Option<Int>.0)
        }

        public fn g(@Int -> @Int)
          requires(true)
          ensures(true)
          effects(pure)
        {
          f(Some(@Int.0))
        }
        """)
    verified = _verify(source)
    site = _at(source, "@Option<Int>.0)")
    assert _records(verified, site, "refine_bind") == ["violated/E505"]
    assert REFINED_TRAP in (_trap_text(_run(source, "g", [-1])) or "")


def test_repro_construction_argument() -> None:
    """A construction's payload is obligated at its constructor field, not
    at the call, and the call's facts discharged it there.  The caller's
    `@Option<PosInt>` parameter is what declares the sort: without it the
    construction does not translate and no facts are assumed at all."""
    source = PAYLOAD + "\n" + textwrap.dedent("""\
        public fn h(@Option<PosInt>, @Int -> @Int)
          requires(true)
          ensures(true)
          effects(pure)
        {
          payload(Some(@Int.0))
        }
        """)
    verified = _verify(source)
    field = _at(source, "@Int.0))")
    assert _records(verified, field, "refine_bind") == ["violated/E505"]


def test_repro_let_narrowing_before_the_call() -> None:
    """A `let` narrowing of the value the call later receives: the call's
    facts discharged the `let`'s obligation as well as its own."""
    source = _caller(
        "let @Nat = @Int.0;\n  nat_to_int(nat_id(@Int.0)) + nat_to_int(@Nat.0)")
    verified = _verify(source)
    assert _records(verified, _at(source, "@Int.0;"), "nat_bind") == [
        "violated/E503"]
    assert _records(verified, _at(source, "@Int.0))"), "nat_bind") == [
        "violated/E503"]


def test_repro_let_bound_argument() -> None:
    """The argument does not narrow at the call (it is the `let`'s `@Nat`),
    but its term is the `let`'s value, so the callee's `ensures` re-derived
    the `let`'s narrowing.  The guard covers every parameter, not only the
    ones a narrowing obligates at the call."""
    source = _caller("let @Nat = @Int.0;\n  nat_to_int(nat_id(@Nat.0))")
    verified = _verify(source)
    assert _records(verified, _at(source, "@Int.0;"), "nat_bind") == [
        "violated/E503"]
    assert _records(verified, _at(source, "@Nat.0))"), "nat_bind") == []
    assert NAT_TRAP in (_trap_text(_run(source, "f", [-1])) or "")


# =====================================================================
# Negative space: what the guard must not move
# =====================================================================


def test_a_precondition_is_checked_before_the_facts() -> None:
    """A `requires` is checked against the arguments before any fact is
    assumed, so its refutation never depended on the order this fix
    changes; it stays an E501."""
    source = textwrap.dedent("""\
        private fn pos(@Int -> @Int)
          requires(@Int.0 > 0)
          ensures(@Int.result == @Int.0 && @Int.result > 0)
          effects(pure)
        {
          @Int.0
        }

        public fn f(@Int -> @Int)
          requires(true)
          ensures(true)
          effects(pure)
        {
          pos(@Int.0)
        }
        """)
    verified = _verify(source)
    assert _records(verified, _at(source, "pos(@Int.0)"), "call_pre") == [
        "violated/E501"]


def test_an_enclosing_branch_still_proves_the_narrowing() -> None:
    source = _caller(
        "if @Int.0 >= 0 then { nat_to_int(nat_id(@Int.0)) } else { 0 }")
    verified = _verify(source)
    assert _records(verified, _at(source, "@Int.0)"), "nat_bind") == [
        "verified"]
    assert verified.ok
    assert _run(source, "f", [-1]).value == 0


def test_a_nat_argument_keeps_the_callees_facts() -> None:
    """A `@Nat` parameter passed to a `@Nat` formal owes nothing at the call,
    and its guard is the `>= 0` its declaration already put in the solver,
    so the caller's own postcondition still proves from `nat_id`'s."""
    source = NAT_ID + "\n" + textwrap.dedent("""\
        public fn f(@Nat -> @Nat)
          requires(true)
          ensures(@Nat.result == @Nat.0)
          effects(pure)
        {
          nat_id(@Nat.0)
        }
        """)
    verified = _verify(source)
    assert _kinds(verified, "nat_bind") == []
    assert verified.ok
    assert all(o.status == "verified" for o in verified.obligations
               if o.kind == "ensures")


SUCC = textwrap.dedent("""\
    private fn succ(@Nat -> @Nat)
      requires(true)
      ensures(@Nat.result == @Nat.0 + 1)
      effects(pure)
    {
      @Nat.0 + 1
    }

    public fn f(@Int -> @Int)
      requires(REQ)
      ensures(@Int.result == @Int.0 + 1)
      effects(pure)
    {
      nat_to_int(succ(@Int.0))
    }
    """)


def test_a_proof_after_the_call_needs_the_arguments_to_fit() -> None:
    """`succ`'s postcondition holds of its result where its argument is a
    `@Nat`.  Shown to be one, the caller's postcondition proves from it; not
    shown, the narrowing is refuted at the call and the postcondition is
    refuted with it, as a `let @Nat = @Int.0` makes both fail today."""
    proved = SUCC.replace("REQ", "@Int.0 >= 0")
    verified = _verify(proved)
    assert verified.ok, [(d.error_code, d.description[:80])
                         for d in verified.errors]
    open_ = SUCC.replace("REQ", "true")
    verified = _verify(open_)
    assert _records(verified, _at(open_, "@Int.0))"), "nat_bind") == [
        "violated/E503"]
    assert [o.status for o in verified.obligations
            if o.kind == "ensures" and o.line == 11] == ["violated"]


def test_a_closure_argument_keeps_its_record() -> None:
    """`apply_fn` carries no `ensures` to assume, so nothing it obligates
    moves: an `@Int` into a `@Nat` closure formal is refuted as before."""
    source = textwrap.dedent("""\
        type NatToInt = fn(Nat -> Int) effects(pure);

        private fn apply(@NatToInt, @Int -> @Int)
          requires(true)
          ensures(true)
          effects(pure)
        {
          apply_fn(@NatToInt.0, @Int.0)
        }
        """)
    verified = _verify(source)
    assert _records(verified, _at(source, "@Int.0)"), "nat_bind") == [
        "violated/E503"]


def test_an_effect_operation_argument_keeps_its_record() -> None:
    """A `State<Nat>` write takes the same refutation it took before."""
    source = textwrap.dedent("""\
        public fn f(@Int -> @Unit)
          requires(true)
          ensures(true)
          effects(<State<Nat>>)
        {
          put(@Int.0)
        }
        """)
    verified = _verify(source)
    assert _records(verified, _at(source, "@Int.0)"), "nat_bind") == [
        "violated/E503"]


def test_a_constructor_field_keeps_its_record() -> None:
    source = textwrap.dedent("""\
        private data Box {
          MkBox(Nat)
        }

        public fn f(@Int -> @Int)
          requires(true)
          ensures(true)
          effects(pure)
        {
          let @Box = MkBox(@Int.0);
          0
        }
        """)
    verified = _verify(source)
    assert _records(verified, _at(source, "@Int.0)"), "nat_bind") == [
        "violated/E503"]


@pytest.mark.parametrize(("source", "needle", "kind"), [
    pytest.param(ISSUE, "@Int.0)", "nat_bind", id="nat"),
    pytest.param(POS_KEEP, "@Int.0)", "refine_bind", id="refined"),
])
def test_the_moved_record_still_joins_its_check(
    source: str, needle: str, kind: str,
) -> None:
    """Issue #1695's join: the record that moves from `verified` to
    `violated` sits where codegen emits its check, and the reconciliation
    reports no claim without a check (E541) and no check without a record
    (W004) at that site."""
    verified = pipeline.verify(source, file=FILE)
    compiled = pipeline.compile(source, file=FILE)
    site = _at(source, needle)
    assert _records(verified, site, kind) and all(
        r.startswith("violated") for r in _records(verified, site, kind))
    mismatches = reconcile(
        verified.result, compiled.result,
        program=verified.checked.program, file=verified.checked.file)
    assert [(m.kind, m.obligation) for m in mismatches
            if (m.line, m.column) == site] == []


# =====================================================================
# Mutant killers: one per mechanism the guard adds
# =====================================================================


def test_kills_an_unguarded_refined_return() -> None:
    """The refined return's predicate is guarded with the `ensures`.  Over a
    fresh result alone it can only leak when it is unsatisfiable, and then it
    leaks everything: `NoInt`'s empty predicate made the context inconsistent, and
    the argument's narrowing discharged vacuously."""
    source = textwrap.dedent("""\
        type NoInt = { @Int | @Int.0 > 0 && @Int.0 < 0 };

        private fn never(@Nat -> @NoInt)
          requires(true)
          ensures(true)
          effects(pure)
        {
          1
        }

        public fn f(@Int -> @Int)
          requires(true)
          ensures(true)
          effects(pure)
        {
          never(@Int.0)
        }
        """)
    verified = _verify(source)
    assert _records(verified, _at(source, "@Int.0)"), "nat_bind") == [
        "violated/E503"]


def test_kills_a_guard_of_the_first_argument_only() -> None:
    """Every argument's facts are in the guard: here the first argument's is
    proved by the `requires`, so a guard holding it alone would hold, and
    `pick`'s `ensures` would re-derive the second's."""
    source = textwrap.dedent("""\
        private fn pick(@Nat, @Nat -> @Nat)
          requires(true)
          ensures(@Nat.result == @Nat.0)
          effects(pure)
        {
          @Nat.0
        }

        public fn f(@Int, @Int -> @Int)
          requires(@Int.1 >= 0)
          ensures(true)
          effects(pure)
        {
          nat_to_int(pick(@Int.1, @Int.0))
        }
        """)
    verified = _verify(source)
    assert _records(verified, _at(source, "@Int.1,"), "nat_bind") == [
        "verified"]
    assert _records(verified, _at(source, "@Int.0)"), "nat_bind") == [
        "violated/E503"]


def test_kills_an_unguarded_match_arm_fact() -> None:
    """The second door: an `ensures` whose content entails nothing about the
    payload (`result >= payload`) but that `match`es on the parameter.  The
    match's translation assumes each binder's declared-type fact about its
    scrutinee, which inside the call is the argument's term, so the payload's
    `> 0` was assumed of the argument; it is now assumed under the binding."""
    source = TYPES + "\n" + textwrap.dedent("""\
        private fn payload(@Option<PosInt> -> @PosInt)
          requires(true)
          ensures(match @Option<PosInt>.0 {
            Some(@PosInt) -> @PosInt.result >= @PosInt.0,
            None -> @PosInt.result == 1
          })
          effects(pure)
        {
          match @Option<PosInt>.0 {
            Some(@PosInt) -> @PosInt.0,
            None -> 1
          }
        }

        public fn f(@Option<Int> -> @Int)
          requires(true)
          ensures(true)
          effects(pure)
        {
          payload(@Option<Int>.0)
        }
        """)
    verified = _verify(source)
    assert _records(verified, _at(source, "@Option<Int>.0)"),
                    "refine_bind") == ["violated/E505"]


def test_kills_an_unguarded_requires_match_arm_fact() -> None:
    """The same door in the callee's `requires`: translated before the
    binding was held, its `match` assumed the payload's `> 0` about the
    argument outright, which discharged both the argument's refinement and
    the precondition itself, and `g(-1)` trapped in a verified program."""
    source = TYPES + "\n" + REQUIRES_MATCH_CALLEE.replace(
        "callee", "peek") + "\n" + textwrap.dedent("""\
        public fn f(@Option<Int> -> @Int)
          requires(true)
          ensures(true)
          effects(pure)
        {
          peek(@Option<Int>.0)
        }

        public fn g(@Int -> @Int)
          requires(true)
          ensures(true)
          effects(pure)
        {
          f(Some(@Int.0))
        }
        """)
    verified = _verify(source)
    call = _at(source, "peek(@Option<Int>.0)")
    assert _records(verified, (call[0], call[1] + len("peek(")),
                    "refine_bind") == ["violated/E505"]
    assert _records(verified, call, "call_pre") == ["violated/E501"]
    assert REFINED_TRAP in (_trap_text(_run(source, "g", [-1])) or "")


def test_kills_a_misaligned_zero_size_argument() -> None:
    """A zero-size parameter has no term (#1214), so the guard pairs each
    remaining term with its own argument: here the `@Nat`'s fact is over
    `@Int.0`, not shifted onto the `@Unit` before it."""
    source = textwrap.dedent("""\
        private fn second(@Unit, @Nat -> @Nat)
          requires(true)
          ensures(@Nat.result == @Nat.0)
          effects(pure)
        {
          @Nat.0
        }

        public fn f(@Int -> @Int)
          requires(true)
          ensures(true)
          effects(pure)
        {
          nat_to_int(second((), @Int.0))
        }
        """)
    verified = _verify(source)
    assert _records(verified, _at(source, "@Int.0)"), "nat_bind") == [
        "violated/E503"]
    assert NAT_TRAP in (_trap_text(_run(source, "f", [-1])) or "")


def test_kills_a_result_without_its_nested_facts() -> None:
    """A call's result carries the refinements inside its return type, as it
    carries its head refinement: `mk`'s return slot established the payload,
    so the guard over `consume`'s argument holds and `f`'s postcondition still
    proves from `consume`'s.  Without the result's facts the solver held none
    for the term, and a sound Tier 1 became an E500."""
    source = TYPES + "\n" + textwrap.dedent("""\
        private fn mk(@Int -> @Option<PosInt>)
          requires(true)
          ensures(true)
          effects(pure)
        {
          Some(7)
        }

        private fn consume(@Option<PosInt> -> @Int)
          requires(true)
          ensures(@Int.result > 0)
          effects(pure)
        {
          match @Option<PosInt>.0 {
            Some(@PosInt) -> @PosInt.0,
            None -> 41
          }
        }

        public fn f(@Int -> @Int)
          requires(true)
          ensures(@Int.result > 0)
          effects(pure)
        {
          consume(mk(@Int.0))
        }
        """)
    verified = _verify(source)
    assert verified.ok, [(d.error_code, d.description[:80])
                         for d in verified.errors]
    assert _records(verified, _at(source, "mk(@Int.0)"), "refine_bind") == [
        "verified"]
    assert [o.status for o in verified.obligations
            if o.kind == "ensures" and o.line == _at(source, "@Int.result > 0", 1)[0]
            ] == ["verified"]
    assert _run(source, "f", [3]).value == 7


def test_kills_a_guard_dropped_under_a_path_condition() -> None:
    """The guard composes with the branch's path condition rather than
    standing in for it: a call inside a branch whose condition proves
    nothing about the argument is refuted as one at the top level is."""
    source = textwrap.dedent("""\
        private fn nat_id(@Nat -> @Nat)
          requires(true)
          ensures(@Nat.result == @Nat.0)
          effects(pure)
        {
          @Nat.0
        }

        public fn f(@Bool, @Int -> @Int)
          requires(true)
          ensures(true)
          effects(pure)
        {
          if @Bool.0 then { nat_to_int(nat_id(@Int.0)) } else { 0 }
        }
        """)
    verified = _verify(source)
    assert _records(verified, _at(source, "@Int.0)"), "nat_bind") == [
        "violated/E503"]


# =====================================================================
# The class instrument
# =====================================================================


@dataclass(frozen=True)
class Formal:
    """The parameter the call's argument binds into."""

    name: str
    #: The formal's type, as the callee's parameter is written.
    ty: str
    #: The caller's own parameter, which the argument is built from.
    source: str
    #: The record the argument's obligation is, and its refutation's code.
    kind: str
    code: str
    #: The predicate over the caller's parameter that proves the narrowing.
    proof: str
    #: The text a negative argument's run traps with.
    trap: str
    #: The refined return the `shifted` fact uses, and how far it shifts.
    shifted_ret: str


FORMALS = (
    Formal("nat", "Nat", "@Int.0", "nat_bind", "E503",
           "@Int.0 >= 0", NAT_TRAP, "PosInt"),
    Formal("pos", "PosInt", "@Int.0", "refine_bind", "E505",
           "@Int.0 > 0", REFINED_TRAP, "Big"),
    Formal("small", "SmallNat", "@Int.0", "refine_bind", "E505",
           "@Int.0 >= 0 && @Int.0 < 1000", NAT_TRAP, "Mid"),
    Formal("nested", "Option<PosInt>", "@Option<Int>.0", "refine_bind",
           "E505",
           "match @Option<Int>.0 { Some(@Int) -> @Int.0 > 0, None -> true }",
           REFINED_TRAP, "Big"),
)

#: The callee's facts.  `True` where they re-derive the narrowing, which is
#: where the cell was `verified` before the fix.
FACTS = ("equal", "below", "above", "shifted", "true")
ARGUMENTS = ("bare", "expr", "requires", "guarded")
POSITIONS = ("return", "let", "outer", "cond", "arm")

_TO_INT = {"Nat": "nat_to_int({})", "SmallNat": "nat_to_int({})"}
_BASE = {"Nat": "Nat", "SmallNat": "Nat", "PosInt": "Int", "Big": "Int",
         "Mid": "Int", "Int": "Int"}


#: A callee whose `requires` matches on its `Option<PosInt>` parameter: the
#: match assumes the binder's `> 0` about the scrutinee as it translates, which
#: inside the call is the argument's term (R77's finding on PR #1715).
REQUIRES_MATCH_CALLEE = textwrap.dedent("""\
    private fn callee(@Option<PosInt> -> @Int)
      requires(match @Option<PosInt>.0 {
        Some(@PosInt) -> @PosInt.0 > 0,
        None -> true
      })
      ensures(true)
      effects(pure)
    {
      0
    }
    """)


def _callee(formal: Formal, fact: str) -> tuple[str, str]:
    """The callee's declaration and its return type."""
    if fact == "requires_match":
        return REQUIRES_MATCH_CALLEE, "Int"
    ret = formal.shifted_ret if fact == "shifted" else (
        "PosInt" if formal.name == "nested" else formal.ty)
    if formal.name == "nested":
        relation = {
            "equal": "@PosInt.result == @PosInt.0",
            "below": "@PosInt.result <= @PosInt.0",
            "above": "@PosInt.result >= @PosInt.0",
            "shifted": "@Big.result == @PosInt.0 + 1",
        }
        none_value = "2" if fact == "shifted" else "1"
        some_value = "@PosInt.0 + 1" if fact == "shifted" else "@PosInt.0"
        ensures = "true" if fact == "true" else (
            "match @Option<PosInt>.0 {\n"
            f"    Some(@PosInt) -> {relation[fact]},\n"
            f"    None -> @{ret}.result == {none_value}\n"
            "  }")
        body = ("match @Option<PosInt>.0 {\n"
                f"    Some(@PosInt) -> {some_value},\n"
                f"    None -> {none_value}\n"
                "  }")
    else:
        param = f"@{formal.ty}.0"
        relation = {
            "equal": f"@{ret}.result == {param}",
            "below": f"@{ret}.result <= {param}",
            "above": f"@{ret}.result >= {param}",
            "shifted": f"@{ret}.result == {param} + 1",
        }
        ensures = "true" if fact == "true" else relation[fact]
        body = f"{param} + 1" if fact == "shifted" else param
    decl = (f"private fn callee(@{formal.ty} -> @{ret})\n"
            "  requires(true)\n"
            f"  ensures({ensures})\n"
            "  effects(pure)\n"
            "{\n"
            f"  {body}\n"
            "}\n")
    return decl, ret


def _program(formal: Formal, fact: str, argument: str, position: str,
             ) -> tuple[str, str, str]:
    """The cell's program, the argument's text and the function to run."""
    decl, ret = _callee(formal, fact)
    if argument == "expr":
        arg = ("Some(@Int.0 - 1)" if formal.name == "nested"
               else "@Int.0 - 1")
    else:
        arg = formal.source
    call = f"callee({arg})"
    to_int = _TO_INT.get(ret, "{}")
    caller_ret = "Int"
    if position == "return":
        expr = call
        caller_ret = _BASE[ret]
    elif position == "let":
        expr = f"let @{ret} = {call};\n  {to_int.format(f'@{ret}.0')}"
    elif position == "outer":
        expr = f"sink({call})"
    elif position == "cond":
        expr = f"if {to_int.format(call)} > 5 then {{ 1 }} else {{ 0 }}"
    else:
        expr = (f"match @Bool.0 {{\n    true -> {to_int.format(call)},\n"
                "    false -> 0\n  }")
    default = "0"
    if argument == "guarded":
        expr = f"if {formal.proof} then {{\n  {expr}\n  }} else {{ {default} }}"
    requires = formal.proof if argument == "requires" else "true"
    source_ty = "Option<Int>, @Int" if formal.name == "nested" else "Int"
    sink = (f"private fn sink(@{ret} -> @Int)\n"
            "  requires(true)\n  ensures(true)\n  effects(pure)\n{\n  0\n}\n")
    caller = (f"public fn f(@Bool, @{source_ty} -> @{caller_ret})\n"
              f"  requires({requires})\n"
              "  ensures(true)\n"
              "  effects(pure)\n"
              "{\n"
              f"  {expr}\n"
              "}\n")
    parts = [TYPES, decl, sink, caller]
    fn = "f"
    if formal.name == "nested":
        # The payload reaches `f` as an `Option<Int>` built here, and as the
        # `@Int` the `expr` argument constructs from; a `requires` on `f` is
        # established for `run`'s callers by the same bound on its `@Int`.
        run_requires = "@Int.0 > 0" if argument == "requires" else "true"
        parts.append(
            f"public fn run(@Bool, @Int -> @{caller_ret})\n"
            f"  requires({run_requires})\n  ensures(true)\n  effects(pure)\n"
            "{\n  f(@Bool.0, Some(@Int.0), @Int.0)\n}\n")
        fn = "run"
    return "\n".join(parts), arg, fn


CELLS = [
    pytest.param(formal, fact, argument, position,
                 id=f"{formal.name}-{fact}-{argument}-{position}")
    for formal in FORMALS
    for fact in FACTS
    for argument in ARGUMENTS
    for position in POSITIONS
]


@pytest.mark.parametrize(("formal", "fact", "argument", "position"), CELLS)
def test_call_facts_never_discharge_their_arguments(
    formal: Formal, fact: str, argument: str, position: str,
) -> None:
    """The rule, per cell: an argument the program does not prove fits its
    parameter is refuted at the call whatever the callee's facts say, and its
    negative traps; one the program proves fits is verified, and runs."""
    source, arg, fn = _program(formal, fact, argument, position)
    verified = _verify(source)
    site = _at(source, f"callee({arg})")
    # The value obligated: the argument, or a construction's payload, which
    # is obligated at its constructor field rather than at the call.
    offset = len("callee(Some(") if arg.startswith("Some(") else len("callee(")
    site = (site[0], site[1] + offset)
    proved = argument in ("requires", "guarded")
    expected = "verified" if proved else f"violated/{formal.code}"
    assert _records(verified, site, formal.kind) == [expected], (
        _kinds(verified, formal.kind))
    if proved:
        assert verified.ok, [(d.error_code, d.description[:80])
                             for d in verified.errors]
        ran = _run(source, fn, [1, 5])
        assert ran.trap is None, _trap_text(ran)
    else:
        ran = _run(source, fn, [1, -1])
        assert formal.trap in (_trap_text(ran) or ""), _trap_text(ran)


REQUIRES_CELLS = [
    pytest.param(argument, position, id=f"requires-{argument}-{position}")
    for argument in ARGUMENTS
    for position in POSITIONS
]


@pytest.mark.parametrize(("argument", "position"), REQUIRES_CELLS)
def test_a_requires_match_never_discharges_its_argument(
    argument: str, position: str,
) -> None:
    """The callee's `requires` is translated under the call's binding as its
    `ensures` is: a `match` there assumes nothing about the argument, so an
    argument the program does not prove fits is refuted twice over (its
    payload, E505, and the precondition the payload decides, E501) and its
    negative traps; one it proves verifies with no record at the call."""
    nested = next(f for f in FORMALS if f.name == "nested")
    source, arg, fn = _program(nested, "requires_match", argument, position)
    verified = _verify(source)
    call = _at(source, f"callee({arg})")
    offset = len("callee(Some(") if arg.startswith("Some(") else len("callee(")
    value = (call[0], call[1] + offset)
    if argument in ("requires", "guarded"):
        assert _records(verified, value, "refine_bind") == ["verified"]
        assert _records(verified, call, "call_pre") == []
        assert verified.ok, [(d.error_code, d.description[:80])
                             for d in verified.errors]
        ran = _run(source, fn, [1, 5])
        assert ran.trap is None, _trap_text(ran)
    else:
        assert _records(verified, value, "refine_bind") == ["violated/E505"]
        assert _records(verified, call, "call_pre") == ["violated/E501"]
        ran = _run(source, fn, [1, -1])
        assert REFINED_TRAP in (_trap_text(ran) or ""), _trap_text(ran)


def test_the_matrix_is_the_product() -> None:
    """Every product is a cell, and every cell id names one product."""
    ids = [c.id for c in CELLS]
    assert len(ids) == len(set(ids)) == (
        len(FORMALS) * len(FACTS) * len(ARGUMENTS) * len(POSITIONS)) == 400
    assert all(re.fullmatch(r"[a-z]+-[a-z]+-[a-z]+-[a-z]+", i) for i in ids)
    requires = [c.id for c in REQUIRES_CELLS]
    assert len(requires) == len(set(requires)) == (
        len(ARGUMENTS) * len(POSITIONS)) == 20
