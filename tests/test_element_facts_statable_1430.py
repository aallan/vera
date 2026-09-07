"""#1430 — the nested-refinement goal is STATABLE for carriers the structural
walk cannot decompose.

#1410 removed a type-comparison shortcut that answered ``verified`` whenever an
argument's declared type already carried the refinements its target asked for.
The shortcut was wrong — a ``verified`` must come from a discharged obligation
— but removing it exposed a completeness gap it had been hiding: for a carrier
with no constructor decomposition the goal cannot be stated at all, so the
obligation discloses ``tier3_unguarded``/E506 instead of reporting a tier.

Stage 1 closes that for ``Array<Refined>`` with the bounded quantifier

    forall i. 0 <= i < length(a)  =>  P(index(a, i))

which the existing encoding already has the pieces for: an uninterpreted
``Array_<elt>`` carrier sort, an uninterpreted ``index_`` and ``length_``.
``arr[i]`` translates to the SAME ``index_`` symbol, so the fact reaches
ordinary programs rather than only literals.

Every cell pins the exact multiset of ``refine_bind`` statuses rather than the
absence of one.  The behaviour being replaced is a DECLINE, so "no longer
unguarded" is satisfied by the obligation disappearing altogether, by a
wrongly-``verified`` answer, and by the correct one alike; only the full
multiset separates them.  The refuting cells use an element (``-2``) whose
honest verdict is a refutation, which no decline-as-default can imitate.
"""

from __future__ import annotations

import json
import os
import subprocess
import sys
from collections import Counter
from pathlib import Path

import pytest

import vera

_PKG_PARENT = str(Path(vera.__file__).resolve().parents[1])

_HDR = "type PosInt = { @Int | @Int.0 > 0 };\n\n"
_CONSUME = (
    "private fn consume(@Array<PosInt> -> @Int)\n"
    "  requires(true)\n  ensures(true)\n  effects(pure)\n"
    "{\n  array_length(@Array<PosInt>.0)\n}\n\n"
)


def _caller(body: str, sig: str = "@Unit") -> str:
    return (
        f"public fn go({sig} -> @Int)\n"
        "  requires(true)\n  ensures(true)\n  effects(pure)\n"
        f"{{\n  {body}\n}}\n"
    )


#: Each program's ONLY difference is the source of the array, so a status that
#: moves between them is attributable to the source and nothing else.
_PROGRAMS = {
    # Forwarding a declared-refined parameter: R1 param-assume supplies the
    # element fact, and the goal is the same formula, so it discharges.
    "forwarded-parameter": _HDR + _CONSUME + _caller(
        "consume(@Array<PosInt>.0)", "@Array<PosInt>"),
    # A literal whose every element satisfies the refinement.  `length == 3`
    # bounds the quantifier, so the instantiation is finite and decidable.
    "good-literal": _HDR + _CONSUME + _caller("consume([1, 2, 3])"),
    # The empty literal: `length == 0` makes the goal vacuously true.  A
    # decline cannot produce this answer, and neither can an implementation
    # that forgot the bound.
    "empty-literal": _HDR + _CONSUME + _caller("consume([])"),
}


def _cli(*args: str, timeout: int = 120) -> subprocess.CompletedProcess[str]:
    env = dict(os.environ)
    existing = env.get("PYTHONPATH", "")
    env["PYTHONPATH"] = (
        f"{_PKG_PARENT}{os.pathsep}{existing}" if existing else _PKG_PARENT
    )
    return subprocess.run(
        [sys.executable, "-m", "vera.cli", *args],
        capture_output=True, text=True, encoding="utf-8", check=False,
        env=env, timeout=timeout,
    )


def _verify(tmp_path: Path, source: str, name: str) -> dict:
    p = tmp_path / f"{name}.vera"
    p.write_text(source, encoding="utf-8")
    proc = _cli("verify", "--json", str(p))
    return json.loads(proc.stdout)


def _refine_bind_statuses(envelope: dict) -> Counter:
    return Counter(
        o["status"] for o in envelope.get("obligations", [])
        if o["kind"] == "refine_bind"
    )


#: The EXACT `refine_bind` multiset each shape must produce.  An exact
#: multiset, not "no unguarded and at least one verified": that weaker form
#: survives dropping either half of the quantifier's range, because the
#: obligation merely demotes to a GUARDED Tier 3 which neither clause
#: inspects.  Mutation testing found precisely that hole.
_EXPECTED = {
    "empty-literal": {"verified": 1},
    "forwarded-parameter": {"verified": 2},
    "good-literal": {"verified": 4},
}


@pytest.mark.parametrize("shape", sorted(_PROGRAMS))
def test_the_array_element_goal_is_stated_and_discharged(
    shape: str, tmp_path: Path,
) -> None:
    """Every `refine_bind` over an `Array<PosInt>` whose elements are known to
    satisfy the refinement reports `verified` — none discloses, none demotes.
    """
    envelope = _verify(tmp_path, _PROGRAMS[shape], shape)
    statuses = _refine_bind_statuses(envelope)
    assert envelope["ok"] is True, envelope["diagnostics"]
    assert dict(statuses) == _EXPECTED[shape], statuses


def test_a_refuting_element_is_refuted_not_disclosed(tmp_path: Path) -> None:
    """`consume([1, -2, 3])` must REFUTE the element goal.

    This is the value chosen so that no decline-as-default can imitate the
    right answer: the honest verdict is a refutation, which "cannot state
    this" never produces.  The carrier obligation is the one under test —
    array literals already obligate each element separately, and one of those
    already refutes on the tip — so the cell asserts that NOTHING discloses,
    which is what changes here.
    """
    source = _HDR + _CONSUME + _caller("consume([1, 0 - 2, 3])")
    envelope = _verify(tmp_path, source, "bad-literal")
    statuses = _refine_bind_statuses(envelope)
    assert envelope["ok"] is False, envelope
    assert statuses["violated"] >= 1, statuses
    assert statuses["tier3_unguarded"] == 0, statuses


def test_the_partition_identity_holds_over_every_shape(
    tmp_path: Path,
) -> None:
    """`len(obligations) == total + violated + tier3_unguarded`, on each shape.

    The change moves records between buckets, and the bucket arithmetic is
    exactly what a miscounted move would break — a record counted in a tier
    AND left in the array, or dropped from both.
    """
    for shape, source in sorted(_PROGRAMS.items()):
        envelope = _verify(tmp_path, source, f"identity-{shape}")
        obligations = envelope.get("obligations", [])
        summary = envelope["verification"]
        extra = sum(
            1 for o in obligations
            if o["status"] in ("violated", "tier3_unguarded")
        )
        assert len(obligations) == summary["total"] + extra, (shape, summary)


def test_a_non_empty_array_with_a_refutable_element_is_not_vacuously_proved(
    tmp_path: Path,
) -> None:
    """Distinguishes "proved because every element satisfies P" from "proved
    because the range was empty" (PR #1447 design review, concern 8).

    `forall i. 0 <= i < length(a) => P(index(a, i))` is vacuously true in any
    model where `length(a) <= 0`.  Before the non-negativity axiom moved to
    the symbol, a function that never called `array_length` left `length`
    unconstrained, so a model could pick a negative length and satisfy the
    fact by supplying nothing — and a green cell could not be told from a real
    proof.  Here the array is known NON-EMPTY and one element refutes, so a
    vacuous answer and the correct one differ: the correct answer is a
    refutation.
    """
    source = _HDR + _CONSUME + _caller("consume([4, 0 - 9, 6])")
    envelope = _verify(tmp_path, source, "non-empty-refuting")
    statuses = _refine_bind_statuses(envelope)
    assert envelope["ok"] is False, envelope
    assert statuses["violated"] >= 1, statuses
    assert statuses["tier3_unguarded"] == 0, statuses


def test_the_length_symbol_carries_its_own_non_negativity() -> None:
    """...and it is asserted at the symbol, surviving a reset.

    `reset()` drops base-context assertions and RE-SEEDS `_length_fns` rather
    than clearing it, so an assertion made only on the mint path would be
    skipped for the re-seeded entry and warm/cold would diverge.  Asserted
    directly, both before and after a reset, because the failure is silent:
    the axiom's absence shows up as a vacuous proof, never as an error.
    """
    import z3

    from vera.smt import SmtContext

    ctx = SmtContext()

    def negative_length_is_unsat(label: str) -> None:
        arr_sort = ctx._get_array_sort(z3.IntSort())
        length_fn = ctx._get_length_fn(arr_sort)
        probe = z3.Const(f"probe_{label}", arr_sort)
        ctx.solver.push()
        ctx.solver.add(length_fn(probe) < 0)
        verdict = ctx.solver.check()
        ctx.solver.pop()
        assert verdict == z3.unsat, (
            f"{label}: a negative length is satisfiable, so the element "
            "quantifier can be vacuous"
        )

    # Cold: the axiom is asserted when the symbol is first requested.
    negative_length_is_unsat("cold")
    # The reset must be exercised AFTER a mint, or the tracking set is empty
    # and clearing it is a no-op the cell cannot see — which is exactly how a
    # first version of this cell passed against a reset that cleared nothing.
    ctx.reset()
    negative_length_is_unsat("after-reset")


def test_an_element_quantifier_does_not_leak_into_a_later_obligation(
    tmp_path: Path,
) -> None:
    """The quantifier is scoped to the query that needs it (concern 6).

    Axioms added at TRANSLATION time land in the solver's base context,
    outside `_check_refutation`'s push/pop, so one obligation's quantifier
    would be present for every later obligation in the same function — and the
    corpus cannot witness that, because no corpus program pairs an
    `Array<Refined>` obligation with anything else.  This function has the
    element obligation FIRST and an unrelated arithmetic postcondition after
    it; the second must still verify.
    """
    source = (
        _HDR + _CONSUME +
        "public fn go(@Array<PosInt>, @Int -> @Int)\n"
        "  requires(@Int.0 > 10)\n"
        "  ensures(@Int.result > 10)\n"
        "  effects(pure)\n"
        "{\n"
        "  let @Int = consume(@Array<PosInt>.0);\n"
        "  @Int.1\n"
        "}\n"
    )
    envelope = _verify(tmp_path, source, "no-leak")
    assert envelope["ok"] is True, envelope["diagnostics"]
    statuses = Counter(
        o["status"] for o in envelope.get("obligations", [])
    )
    assert statuses["tier3"] == 0, statuses
    assert statuses["timeout"] == 0, statuses
    ensures = [
        o["status"] for o in envelope["obligations"] if o["kind"] == "ensures"
    ]
    assert all(s == "verified" for s in ensures), ensures


def test_a_true_postcondition_over_an_element_is_no_longer_refused(
    tmp_path: Path,
) -> None:
    """Regression for #1449, found while measuring this change.

    `head_is_positive` is TRUE: every element is `PosInt` and the precondition
    puts index 0 in range.  On the pristine base the verifier reported
    `ensures: violated` with `[E500]` and exited 1 — a refutation, not a
    disclosure — because no element fact existed to discharge it, so the
    solver was free to answer `@Int.result = 0` over an unconstrained
    `Array_Int!val!0`.  A user was told a true contract was false and handed a
    counterexample that describes the absence of a constraint rather than a
    program.

    Asserted on the exact status, not on `ok`: an implementation that demoted
    the postcondition to Tier 3 would also stop failing, and that is a
    different (and lesser) outcome from proving it.
    """
    source = (
        _HDR +
        "public fn head_is_positive(@Array<PosInt> -> @Int)\n"
        "  requires(array_length(@Array<PosInt>.0) > 0)\n"
        "  ensures(@Int.result > 0)\n"
        "  effects(pure)\n"
        "{\n  @Array<PosInt>.0[0]\n}\n"
    )
    envelope = _verify(tmp_path, source, "true-postcondition")
    assert envelope["ok"] is True, envelope["diagnostics"]
    ensures = [
        o["status"] for o in envelope["obligations"] if o["kind"] == "ensures"
    ]
    assert ensures == ["verified"], ensures


def test_a_bad_array_cannot_be_laundered_through_a_refined_return(
    tmp_path: Path,
) -> None:
    """The assumption is closed by an obligation at every producer.

    Assuming a parameter's element fact is sound only while every producer of
    such a value is obligated to discharge it.  The shape that would break it
    is a function whose DECLARED return type carries the refinement while its
    body builds a violating value — the #1420 F4 error in carrier form.  The
    construction must be refused inside the producer, which is where the
    obligation belongs; the call site then legitimately verifies against the
    declared return, and that is the modular structure rather than a hole.
    """
    source = (
        _HDR +
        "private fn assume_positive(@Array<PosInt> -> @Int)\n"
        "  requires(array_length(@Array<PosInt>.0) > 0)\n"
        "  ensures(@Int.result > 0)\n"
        "  effects(pure)\n"
        "{\n  @Array<PosInt>.0[0]\n}\n\n"
        "private fn launder(@Int -> @Array<PosInt>)\n"
        "  requires(true)\n  ensures(true)\n  effects(pure)\n"
        "{\n  [0 - 5]\n}\n\n"
        "public fn main(@Int -> @Int)\n"
        "  requires(true)\n  ensures(true)\n  effects(pure)\n"
        "{\n  assume_positive(launder(1))\n}\n"
    )
    envelope = _verify(tmp_path, source, "laundry")
    assert envelope["ok"] is False, envelope
    codes = {d.get("error_code") for d in envelope["diagnostics"]}
    assert "E505" in codes, codes
    violated = [
        o for o in envelope["obligations"]
        if o["kind"] == "refine_bind" and o["status"] == "violated"
    ]
    assert violated, envelope["obligations"]
    # Refused where the value is BUILT, not merely at the call.
    assert any("5" in o["description"] for o in violated), violated


def test_the_assumed_element_fact_does_not_prove_a_false_postcondition(
    tmp_path: Path,
) -> None:
    """The assumptions must stay CONSISTENT — the sharpest cell here.

    Every other cell in this file survived a mutation that replaced the
    element predicate with `False`, and the reason is instructive.  Where the
    goal and the source fact are the same formula over the same term, the
    query is `F => F` and discharges by identity whatever `F` says; and where
    the fact is ASSUMED, an over-strong `F` makes the premise set
    contradictory, so every postcondition in that function proves — a false
    Tier 1 that looks exactly like a real one.

    A deliberately FALSE postcondition is what separates them.  `result < 0`
    cannot be proved from any consistent set of facts about an array of
    positive elements, so this cell fails the moment the assumptions become
    inconsistent, and it cannot be satisfied by identity discharge because
    nothing states it.
    """
    source = (
        _HDR +
        "public fn head_is_negative(@Array<PosInt> -> @Int)\n"
        "  requires(array_length(@Array<PosInt>.0) > 0)\n"
        "  ensures(@Int.result < 0)\n"
        "  effects(pure)\n"
        "{\n  @Array<PosInt>.0[0]\n}\n"
    )
    envelope = _verify(tmp_path, source, "false-postcondition")
    ensures = [
        o["status"] for o in envelope["obligations"] if o["kind"] == "ensures"
    ]
    assert ensures and all(s != "verified" for s in ensures), (
        "a false postcondition was proved — the assumed element fact has made "
        f"the premises inconsistent: {ensures}"
    )
    assert envelope["ok"] is False, envelope


def test_the_element_fact_is_used_not_merely_matched(tmp_path: Path) -> None:
    """The quantifier's CONTENT has to do the work somewhere.

    `head_is_positive` proves only if the assumed fact actually says the
    elements are positive: the goal `@Int.result > 0` is a different formula
    from the assumption, over a different term (`index(a, 0)` against a
    quantified `index(a, i)`), so no identity discharge is available and the
    solver has to instantiate.  Paired with the consistency cell above, this
    pins both halves — that the fact means something, and that it does not
    mean too much.
    """
    positive = (
        _HDR +
        "public fn head_is_positive(@Array<PosInt> -> @Int)\n"
        "  requires(array_length(@Array<PosInt>.0) > 0)\n"
        "  ensures(@Int.result > 0)\n"
        "  effects(pure)\n"
        "{\n  @Array<PosInt>.0[0]\n}\n"
    )
    envelope = _verify(tmp_path, positive, "content-used")
    ensures = [
        o["status"] for o in envelope["obligations"] if o["kind"] == "ensures"
    ]
    assert ensures == ["verified"], ensures


# --------------------------------------------------------------------------
# Stage 2 — recursive constructor fields
# --------------------------------------------------------------------------

_CHAIN = (
    "private data Chain {\n  Link(PosInt, Chain),\n  End\n}\n\n"
    "private fn consume(@Chain -> @Int)\n"
    "  requires(true)\n  ensures(true)\n  effects(pure)\n"
    "{\n  match @Chain.0 {\n    Link(@PosInt, @Chain) -> @PosInt.0,\n"
    "    End -> 1\n  }\n}\n\n"
)


def test_a_recursive_tail_forwards_per_value(tmp_path: Path) -> None:
    """The shape a real recursive program has, where the argument is the TAIL.

    `match c { Link(@PosInt, @Chain) -> consume(@Chain.0) }` passes a
    DIFFERENT term from the matched value, so no identity discharge is
    available: `refines_K(Link_1(c))` has to be derived.  Param-assume
    supplies `refines_K(c)`, the match supplies `is_Link(c)`, and the single
    unfolding axiom relates them.  That is the whole of stage 2 — one level of
    structure per value, no induction.
    """
    source = (
        _HDR + _CHAIN +
        "public fn walk(@Chain -> @Int)\n"
        "  requires(true)\n  ensures(true)\n  effects(pure)\n"
        "{\n  match @Chain.0 {\n"
        "    Link(@PosInt, @Chain) -> consume(@Chain.0),\n"
        "    End -> 0\n  }\n}\n"
    )
    envelope = _verify(tmp_path, source, "recursive-tail")
    assert envelope["ok"] is True, envelope["diagnostics"]
    assert dict(_refine_bind_statuses(envelope)) == {"verified": 1}, (
        _refine_bind_statuses(envelope)
    )


def test_a_violating_recursive_construction_is_refused(tmp_path: Path) -> None:
    """Nothing concludes `refines_K`, so a construction still has to discharge.

    The unfolding axiom only lets the predicate be taken apart; it never
    establishes it.  A producer whose declared return carries the refinements
    while its body builds `Link(0 - 5, End)` is therefore refused at the
    construction — the same closure that makes assuming it sound.
    """
    source = (
        _HDR + _CHAIN +
        "private fn make(@Int -> @Chain)\n"
        "  requires(true)\n  ensures(true)\n  effects(pure)\n"
        "{\n  Link(0 - 5, End)\n}\n\n"
        "public fn main(@Int -> @Int)\n"
        "  requires(true)\n  ensures(true)\n  effects(pure)\n"
        "{\n  consume(make(1))\n}\n"
    )
    envelope = _verify(tmp_path, source, "recursive-launder")
    assert envelope["ok"] is False, envelope
    assert "E505" in {d.get("error_code") for d in envelope["diagnostics"]}
    statuses = _refine_bind_statuses(envelope)
    assert statuses["violated"] >= 1, statuses


def test_the_recursive_fact_does_not_prove_a_false_postcondition(
    tmp_path: Path,
) -> None:
    """The unfolding axiom must not make the premises inconsistent.

    An axiom asserting `forall v. refines_K(v)` would prove the refinement of
    every value of the type; one that over-constrained the premise set would
    prove every postcondition in the function, which #1451 shows is reported
    as Tier 1 with no warning.  The axiom here is an implication FROM the
    predicate, so an interpretation making it false everywhere satisfies it
    and nothing becomes inconsistent.  A deliberately FALSE postcondition is
    what tests that, since it cannot be met by identity or by vacuity.
    """
    source = (
        _HDR + _CHAIN +
        "public fn walk(@Chain -> @Int)\n"
        "  requires(true)\n"
        "  ensures(@Int.result < 0)\n"
        "  effects(pure)\n"
        "{\n  match @Chain.0 {\n"
        "    Link(@PosInt, @Chain) -> consume(@Chain.0),\n"
        "    End -> 0\n  }\n}\n"
    )
    envelope = _verify(tmp_path, source, "recursive-false-post")
    # The FALSE one specifically.  A first version asserted over every
    # `ensures` in the program and failed on `consume`'s trivially true one,
    # which is correctly verified — the assertion has to name its target or it
    # reports a soundness bug that is not there.
    false_post = [
        o["status"] for o in envelope["obligations"]
        if o["kind"] == "ensures" and "< 0" in o["description"]
    ]
    assert false_post == ["violated"], (
        f"the false postcondition was not refuted — the recursive fact may "
        f"have made the premises inconsistent: {false_post}"
    )


def test_two_contradictory_refinements_do_not_share_a_predicate(
    tmp_path: Path,
) -> None:
    """Concern 9: the predicate is keyed on the TYPE key, not the sort key.

    `_adt_sort_key` maps a refinement to its carrier on purpose — the sort is
    the carrier and the predicate is discharged elsewhere — so
    `Chain<{ @Int | @Int.0 > 0 }>` and `Chain<{ @Int | @Int.0 < 0 }>` share
    one Z3 sort AND one ADT name.  A predicate keyed on either would be the
    same symbol for both, and assuming it of a positive chain would discharge
    an obligation stated of a negative one, by identity, reporting Tier 1 for
    a value satisfying the opposite refinement.

    Two INSTANTIATIONS of one generic type is what would make this bite; two
    separate `data` declarations would not, since those differ in sort anyway.

    Reported honestly: this cell does NOT kill a mutation that keys the
    predicate on the ADT name instead.  The refutation here comes from the
    DEPTH-1 element obligation (`> 0` against `< 0`), which fires before the
    depth-2 `refines_K` is consulted, and no shape was found where the two
    refinements differ only below the first level — the refinement is on `T`,
    and `T` occurs at depth 1.  The precise key is kept because it is free and
    strictly safer, not because a program distinguishes it; if one is ever
    constructed it belongs here.
    """
    source = (
        "type PosInt = { @Int | @Int.0 > 0 };\n"
        "type NegInt = { @Int | @Int.0 < 0 };\n\n"
        "private data Chain<T> { Link(T, Chain<T>), End }\n\n"
        "private fn wants_negative(@Chain<NegInt> -> @Int)\n"
        "  requires(true)\n  ensures(true)\n  effects(pure)\n"
        "{\n  match @Chain<NegInt>.0 {\n"
        "    Link(@NegInt, @Chain<NegInt>) -> @NegInt.0,\n"
        "    End -> 0 - 1\n  }\n}\n\n"
        "public fn feed(@Chain<PosInt> -> @Int)\n"
        "  requires(true)\n  ensures(true)\n  effects(pure)\n"
        "{\n  wants_negative(@Chain<PosInt>.0)\n}\n"
    )
    envelope = _verify(tmp_path, source, "same-generic-opposite")
    assert envelope["ok"] is False, envelope
    assert dict(_refine_bind_statuses(envelope)) == {"violated": 1}, (
        "a positive chain discharged a negative refinement: "
        f"{_refine_bind_statuses(envelope)}"
    )
    assert "E505" in {d.get("error_code") for d in envelope["diagnostics"]}


# --------------------------------------------------------------------------
# Stage 1b — the R1 element licence must be backed by a runtime guard
# --------------------------------------------------------------------------
#
# Stage 1 let a callee ASSUME its parameter's element refinement, licensed by
# "every caller is obligated to discharge it at the argument position".  Being
# obligated is not discharging.  When the argument comes from an
# array-returning builtin applied to a parameter, the walk cannot state the
# result's elements, so the argument obligation resolves `tier3_unguarded` —
# counted in no tier — and `vera verify` exits 0 while the callee's `ensures`
# is reported `verified` on a program the compiled module refutes.
#
# The scalar analogue is sound because codegen emits a refinement guard at the
# boundary, so an undecided proof is backed by a runtime check.  For array
# elements no such guard existed, and stage 1 extended the licence without
# extending the guard.  These cells are the whole evidence: 0 of 474 corpus
# programs reach `_array_element_facts`, so no differential can see this.

_BLOCKING_PRODUCERS = {
    "array_append": "array_append(@Array<Int>.0, 7)",
    "array_concat": "array_concat(@Array<Int>.0, [9])",
    "array_reverse": "array_reverse(@Array<Int>.0)",
    "array_slice": "array_slice(@Array<Int>.0, 0, 1)",
}


def _blocking_program(producer: str) -> str:
    """R-1432's fixture, identical apart from the producer expression."""
    return (
        "type PosInt = { @Int | @Int.0 > 0 };\n\n"
        "private fn consume(@Array<PosInt> -> @Int)\n"
        "  requires(true)\n"
        "  ensures(@Int.result > 0)\n"
        "  effects(pure)\n"
        "{\n"
        "  if array_length(@Array<PosInt>.0) > 0 then {\n"
        "    @Array<PosInt>.0[0]\n"
        "  } else {\n"
        "    1\n"
        "  }\n"
        "}\n\n"
        "private fn launder(@Array<Int> -> @Array<PosInt>)\n"
        "  requires(true)\n"
        "  ensures(true)\n"
        "  effects(pure)\n"
        "{\n"
        f"  {producer}\n"
        "}\n\n"
        "public fn main(@Unit -> @Int)\n"
        "  requires(true)\n"
        "  ensures(true)\n"
        "  effects(pure)\n"
        "{\n"
        "  consume(launder([0 - 5]))\n"
        "}\n"
    )


@pytest.mark.parametrize("producer", sorted(_BLOCKING_PRODUCERS))
def test_a_disclosed_element_argument_is_guarded_not_merely_disclosed(
    producer: str, tmp_path: Path,
) -> None:
    """Criterion 1: the argument obligation is GUARDED, not disclosed.

    `tier3_unguarded` says "neither proved nor runtime-checked" and counts in
    no tier, so the callee's assumption rests on nothing.  With an element-wise
    boundary guard the same obligation is `tier3` — undecided statically but
    backed at run time — and counts in `tier3_runtime`.

    Asserted on the count as well as the status, because the two must move
    together: a head that relabelled the status without emitting the guard
    would leave `tier3_runtime` at 0.
    """
    source = _blocking_program(_BLOCKING_PRODUCERS[producer])
    envelope = _verify(tmp_path, source, f"blocking-{producer}")
    statuses = _refine_bind_statuses(envelope)
    assert statuses["tier3_unguarded"] == 0, (
        f"the element argument is still disclosed: {statuses}"
    )
    assert statuses["tier3"] >= 1, statuses
    assert envelope["verification"]["tier3_runtime"] >= 1, (
        envelope["verification"]
    )


@pytest.mark.parametrize("producer", sorted(_BLOCKING_PRODUCERS))
def test_the_guard_traps_at_the_argument_boundary(
    producer: str, tmp_path: Path,
) -> None:
    """Criterion 2: the trap is at the ARGUMENT boundary, not inside the callee.

    Where it traps is the whole difference between a backed assumption and a
    false Tier 1.  A postcondition violation inside `consume` means the bad
    array got in and the verifier's `verified` was wrong; a refinement
    violation at the boundary means the check the verifier promised actually
    ran.  The scalar control already behaves this way — it traps in `launder`,
    naming the refinement — and this is that behaviour for elements.

    Criterion 5 rides along: the program really is wrong, so the run must
    still fail.  What changes is HOW.
    """
    source = _blocking_program(_BLOCKING_PRODUCERS[producer])
    path = tmp_path / f"trap-{producer}.vera"
    path.write_text(source, encoding="utf-8")
    proc = _cli("run", str(path), "--fn", "main")
    assert proc.returncode != 0, proc.stdout
    combined = proc.stdout + proc.stderr
    assert "Postcondition violation in consume" not in combined, (
        "the bad array reached the callee and refuted the postcondition the "
        f"verifier proved:\n{combined[:400]}"
    )
    assert "Refinement violation" in combined, combined[:400]


@pytest.mark.parametrize("producer", sorted(_BLOCKING_PRODUCERS))
def test_the_callee_postcondition_may_stay_verified(
    producer: str, tmp_path: Path,
) -> None:
    """Criterion 3: `consume`'s `ensures` stays `verified` — that is the point
    of stage 1 — but only because the guard makes it rest on a real check.

    Kept as its own cell so a head that fixed the soundness by DEMOTING the
    postcondition fails here rather than passing quietly: retreating to
    `violated` would restore safety by giving up the Tier 1 stage 1 exists to
    win back.
    """
    source = _blocking_program(_BLOCKING_PRODUCERS[producer])
    envelope = _verify(tmp_path, source, f"post-{producer}")
    ensures = [
        o["status"] for o in envelope["obligations"]
        if o["kind"] == "ensures" and "> 0" in o["description"]
    ]
    assert ensures == ["verified"], ensures


def test_the_scalar_control_is_unchanged(tmp_path: Path) -> None:
    """Criterion 6: the scalar analogue must not move.

    The same laundering shape with a scalar `@PosInt` is caught twice — the
    obligation is `violated`/E505, and the run traps on a refinement guard at
    `launder`'s RETURN boundary.  It is the reference behaviour this change
    brings arrays into line with, so it is also the thing that must not
    regress while doing so.
    """
    source = (
        _HDR +
        "private fn consume(@PosInt -> @Int)\n"
        "  requires(true)\n  ensures(@Int.result > 0)\n  effects(pure)\n"
        "{\n  @PosInt.0\n}\n\n"
        "private fn launder(@Int -> @PosInt)\n"
        "  requires(true)\n  ensures(true)\n  effects(pure)\n"
        "{\n  @Int.0\n}\n\n"
        "public fn main(@Unit -> @Int)\n"
        "  requires(true)\n  ensures(true)\n  effects(pure)\n"
        "{\n  consume(launder(0 - 5))\n}\n"
    )
    envelope = _verify(tmp_path, source, "scalar-control")
    assert envelope["ok"] is False, envelope
    statuses = _refine_bind_statuses(envelope)
    assert statuses["violated"] >= 1, statuses

    path = tmp_path / "scalar-control.vera"
    proc = _cli("run", str(path), "--fn", "main")
    assert proc.returncode != 0
    assert "Refinement violation" in proc.stdout + proc.stderr


def test_an_unguardable_element_still_discloses(tmp_path: Path) -> None:
    """The #1362 invariant: a `guarded` claim must match what codegen emits.

    The element guard loads each element and runs the predicate on it, which
    it can only do for a scalar-shaped element.  A PAIR-shaped one — an
    `Array<Array<Int>>` element, whose runtime value is a (ptr, len) pair —
    would need the length half too, and the emitter declines it: a half-guard
    reading only the ptr is worse than an honest disclosure.

    So the verifier must decline the `tier3` claim there as well.  Claiming
    guarded for every array element regardless is the cheapest way to make
    the four blocking cells pass without earning it, and this cell is what
    makes that fail — mutation testing found it surviving otherwise.
    """
    source = (
        "type NonEmpty = { @Array<Int> | array_length(@Array<Int>.0) > 0 };\n\n"
        "private fn consume(@Array<NonEmpty> -> @Int)\n"
        "  requires(true)\n  ensures(true)\n  effects(pure)\n"
        "{\n  array_length(@Array<NonEmpty>.0)\n}\n\n"
        "private fn launder(@Array<Array<Int>> -> @Array<NonEmpty>)\n"
        "  requires(true)\n  ensures(true)\n  effects(pure)\n"
        "{\n  array_reverse(@Array<Array<Int>>.0)\n}\n\n"
        "public fn main(@Unit -> @Int)\n"
        "  requires(true)\n  ensures(true)\n  effects(pure)\n"
        "{\n  consume(launder([[1]]))\n}\n"
    )
    envelope = _verify(tmp_path, source, "pair-element")
    statuses = _refine_bind_statuses(envelope)
    assert statuses["tier3_unguarded"] >= 1, (
        "a pair-shaped element claimed a guard codegen does not emit: "
        f"{statuses}"
    )
    assert statuses["tier3"] == 0, statuses
