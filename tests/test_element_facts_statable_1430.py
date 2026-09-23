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
from tests import guard_emitter_scan

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


def _cli(*args: str, timeout: int = 120,
         env_overrides: dict[str, str] | None = None,
         ) -> subprocess.CompletedProcess[str]:
    """Run the CLI with a DERIVED environment, never the ambient one.

    `VERA_EAGER_GC` is popped from the copy before the overrides are applied,
    so a cell that does not ask for eager GC does not silently get it from
    whoever ran the suite — the two directions of every guarded cell would
    otherwise be the same direction (CodeRabbit, PR #1447).
    """
    env = dict(os.environ)
    env.pop("VERA_EAGER_GC", None)
    existing = env.get("PYTHONPATH", "")
    env["PYTHONPATH"] = (
        f"{_PKG_PARENT}{os.pathsep}{existing}" if existing else _PKG_PARENT
    )
    env.update(env_overrides or {})
    return subprocess.run(
        [sys.executable, "-m", "vera.cli", *args],
        capture_output=True, text=True, encoding="utf-8", check=False,
        env=env, timeout=timeout,
    )


def _verify(tmp_path: Path, source: str, name: str) -> dict:
    p = tmp_path / f"{name}.vera"
    p.write_text(source, encoding="utf-8")
    proc = _cli("verify", "--json", str(p))
    # An empty or malformed envelope is a CLI failure wearing a cell's
    # clothes; say so here rather than letting a KeyError further down read
    # as the property being tested (CodeRabbit, PR #1447).
    assert proc.stdout.strip(), (
        f"`vera verify --json` produced no envelope (rc={proc.returncode}): "
        f"{proc.stderr[-500:]}"
    )
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
    # Refused where the value is BUILT, not merely at the call: the whole
    # construction, since a lone digit can appear in another site's rendered
    # expression (CodeRabbit, PR #1447).
    assert any(o["description"] == "0 - 5" for o in violated), violated


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
    # A DIFFERENT program from #1449's cell, deliberately: that one indexes a
    # literal 0, so both could be discharged by the same instantiation and
    # neither proved on its own that the quantifier's content does the work
    # (CodeRabbit, PR #1447).  Here the index is a PARAMETER the contract
    # only bounds, so the solver must instantiate the quantifier at a term it
    # cannot evaluate — an identity match is unavailable twice over.
    positive = (
        _HDR +
        "public fn any_is_positive(@Array<PosInt>, @Int -> @Int)\n"
        "  requires(@Int.0 >= 0 && "
        "@Int.0 < array_length(@Array<PosInt>.0))\n"
        "  ensures(@Int.result > 0)\n"
        "  effects(pure)\n"
        "{\n  @Array<PosInt>.0[@Int.0]\n}\n"
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


# ---------------------------------------------------------------------------
# The carrier registry (#1430): one enumeration, held to the built-ins
# ---------------------------------------------------------------------------


def test_every_carrier_projection_agrees_with_its_builtin() -> None:
    """Each element position's projection is a built-in whose signature maps
    THAT carrier to an array of THAT type argument.

    The registry's whole value is that three lowerings read one table rather
    than branching per container, so a projection naming nothing — a typo, a
    built-in renamed out from under it — would make every one of them decline
    for that carrier with nothing to say why.  Asserted against the live
    signature rather than a hand-written list, and against the ARGUMENT INDEX
    too: `map_keys : Map<K, V> -> Array<K>` pins the key position to index 0
    and `map_values : Map<K, V> -> Array<V>` the value position to index 1, so
    a registry with the two swapped would state a fact about the keys to
    discharge a goal about the values, and this cell is what refuses it.
    """
    from vera.carriers import element_carriers
    from vera.environment import TypeEnv
    from vera.types import AdtType, PrimitiveType, TypeVar

    functions = TypeEnv().functions
    int_ty = PrimitiveType("Int")
    string_ty = PrimitiveType("String")
    seen: set[str] = set()
    for shape in (AdtType("Array", (int_ty,)),
                  AdtType("Map", (string_ty, int_ty)),
                  AdtType("Set", (int_ty,))):
        positions = element_carriers(shape)
        assert positions, f"{shape.name} has no element position registered"
        for carrier in positions:
            if carrier.projection is None:
                assert shape.name == "Array", (
                    f"{carrier.kind} projects nothing, but only an `Array` is "
                    f"its own element sequence"
                )
                continue
            spec = functions.get(carrier.projection)
            assert spec is not None, (
                f"{carrier.kind} projects through `{carrier.projection}`, "
                f"which is not a built-in — every lowering would decline for "
                f"this carrier and nothing would say why"
            )
            seen.add(carrier.projection)
            # Takes this carrier...
            assert len(spec.param_types) == 1, spec
            param = spec.param_types[0]
            assert isinstance(param, AdtType) and param.name == shape.name, (
                f"`{carrier.projection}` takes {param}, not a {shape.name}"
            )
            # ...and returns an array of the argument at this position.
            ret = spec.return_type
            assert isinstance(ret, AdtType) and ret.name == "Array", (
                f"`{carrier.projection}` returns {ret}, not an array: the "
                f"element goal quantifies over a sequence's indices, so a "
                f"projection returning anything else has no elements"
            )
            returned = ret.type_args[0]
            assert isinstance(returned, TypeVar), ret
            index = param.type_args.index(returned)
            assert shape.type_args[index] == carrier.element_type, (
                f"`{carrier.projection}` projects type argument {index} of "
                f"{shape.name}, but the registry gives {carrier.kind} the "
                f"type {carrier.element_type} — the two disagree about WHICH "
                f"position this projection reads"
            )
    assert seen == {"map_keys", "map_values", "set_to_array"}, seen


def test_a_type_with_no_element_position_is_not_a_carrier() -> None:
    """A type with constructor decomposition is NOT a carrier.

    The distinction keeps the two mechanisms apart: `Option<PosInt>`'s payload
    is reached by an accessor and stated EXACTLY by the structural walk, and
    routing it through an element quantifier would replace that with a weaker
    fact.  This cell is the boundary, in the direction a widened registry
    would break.
    """
    from vera import ast as vera_ast
    from vera.carriers import element_carriers, is_carrier
    from vera.types import AdtType, PrimitiveType, RefinedType

    int_ty = PrimitiveType("Int")
    # Any predicate node will do: what is under test is the SHAPE of the
    # type, and `element_carriers` never reads a predicate.
    pos = RefinedType(int_ty, vera_ast.IntLit(0))
    for shape in (AdtType("Option", (pos,)),
                  AdtType("Result", (pos, int_ty)),
                  AdtType("Tuple", (pos, int_ty)),
                  AdtType("Chain", ()),
                  int_ty,
                  pos):
        assert element_carriers(shape) == (), shape
        assert not is_carrier(shape), shape


def test_a_non_regular_declaration_does_not_hang_the_element_walk(
    tmp_path: Path,
) -> None:
    """A NON-REGULAR declaration terminates the walk by the rule (#1429).

    R1 states a parameter's nested refinements for EVERY parameter, which is a
    walk through constructor fields keyed on the INSTANTIATED type — and a
    non-regular declaration gives that key no fixed point: `Nest<Pos>`, then
    `Nest<Option<Pos>>`, then `Nest<Option<Option<Pos>>>`, each new, so the
    `seen` set never closes.  Measured on this branch before the fix:
    `tests/test_nonregular_data_rejected_1429.py` did not complete in 600 s,
    where it takes twelve.

    The refinement is what makes this cell the element walk's own: the
    upstream cell's program carries none, so it stops at the first
    `_contains_refinement`; this one has facts to build at every level and
    still must decline.  A TIME assertion rather than a status one, because
    what failed was termination — and a generous bound, since what separates
    pass from fail here is seconds against never.
    """
    import time

    source = (
        "type Pos = { @Int | @Int.0 > 0 };\n\n"
        "private data Nest<T> { N(Nest<Option<T>>), Z }\n\n"
        "public fn f(@Nest<Pos> -> @Int)\n"
        "  requires(true)\n  ensures(true)\n  effects(pure)\n"
        "{\n  match @Nest<Pos>.0 { N(@Nest<Option<Pos>>) -> 1, Z -> 0 }\n}\n"
    )
    started = time.monotonic()
    envelope = _verify(tmp_path, source, "non-regular")
    elapsed = time.monotonic() - started
    assert elapsed < 60, f"the element walk did not decline promptly: {elapsed}s"
    # The checker refuses the declaration (E129), which is the point: the
    # walk must decline anyway, because `verify()` is a public entry point
    # whose check-clean precondition is the caller's to keep.
    assert any(d.get("error_code") == "E129"
               for d in envelope.get("diagnostics", [])), envelope


# ---------------------------------------------------------------------------
# The element guard is PRESENT where the status claims it (#1362, #1430)
# ---------------------------------------------------------------------------
#
# Not an agreement between two tables — two tables agree while both are wrong,
# and that is how a `tier3` came to be recorded at a closure boundary whose
# module carried no element loop at all.  Each cell reads the EMITTED module:
# a claimed guard means a loop at that boundary and a violating value refused
# at run time; a disclosure means no loop and a clean run.

_CLOSURE_ONLY = (
    "type Pos = { @Int | @Int.0 > 0 };\n\n"
    "private fn launder(@Array<Int> -> @Array<Int>)\n"
    "  requires(true)\n  ensures(true)\n  effects(pure)\n"
    "{\n  array_append(@Array<Int>.0, 0 - 5)\n}\n\n"
    "public fn main(@Unit -> @Int)\n"
    "  requires(true)\n  ensures(true)\n  effects(pure)\n"
    "{\n  apply_fn(fn(@Array<Pos> -> @Int) effects(pure) "
    "{ array_length(@Array<Pos>.0) }, launder([1]))\n}\n"
)


def _element_loops(tmp_path: Path, source: str, name: str) -> dict[str, int]:
    """Element guard loops in the emitted module, per WASM function."""
    p = tmp_path / f"{name}.vera"
    p.write_text(source, encoding="utf-8")
    proc = _cli("compile", "--wat", str(p))
    # A compile FAILURE yields no WAT, which parses as "zero element loops"
    # and passes every disclosure cell for the wrong reason (CodeRabbit,
    # PR #1447).  The exit code is the only thing that separates the two.
    assert proc.returncode == 0, (
        f"`vera compile --wat` failed (rc={proc.returncode}), so the WAT this "
        f"cell reads is empty rather than loop-free: {proc.stderr[-500:]}"
    )
    wat = proc.stdout
    loops: dict[str, int] = {}
    current = "?"
    for line in wat.splitlines():
        stripped = line.strip()
        if stripped.startswith("(func $"):
            current = stripped.split()[1]
        elif stripped.startswith("loop $lp_elem"):
            loops[current] = loops.get(current, 0) + 1
    return loops


def _run(tmp_path: Path, source: str, name: str,
         eager_gc: bool = False) -> subprocess.CompletedProcess[str]:
    p = tmp_path / f"{name}.vera"
    p.write_text(source, encoding="utf-8")
    # Passed through rather than set on `os.environ`: mutating the process
    # environment leaks into every other cell running beside this one, and
    # restoring it in a `finally` only narrows the window.
    return _cli("run", str(p),
                env_overrides={"VERA_EAGER_GC": "1"} if eager_gc else None)


def test_a_guarded_closure_boundary_carries_the_loop_it_claims(
    tmp_path: Path,
) -> None:
    """A `tier3` at a CLOSURE boundary means a loop in the lifted body.

    The red-first cell, measured before the emitter was wired there: the
    obligation read `tier3` — a claimed runtime check — while the whole module
    contained ZERO element loops and `vera run` returned 2 on an array whose
    last element is `-5`.  The status half read the scalar guard roster, which
    answers a different lowering's question.
    """
    envelope = _verify(tmp_path, _CLOSURE_ONLY, "closure-only")
    statuses = _refine_bind_statuses(envelope)
    # ON THE RECORD, not at a pinned status.  The `apply_fn` argument's own
    # status follows the modular rule — `launder` is declared
    # `-> @Array<Int>`, so its result is refuted like any other unestablished
    # narrowing — and the claim under test is the BOUNDARY's, which is that a
    # loop exists and the value is refused.  Pinning `tier3` here would have
    # been pinning the F1 defect: before that fix, the `array_length` call
    # inside the closure body read `tier3` for a built-in that carries no
    # prologue.
    assert statuses, "the closure boundary is silent"
    assert statuses["tier3_unguarded"] + statuses["violated"] >= 1, statuses

    loops = _element_loops(tmp_path, _CLOSURE_ONLY, "closure-only")
    lifted = {fn: n for fn, n in loops.items() if fn.startswith("$rt.anon")}
    assert lifted, (
        f"the obligation claims a runtime check at the closure boundary and "
        f"the module carries no element loop in any lifted body: {loops}"
    )

    result = _run(tmp_path, _CLOSURE_ONLY, "closure-only")
    assert result.returncode != 0, (
        f"a violating element crossed a boundary the status calls guarded "
        f"and the program ran to completion: {result.stdout}"
    )
    assert "array element" in result.stdout + result.stderr, result.stdout


def test_the_guarded_closure_boundary_holds_under_eager_gc(
    tmp_path: Path,
) -> None:
    """The same, with a collection at every allocation.

    The guard runs in the lifted body's prologue, where the shadow stack has
    just been set up; `VERA_EAGER_GC=1` is what says the walk reads the array
    it was handed rather than a swept one.
    """
    result = _run(tmp_path, _CLOSURE_ONLY, "closure-eager", eager_gc=True)
    assert result.returncode != 0, result.stdout
    assert "array element" in result.stdout + result.stderr, result.stdout


def test_a_disclosed_element_boundary_carries_no_loop(tmp_path: Path) -> None:
    """The complement: an unguardable element base emits nothing and says so.

    A `String` element is pair-represented, so the loop's single scalar load
    cannot read it — the emitter declines and the verifier discloses.  The
    cell asserts BOTH halves, because a module that quietly emitted a
    half-guard would satisfy the status half alone.
    """
    source = (
        "type NonEmpty = { @String | string_length(@String.0) > 0 };\n\n"
        "private fn consume(@Array<NonEmpty> -> @Int)\n"
        "  requires(true)\n  ensures(true)\n  effects(pure)\n"
        "{\n  array_length(@Array<NonEmpty>.0)\n}\n\n"
        "public fn main(@Unit -> @Int)\n"
        "  requires(true)\n  ensures(true)\n  effects(pure)\n"
        '{\n  consume([""])\n}\n'
    )
    envelope = _verify(tmp_path, source, "pair-base")
    statuses = _refine_bind_statuses(envelope)
    assert statuses["tier3_unguarded"] >= 1, statuses
    assert statuses["tier3"] == 0, statuses
    assert _element_loops(tmp_path, source, "pair-base") == {}, (
        "a base the emitter declines still produced an element loop"
    )
    result = _run(tmp_path, source, "pair-base")
    assert result.returncode == 0, result.stdout


def _emitter_call_sites() -> set[str]:
    """The FUNCTIONS that call the element-guard emitter, read from source.

    Through `tests/guard_emitter_scan.py`, which ENUMERATES the
    code-generation layer.  This scan used to name four files, so an emitter
    wired in a fifth was its blind spot — the comparison would have gone on
    agreeing while a whole position went unheld (PR #1447 review, 65d90c4e).
    The scan is shared with the boundary-guard roster
    (`test_boundary_guard_correctness_1466.py`), so "where guards are
    emitted" is derived once rather than once per roster.
    """
    return guard_emitter_scan.emitter_call_sites("_emit_element_guards")


def test_the_emitter_scan_enumerates_the_codegen_layer() -> None:
    """The scan's own premise: the four files it used to name are INSIDE the
    enumeration, rather than being it.

    A roster is worth what holds it to the emitter, and the scan is what does
    the holding — so the scan's reach is asserted rather than assumed.
    """
    enumerated = {
        str(p).split(f"{os.sep}vera{os.sep}")[-1].replace(os.sep, "/")
        for p in guard_emitter_scan.codegen_sources()
    }
    missing = [
        f for f in guard_emitter_scan.KNOWN_EMITTER_FILES
        if f not in enumerated
    ]
    assert not missing, (
        f"{missing} wire a guard emitter and are outside the enumerated "
        f"code-generation layer {sorted(guard_emitter_scan.EMITTER_PACKAGES)}"
    )
    assert len(enumerated) > len(guard_emitter_scan.KNOWN_EMITTER_FILES), (
        "the enumeration is no larger than the list it replaced, so it is "
        "still a list"
    )


def test_the_element_guard_roster_matches_where_it_is_wired() -> None:
    """Every roster position names a FUNCTION that wires the emitter, and
    every function that wires it is named by a position.

    The roster is what a `guarded` status is read from, so it may not be a
    list someone keeps up to date: it is held to the emitter's call sites,
    resolved to the enclosing function rather than to the file.  File
    granularity is what let the `return type` entry name `functions.py` —
    which wires the PARAMETER loop — while the return boundary is emitted in
    `contracts.py`, with nothing to notice (PR #1447 review, F3).
    """
    from vera import carriers

    wired = _emitter_call_sites()
    named = set(carriers.ELEMENT_GUARD_SITES.values())
    assert wired == named, (
        f"the element-guard roster and the emitter's call sites disagree: "
        f"wired={sorted(wired)} named={sorted(named)}"
    )


def test_dropping_any_roster_entry_is_visible() -> None:
    """EVERY entry, not one example.

    A scan that compares SETS is satisfied by a roster that still names each
    file through some other entry, which is exactly how `closure return`
    could be deleted with the suite staying green.  This drives the
    comparison the scan makes once per entry, so each one is load-bearing on
    its own.
    """
    from vera import carriers

    wired = _emitter_call_sites()
    for position in sorted(carriers.ELEMENT_GUARD_SITES):
        without = {
            fn for site, fn in carriers.ELEMENT_GUARD_SITES.items()
            if site != position
        }
        assert without != wired, (
            f"deleting `{position}` from the roster leaves the comparison "
            f"unchanged, so nothing holds that entry to an emitter"
        )


# ---------------------------------------------------------------------------
# The class instrument: carrier kind x fact shape x consumer (#1430)
# ---------------------------------------------------------------------------
#
# The class is "a container's element refinements are stated per container",
# so the instrument ranges over the CARRIERS and asserts they answer alike:
# identical statuses for identical element facts, one guard shape, one trap.
# A cell per carrier written by hand would demonstrate the instance three
# times; the product is what says the lowering is one lowering.

#: carrier -> (declared slot, an expression producing a good one from `@Int.0`,
#:             the position's name in a trap message)
_CARRIERS: dict[str, tuple[str, str, str]] = {
    "array": ("@Array<Pos>", "array_append([], @Int.0)", "array element"),
    "map": ("@Map<String, Pos>", 'map_insert(map_new(), "a", @Int.0)',
            "map value"),
    # The KEY position, which is a different projection (`map_keys`) and a
    # different guard: every other map fixture puts the refinement in the
    # value, so a defect in the key half would pass the matrix unseen
    # (CodeRabbit, PR #1447).
    "map-key": ("@Map<Pos, String>", 'map_insert(map_new(), @Int.0, "a")',
                "map key"),
    "set": ("@Set<Pos>", "set_add(set_new(), @Int.0)", "set element"),
}

#: The same three, with the element type left UNREFINED — what an opaque
#: producer hands over, so the consumer's parameter is a real narrowing.
_PLAIN = {"array": "@Array<Int>", "map": "@Map<String, Int>",
          "map-key": "@Map<Int, String>", "set": "@Set<Int>"}

#: What the consumer does with the carrier.  Two consumers, because a fact
#: that reaches one and not the other is the drift this class is made of.
_CONSUMERS = {
    "size": {"array": "array_length", "map": "map_size",
             "map-key": "map_size", "set": "set_size"},
}


def _forwarding(carrier: str) -> str:
    """A parameter forwarded to a callee at the SAME refined carrier type."""
    slot, _produce, _kind = _CARRIERS[carrier]
    size = _CONSUMERS["size"][carrier]
    return (
        "type Pos = { @Int | @Int.0 > 0 };\n\n"
        f"private fn consume({slot} -> @Int)\n"
        "  requires(true)\n  ensures(true)\n  effects(pure)\n"
        f"{{\n  {size}({slot}.0)\n}}\n\n"
        f"private fn forward({slot} -> @Int)\n"
        "  requires(true)\n  ensures(true)\n  effects(pure)\n"
        f"{{\n  consume({slot}.0)\n}}\n\n"
        "public fn main(@Unit -> @Int)\n"
        "  requires(true)\n  ensures(true)\n  effects(pure)\n"
        "{\n  forward(" + _CARRIERS[carrier][1].replace("@Int.0", "5")
        + ")\n}\n"
    )


def _laundered(carrier: str, value: str) -> str:
    """A carrier built behind an UNREFINED return, so the consumer's
    parameter is the only boundary the element predicate can be checked at."""
    slot, produce, _kind = _CARRIERS[carrier]
    plain = _PLAIN[carrier]
    size = _CONSUMERS["size"][carrier]
    return (
        "type Pos = { @Int | @Int.0 > 0 };\n\n"
        f"private fn launder(@Int -> {plain})\n"
        "  requires(true)\n  ensures(true)\n  effects(pure)\n"
        f"{{\n  {produce}\n}}\n\n"
        f"private fn consume({slot} -> @Int)\n"
        "  requires(true)\n  ensures(true)\n  effects(pure)\n"
        f"{{\n  {size}({slot}.0)\n}}\n\n"
        "public fn main(@Unit -> @Int)\n"
        "  requires(true)\n  ensures(true)\n  effects(pure)\n"
        f"{{\n  consume(launder({value}))\n}}\n"
    )


@pytest.mark.parametrize("carrier", sorted(_CARRIERS))
def test_forwarding_proves_at_tier_1_for_every_carrier(
    carrier: str, tmp_path: Path,
) -> None:
    """The case #1430 measured: a forwarded carrier goes `verified`.

    The issue's own synthetic case is a `Map<K, Refined>` forwarded inside a
    callee, which went `verified` -> `tier3_unguarded` when #1410 removed the
    type-comparison shortcut.  It comes back as a DISCHARGED obligation — the
    parameter's assumed element fact and the argument's goal name the same
    projection symbol, so the query is closed by congruence rather than by a
    shortcut — and it must do so for every carrier, which is the whole claim
    of one lowering.
    """
    envelope = _verify(tmp_path, _forwarding(carrier), f"fwd-{carrier}")
    statuses = _refine_bind_statuses(envelope)
    assert envelope["ok"] is True, envelope.get("diagnostics")
    assert statuses["verified"] >= 1, (
        f"{carrier}: forwarding a refined carrier did not discharge: "
        f"{statuses}"
    )
    # EVERY `refine_bind` is accounted for, not just the presence of one: a
    # stream holding a `verified` beside a `violated` or a disclosure would
    # satisfy a floor while the carrier had stopped discharging what it used
    # to (CodeRabbit, PR #1447).  `tier3` is admitted and `violated` and
    # `tier3_unguarded` are not, because the program's OUTERMOST site hands a
    # freshly constructed carrier to a refined parameter — a boundary with a
    # guard, honestly Tier 3 — while the forwarding site under test is the
    # one that must discharge.
    assert set(statuses) <= {"verified", "tier3"}, statuses


def test_every_carrier_answers_the_same_way() -> None:
    """The product's point: the three carriers report ALIKE.

    Asserted as one comparison over the whole set rather than three separate
    expectations — the #1461 lesson — so a carrier that drifts shows up as a
    disagreement instead of as a cell someone forgot to update.
    """
    import tempfile

    seen: dict[str, tuple] = {}
    for carrier in sorted(_CARRIERS):
        with tempfile.TemporaryDirectory() as d:
            envelope = _verify(Path(d), _forwarding(carrier), f"cmp-{carrier}")
        seen[carrier] = tuple(sorted(_refine_bind_statuses(envelope).items()))
    assert len(set(seen.values())) == 1, (
        f"the carriers do not answer alike on the same element fact: {seen}"
    )


@pytest.mark.parametrize("carrier", sorted(_CARRIERS))
def test_a_laundered_element_traps_at_the_boundary(
    carrier: str, tmp_path: Path,
) -> None:
    """A violating element from an opaque producer is refused at RUN TIME.

    The guard is what licenses the R1 assumption, so the cell reads the
    emitted module and the process exit rather than a status: a `Map` or
    `Set` boundary projects its handle through the same host import an
    ordinary `map_values(m)` call would and walks the pair that comes back,
    which is why one loop serves every carrier.
    """
    source = _laundered(carrier, "0 - 5")
    result = _run(tmp_path, source, f"bad-{carrier}")
    assert result.returncode != 0, (
        f"{carrier}: a violating element crossed a guarded boundary and the "
        f"program ran to completion: {result.stdout}"
    )
    assert _CARRIERS[carrier][2] in result.stdout + result.stderr, result.stdout


@pytest.mark.parametrize("carrier", sorted(_CARRIERS))
def test_a_satisfying_element_is_not_refused_at_run_time(
    carrier: str, tmp_path: Path,
) -> None:
    """The direction #1466 is about: the guard must not refuse a good value.

    A guard that traps on a value its predicate admits is worse than no
    guard, so every carrier's good case is run, not merely verified.
    """
    result = _run(tmp_path, _laundered(carrier, "5"), f"good-{carrier}")
    assert result.returncode == 0, (
        f"{carrier}: a satisfying element was refused at run time: "
        f"{result.stdout}{result.stderr}"
    )


@pytest.mark.parametrize("carrier", sorted(_CARRIERS))
def test_the_guarded_carrier_holds_under_eager_gc(
    carrier: str, tmp_path: Path,
) -> None:
    """A projection ALLOCATES the array it returns, so the walk runs with a
    collection at every allocation.

    `Map` and `Set` reach their elements through a host import that builds a
    fresh array; the array carrier does not allocate at all.  BOTH directions
    are run, and the satisfying one is the load-bearing half: a violating
    value must trap anyway, so corruption during the projection could produce
    another invalid value and pass (CodeRabbit, PR #1447).  A SATISFYING
    value completing is what says the walk read the sequence it was handed
    rather than a swept one.
    """
    good = _run(tmp_path, _laundered(carrier, "5"), f"eager-good-{carrier}",
                eager_gc=True)
    assert good.returncode == 0, (
        f"{carrier}: a satisfying element was refused under eager GC — the "
        f"walk read something other than the sequence it was handed: "
        f"{good.stdout}{good.stderr}"
    )
    bad = _run(tmp_path, _laundered(carrier, "0 - 5"), f"eager-bad-{carrier}",
               eager_gc=True)
    assert bad.returncode != 0, bad.stdout
    assert _CARRIERS[carrier][2] in bad.stdout + bad.stderr, bad.stdout


# ---------------------------------------------------------------------------
# Depth x producer kind: the element arm answers what the SCALAR arm answers
# ---------------------------------------------------------------------------
#
# Making the goal statable is a TIGHTENING, not a fix: where the element
# position used to disclose because nothing could be said about it, it now
# reports whatever the scalar rule reports for the same producer.  That is the
# consistent modular answer — a callee declared `-> @Array<Int>` with
# `ensures(true)` permits a violating result, exactly as a `-> @Int` one does —
# and the rows below are what hold the two depths together, so the day the
# scalar rule moves and the element arm does not follow, the disagreement is a
# red cell rather than a discovery.
#
# Measured at `release/v0.2.0` and at this head: the scalar column is
# IDENTICAL at both revisions (this PR does not touch it), the element column
# was `tier3_unguarded` at the tip for every producer, and is now the scalar
# answer for every producer.

_PRODUCERS: dict[str, tuple[str, str]] = {
    # name -> (scalar program, element program)
    "callee-result": (
        "private fn launder(@Int -> @Int)\n"
        "  requires(true)\n  ensures(true)\n  effects(pure)\n"
        "{\n  @Int.0\n}\n\n"
        "private fn consume(@Pos -> @Int)\n"
        "  requires(true)\n  ensures(true)\n  effects(pure)\n"
        "{\n  @Pos.0\n}\n\n"
        "public fn main(@Unit -> @Int)\n"
        "  requires(true)\n  ensures(true)\n  effects(pure)\n"
        "{\n  consume(launder(5))\n}\n",
        "private fn launder(@Int -> @Array<Int>)\n"
        "  requires(true)\n  ensures(true)\n  effects(pure)\n"
        "{\n  array_append([], @Int.0)\n}\n\n"
        "private fn consume(@Array<Pos> -> @Int)\n"
        "  requires(true)\n  ensures(true)\n  effects(pure)\n"
        "{\n  array_length(@Array<Pos>.0)\n}\n\n"
        "public fn main(@Unit -> @Int)\n"
        "  requires(true)\n  ensures(true)\n  effects(pure)\n"
        "{\n  consume(launder(5))\n}\n",
    ),
    "free-parameter": (
        "private fn consume(@Pos -> @Int)\n"
        "  requires(true)\n  ensures(true)\n  effects(pure)\n"
        "{\n  @Pos.0\n}\n\n"
        "public fn entry(@Int -> @Int)\n"
        "  requires(true)\n  ensures(true)\n  effects(pure)\n"
        "{\n  consume(@Int.0)\n}\n",
        "private fn consume(@Array<Pos> -> @Int)\n"
        "  requires(true)\n  ensures(true)\n  effects(pure)\n"
        "{\n  array_length(@Array<Pos>.0)\n}\n\n"
        "public fn entry(@Array<Int> -> @Int)\n"
        "  requires(true)\n  ensures(true)\n  effects(pure)\n"
        "{\n  consume(@Array<Int>.0)\n}\n",
    ),
    "effect-operation": (
        "effect Source {\n  op fetch(Unit -> Int);\n}\n\n"
        "private fn consume(@Pos -> @Int)\n"
        "  requires(true)\n  ensures(true)\n  effects(pure)\n"
        "{\n  @Pos.0\n}\n\n"
        "public fn entry(@Unit -> @Int)\n"
        "  requires(true)\n  ensures(true)\n  effects(<Source>)\n"
        "{\n  consume(Source.fetch(()))\n}\n",
        "effect Source {\n  op fetch(Unit -> Array<Int>);\n}\n\n"
        "private fn consume(@Array<Pos> -> @Int)\n"
        "  requires(true)\n  ensures(true)\n  effects(pure)\n"
        "{\n  array_length(@Array<Pos>.0)\n}\n\n"
        "public fn entry(@Unit -> @Int)\n"
        "  requires(true)\n  ensures(true)\n  effects(<Source>)\n"
        "{\n  consume(Source.fetch(()))\n}\n",
    ),
}


@pytest.mark.parametrize("producer", sorted(_PRODUCERS))
def test_the_element_arm_answers_what_the_scalar_arm_answers(
    producer: str, tmp_path: Path,
) -> None:
    """Same producer, two depths, one answer.

    The cell compares the two STREAMS' distinguishing status rather than a
    literal, so it holds the two arms together without pinning either to a
    verdict a later rule change would have to edit in two places.  A literal
    expectation here would go green for a compiler that had stopped deciding
    anything, which is what TESTING.md § Class Instruments warns a status
    assertion can do.
    """
    header = "type Pos = { @Int | @Int.0 > 0 };\n\n"
    scalar_src, element_src = _PRODUCERS[producer]
    scalar = _refine_bind_statuses(
        _verify(tmp_path, header + scalar_src, f"scalar-{producer}"))
    element = _refine_bind_statuses(
        _verify(tmp_path, header + element_src, f"element-{producer}"))
    assert scalar, f"the scalar twin raised no refine_bind at all: {scalar}"
    assert element, f"the element case raised no refine_bind at all: {element}"
    worst = ["violated", "tier3_unguarded", "tier3", "verified"]
    scalar_worst = next(s for s in worst if scalar.get(s))
    element_worst = next(s for s in worst if element.get(s))
    assert scalar_worst == element_worst, (
        f"{producer}: the scalar twin reports {scalar_worst} and the element "
        f"case reports {element_worst} — one narrowing rule must hold at "
        f"every depth (scalar={dict(scalar)}, element={dict(element)})"
    )


def test_the_element_load_width_matches_the_stride(tmp_path: Path) -> None:
    """A one-byte element is read with a one-byte load.

    `Bool` and `Byte` are stored one byte wide and read into an `i32` local,
    so deriving the load from the LOCAL's type emits `i32.load` for a
    one-byte stride: each predicate would see three adjacent elements, and
    the last iteration would read past the sequence.  The width belongs with
    the stride, and the cell reads the EMITTED module because that is where
    the two can disagree (CodeRabbit, PR #1447).
    """
    source = (
        "type Truthy = { @Bool | @Bool.0 };\n\n"
        "private fn launder(@Bool -> @Array<Bool>)\n"
        "  requires(true)\n  ensures(true)\n  effects(pure)\n"
        "{\n  array_append([true, true, true], @Bool.0)\n}\n\n"
        "private fn consume(@Array<Truthy> -> @Int)\n"
        "  requires(true)\n  ensures(true)\n  effects(pure)\n"
        "{\n  array_length(@Array<Truthy>.0)\n}\n\n"
        "public fn main(@Unit -> @Int)\n"
        "  requires(true)\n  ensures(true)\n  effects(pure)\n"
        "{\n  consume(launder(VALUE))\n}\n"
    )
    good = source.replace("VALUE", "true")
    p = tmp_path / "byte-elem.vera"
    p.write_text(good, encoding="utf-8")
    proc = _cli("compile", "--wat", str(p))
    assert proc.returncode == 0, (
        f"`vera compile --wat` failed (rc={proc.returncode}): "
        f"{proc.stderr[-500:]}"
    )
    wat = proc.stdout
    loop_body = wat[wat.index("loop $lp_elem"):] if "loop $lp_elem" in wat else ""
    assert "i32.load8_u" in loop_body, (
        "a one-byte element is read with a wider load; the guard would see "
        f"adjacent elements:\n{loop_body[:400]}"
    )
    assert _run(tmp_path, good, "byte-good").returncode == 0, (
        "a satisfying one-byte array was refused at run time"
    )
    bad = _run(tmp_path, source.replace("VALUE", "false"), "byte-bad")
    assert bad.returncode != 0, bad.stdout
    assert "array element" in bad.stdout + bad.stderr, bad.stdout


def test_a_projection_needs_a_minted_carrier_sort() -> None:
    """`carrier_elements` declines a term that is not in a carrier sort.

    A `Map` or `Set` the verifier could not give a carrier sort to falls
    through to `declare_int`, and projecting THAT would mint `map_values_Int`
    — a symbol with no carrier behind it, shared by every such fallback whose
    element sorts agree, so a fact about one map's values could meet a goal
    about another's (CodeRabbit, PR #1447).  Asserted at the seam rather than
    through a program, because what must not happen is the minting.
    """
    import z3

    from vera.smt import SmtContext
    from vera.types import PrimitiveType

    smt = SmtContext()
    int_ty = PrimitiveType("Int")
    fallback = smt.declare_int("m")
    assert smt.carrier_elements(fallback, "map_values", int_ty) is None, (
        "an Int-modelled container was projected; the symbol that mints has "
        "no carrier behind it"
    )
    minted = smt.declare_collection_var(
        "m2", "Map", (z3.StringSort(), z3.IntSort()))
    observers = smt.carrier_elements(minted, "map_values", int_ty)
    assert observers is not None, "a minted carrier sort was declined"
    sequence, _index_fn, _length_fn, _elt = observers
    assert str(sequence.sort()).startswith("Array_"), sequence


def test_the_guard_pre_scan_sees_the_element_predicate(
    tmp_path: Path,
) -> None:
    """Every predicate the guard LOWERS is in the pre-scan's enumeration.

    The pre-scan registers the host imports and handler families a boundary
    guard's predicate needs; a predicate reached only by the element walk is
    invisible to the structural scan of the body, so an import it needs would
    be lowered against nothing the module declares — the #808 fan-in, one
    lowering further out (CodeRabbit, PR #1447).

    Driven through the real compile path so the alias table and the registry
    are the ones a program gets, and asserted over the ENUMERATION rather
    than over a module that happens to need an import: the cell then fails
    when the walk is extended and the pre-scan is not.
    """
    from vera import ast
    from vera.codegen.core import CodeGenerator
    from vera.parser import parse_to_ast

    source = (
        "type PosInt = { @Int | @Int.0 > 0 };\n\n"
        "public fn f(@Array<PosInt> -> @Int)\n"
        "  requires(true)\n  ensures(true)\n  effects(pure)\n"
        "{\n  array_length(@Array<PosInt>.0)\n}\n"
    )
    program = parse_to_ast(source)
    gen = CodeGenerator(source)
    gen.compile_program(program)
    decl = next(
        d for d in (getattr(x, "decl", x) for x in program.declarations)
        if isinstance(d, ast.FnDecl) and d.name == "f"
    )
    rendered = [
        ast.format_expr(p) for p in gen._signature_refinement_predicates(decl)
    ]
    assert any("@Int.0 > 0" in r for r in rendered), (
        f"the element predicate the guard lowers is not in the pre-scan's "
        f"enumeration: {rendered}"
    )


# ---------------------------------------------------------------------------
# A site name is not a guarantee that the CALLEE carries the guard (F1)
# ---------------------------------------------------------------------------
#
# `ELEMENT_GUARD_SITES["call argument"]` names the emitter in
# `vera/codegen/functions.py` — the CALLEE's prologue.  A built-in has none,
# so at `array_length(a[0])` the element record read `tier3`, a promised
# runtime check, while the module carried no element loop anywhere and a `-5`
# ran through (PR #1447 review, F1).  Each cell reads the record, the EMITTED
# module and the run, because two agreeing tables is what this PR says it
# will not rely on.

_NESTED_HEADER = "type Pos = { @Int | @Int.0 > 0 };\n\n"
_HIDE = (
    "private fn hide(@Int -> @Array<Array<Pos>>)\n"
    "  requires(true)\n  ensures(true)\n  effects(pure)\n"
    "{\n  array_append([], [@Int.0])\n}\n\n"
)
_MAIN = (
    "public fn main(@Unit -> @Int)\n"
    "  requires(true)\n  ensures(true)\n  effects(pure)\n"
    "{\n  peek(hide(0 - 5))\n}\n"
)
_BUILTIN_CALLEE = _NESTED_HEADER + (
    "private fn peek(@Array<Array<Pos>> -> @Int)\n"
    "  requires(array_length(@Array<Array<Pos>>.0) > 0)\n"
    "  ensures(true)\n  effects(pure)\n"
    "{\n  array_length(@Array<Array<Pos>>.0[0])\n}\n\n"
) + _HIDE + _MAIN
_BUILTIN_MAP = _NESTED_HEADER + (
    "public fn entry(@Array<Map<Int, Pos>> -> @Int)\n"
    "  requires(array_length(@Array<Map<Int, Pos>>.0) > 0)\n"
    "  ensures(true)\n  effects(pure)\n"
    "{\n  map_size(@Array<Map<Int, Pos>>.0[0])\n}\n"
)
_USER_CALLEE = _NESTED_HEADER + (
    "private fn consume(@Array<Pos> -> @Int)\n"
    "  requires(true)\n  ensures(true)\n  effects(pure)\n"
    "{\n  array_length(@Array<Pos>.0)\n}\n\n"
    "private fn peek(@Array<Array<Pos>> -> @Int)\n"
    "  requires(array_length(@Array<Array<Pos>>.0) > 0)\n"
    "  ensures(true)\n  effects(pure)\n"
    "{\n  consume(@Array<Array<Pos>>.0[0])\n}\n\n"
) + _HIDE + _MAIN


@pytest.mark.parametrize("name,source", [
    ("array", _BUILTIN_CALLEE), ("map", _BUILTIN_MAP),
])
def test_a_builtin_callee_discloses_rather_than_claiming_a_guard(
    name: str, source: str, tmp_path: Path,
) -> None:
    """A built-in callee has no prologue, so the element record must disclose.

    Measured at the release tip: `tier3_unguarded`.  Measured here before the
    fix: `tier3` — a claimed runtime check — with ZERO element loops in the
    whole module and `vera run` returning 1 with a `-5` inside.  The cell
    holds all three together, because the record alone was already wrong
    while the other two looked fine.
    """
    envelope = _verify(tmp_path, source, f"builtin-{name}")
    statuses = _refine_bind_statuses(envelope)
    assert statuses["tier3"] == 0, (
        f"a built-in callee claims a runtime check it cannot carry: "
        f"{statuses}"
    )
    assert statuses["tier3_unguarded"] >= 1, statuses
    assert _element_loops(tmp_path, source, f"builtin-{name}") == {}, (
        "no element guard can be emitted for a built-in callee, so any loop "
        "here belongs to something else"
    )


def test_a_user_callee_keeps_the_guard_the_record_claims(
    tmp_path: Path,
) -> None:
    """The isolating control: the same program through a USER callee.

    Swapping `array_length(a[0])` for a call to `consume(@Array<Pos> -> @Int)`
    changes nothing but the callee, and the callee is where the prologue is.
    A `tier3` here is backed by a loop in that function.
    """
    envelope = _verify(tmp_path, _USER_CALLEE, "user-callee")
    statuses = _refine_bind_statuses(envelope)
    assert statuses["tier3"] >= 1, (
        f"a user callee's element boundary lost its guarded record: "
        f"{statuses}"
    )
    loops = _element_loops(tmp_path, _USER_CALLEE, "user-callee")
    assert loops, (
        f"the record claims a runtime check and the module carries no "
        f"element loop: {loops}"
    )


def test_the_builtin_answer_is_the_one_the_nat_arm_gives(
    tmp_path: Path,
) -> None:
    """Depth x producer, one row further: a BUILT-IN callee.

    The `@Nat` arm has known since #1362 that a built-in bypasses the
    callee-prologue guard; the element arm learned it here, by asking the
    same predicate rather than by growing a builtin test of its own.  The
    cell compares the two arms on the same callee, so a future divergence is
    a red cell rather than a second discovery.
    """
    nat_source = (
        "private fn peek(@Array<Nat> -> @Int)\n"
        "  requires(array_length(@Array<Nat>.0) > 0)\n"
        "  ensures(true)\n  effects(pure)\n"
        "{\n  nat_to_int(@Array<Nat>.0[0])\n}\n\n"
        "public fn main(@Unit -> @Int)\n"
        "  requires(true)\n  ensures(true)\n  effects(pure)\n"
        "{\n  peek([1])\n}\n"
    )
    nat = _verify(tmp_path, nat_source, "nat-builtin")
    nat_guarded = {
        o["status"] for o in nat.get("obligations", [])
        if o["kind"] == "nat_bind"
    }
    element = _refine_bind_statuses(
        _verify(tmp_path, _BUILTIN_CALLEE, "element-builtin"))
    # Neither arm may claim a guarded Tier 3 at a built-in call argument.
    assert "tier3" not in element, element
    assert nat_guarded <= {"verified", "tier3_unguarded"}, (
        f"the `@Nat` arm claims a guard at a built-in call the element arm "
        f"declines: {nat_guarded}"
    )


def _allocating_predicate_program(elements: int = 16) -> str:
    """A `Map` carrier whose element predicate ALLOCATES, per element.

    The projected array is handed back by `map_values` and reachable from
    nothing else, so an allocation inside the walk is what could collect it.
    """
    inserts = "map_new()"
    for i in range(elements):
        inserts = f'map_insert({inserts}, "k{i}", {i + 1})'
    return (
        "private fn tag(@Int -> @String)\n"
        "  requires(true)\n  ensures(true)\n  effects(pure)\n"
        '{\n  string_concat(string_concat("value-", int_to_string(@Int.0)), '
        '"-padding-padding-padding")\n}\n\n'
        "type Tagged = { @Int | string_length(tag(@Int.0)) > 1 };\n\n"
        "private fn launder(@Int -> @Map<String, Int>)\n"
        "  requires(true)\n  ensures(true)\n  effects(pure)\n"
        f"{{\n  {inserts}\n}}\n\n"
        "private fn consume(@Map<String, Tagged> -> @Int)\n"
        "  requires(true)\n  ensures(true)\n  effects(pure)\n"
        "{\n  map_size(@Map<String, Tagged>.0)\n}\n\n"
        "public fn main(@Unit -> @Int)\n"
        "  requires(true)\n  ensures(true)\n  effects(pure)\n"
        "{\n  consume(launder(7))\n}\n"
    )


def test_the_projected_sequence_is_rooted_before_the_walk(
    tmp_path: Path,
) -> None:
    """The array a projection returns is on the SHADOW STACK before the walk.

    `map_values` allocates the array it hands back, and nothing else
    references it: a WASM local is not a GC root, so a per-element predicate
    that allocates could collect it mid-loop and the walk would read swept
    memory — the #593 / #1379 rule, at a pointer this PR introduced
    (CodeRabbit, PR #1447).

    Asserted STRUCTURALLY, and the reason is worth recording rather than
    dressing up: with the push removed, the allocating-predicate program
    below still runs to completion under `VERA_EAGER_GC=1` — over 16
    elements, with a per-element string built from two concatenations — so
    no program measured here observes the difference.  The collector does
    not hand the swept block back inside the walk's lifetime.  That makes
    the behavioural cell a weak instrument and the emitted-code one the
    honest instrument: the push is required by the invariant, not by a
    failure anyone has produced, and a cell that passed either way would
    read as coverage of something it does not cover.
    """
    source = _allocating_predicate_program()
    p = tmp_path / "alloc-pred.vera"
    p.write_text(source, encoding="utf-8")
    proc = _cli("compile", "--wat", str(p))
    assert proc.returncode == 0, proc.stderr[-500:]
    wat = proc.stdout
    call = wat.index("call $vera.map_values")
    loop = wat.index("loop $lp_elem", call)
    between = wat[call:loop]
    assert "$gc_sp" in between, (
        "the projected array is walked without being rooted: nothing between "
        f"the projection call and the loop touches the shadow stack:\n"
        f"{between[:400]}"
    )


def test_an_allocating_element_predicate_completes_under_eager_gc(
    tmp_path: Path,
) -> None:
    """And the walk itself survives a collection at every allocation.

    The behavioural half of the cell above: the predicate allocates twice per
    element, `VERA_EAGER_GC=1` collects at each one, and the program must
    still complete.  It passes with the root removed as well, which is why
    the cell above asserts the emitted code rather than this outcome.
    """
    source = _allocating_predicate_program()
    result = _run(tmp_path, source, "alloc-pred-eager", eager_gc=True)
    assert result.returncode == 0, (
        f"an allocating element predicate did not survive eager GC: "
        f"{result.stdout}{result.stderr}"
    )
    assert result.stdout.strip().endswith("16"), result.stdout


def test_the_carrier_sort_name_is_injective() -> None:
    """Two different carriers never share a sort name.

    An underscore is a character a Vera identifier may contain, so joining
    the element sorts on one is not injective: with a user `data A_B` and a
    user `data B_C` in scope, `Map<A_B, C>` and `Map<A, B_C>` both rendered
    `Map_A_B_C`, and two different carriers sharing one sort is a fact about
    either meeting a goal about the other (CodeRabbit, PR #1447).

    Asserted over a GENERATED product rather than the one pair that exposed
    it: every arrangement of names that can collide under a separator an
    identifier may contain is in the set, so a future separator change is
    tested against the property rather than against this example.
    """
    import itertools

    import z3

    from vera.smt import SmtContext

    smt = SmtContext()
    names = ["A", "C", "A_B", "B_C", "A_B_C", "Map", "Set"]
    sorts = {name: z3.DeclareSort(name) for name in names}
    rendered: dict[str, tuple[str, ...]] = {}
    for kind in ("Map", "Set"):
        arity = 2 if kind == "Map" else 1
        for combo in itertools.product(names, repeat=arity):
            key = smt.collection_sort_name(
                kind, tuple(sorts[n] for n in combo))
            assert key not in rendered, (
                f"{kind}{combo} and {kind}{rendered[key]} both render "
                f"`{key}`, so two carriers would share one sort"
            )
            rendered[key] = combo
    assert len(rendered) == len(names) ** 2 + len(names), len(rendered)


def test_two_colliding_carrier_types_verify_side_by_side(
    tmp_path: Path,
) -> None:
    """And the program the collision is reachable from verifies.

    A user ADT may be called `A_B`, so this is a program someone can write,
    not a property of the renderer alone: both maps' element facts stay
    usable and the forwarding one still discharges.
    """
    source = (
        "type Pos = { @Int | @Int.0 > 0 };\n\n"
        "private data A_B { MkAB(Int) }\n\n"
        "private data B_C { MkBC(Int) }\n\n"
        "private fn left(@Map<A_B, Pos> -> @Int)\n"
        "  requires(true)\n  ensures(true)\n  effects(pure)\n"
        "{\n  map_size(@Map<A_B, Pos>.0)\n}\n\n"
        "private fn right(@Map<Pos, B_C> -> @Int)\n"
        "  requires(true)\n  ensures(true)\n  effects(pure)\n"
        "{\n  map_size(@Map<Pos, B_C>.0)\n}\n\n"
        "private fn fwd_left(@Map<A_B, Pos> -> @Int)\n"
        "  requires(true)\n  ensures(true)\n  effects(pure)\n"
        "{\n  left(@Map<A_B, Pos>.0)\n}\n\n"
        "private fn fwd_right(@Map<Pos, B_C> -> @Int)\n"
        "  requires(true)\n  ensures(true)\n  effects(pure)\n"
        "{\n  right(@Map<Pos, B_C>.0)\n}\n\n"
        "public fn main(@Unit -> @Int)\n"
        "  requires(true)\n  ensures(true)\n  effects(pure)\n"
        "{\n  0\n}\n"
    )
    envelope = _verify(tmp_path, source, "colliding-carriers")
    assert envelope["ok"] is True, envelope.get("diagnostics")
    statuses = _refine_bind_statuses(envelope)
    assert set(statuses) == {"verified"}, statuses


# ---------------------------------------------------------------------------
# A binder that narrows BOTH ways at once (#1430; PR #1447 review)
# ---------------------------------------------------------------------------

_NESTED_BINDER = "type NonEmptyPos = { @Array<Pos> | array_length(@Array<Pos>.0) > 0 };\n\n"


def test_a_nested_refinement_at_a_clause_binder_does_not_overclaim(
    tmp_path: Path,
) -> None:
    """`{ @Array<Pos> | array_length(…) > 0 }` narrows twice, and the guard
    planted at a clause binder lowers the OUTER predicate only.

    Measured before this: the record read `tier3` — a claimed runtime check —
    while `[0 - 5]` satisfies the outer predicate (its length is 1), reaches
    the clause body at a type that forbids it, and the program runs to
    completion.  The check that existed covered half of what the record
    claimed, which is the guard-claim class one level in.

    The record now discloses, and the reason says which half is uncovered.
    Two controls bound it: the same binder at a PARAMETER is refused, and a
    plain refined clause binder with no element half keeps its `tier3`.
    """
    source = (
        "type Pos = { @Int | @Int.0 > 0 };\n\n" + _NESTED_BINDER +
        "public fn f(@Unit -> @Int)\n"
        "  requires(true)\n  ensures(true)\n  effects(pure)\n"
        "{\n  handle[Exn<Array<Int>>] {\n"
        "    throw(@NonEmptyPos) -> { 1 }\n"
        "  } in {\n    throw([0 - 5])\n  }\n}\n"
    )
    statuses = _refine_bind_statuses(_verify(tmp_path, source, "clause-nested"))
    assert statuses["tier3"] == 0, (
        f"the clause binder claims a runtime check that covers the outer "
        f"predicate only: {statuses}"
    )
    assert statuses["tier3_unguarded"] >= 1, statuses
    assert _element_loops(tmp_path, source, "clause-nested") == {}, (
        "no element walk is wired at this position, so any loop here is "
        "something else"
    )


def test_a_plain_refined_clause_binder_keeps_its_guard(
    tmp_path: Path,
) -> None:
    """The control for the cell above: no element half, no disclosure.

    `handle[Exn<Int>] { throw(@Pos) -> … }` is #1445/#1448's own shape — the
    binder's predicate IS lowered here — so it must still read `tier3` and
    still trap.  Without this, disclosing the nested shape could be achieved
    by disclosing every clause binder.
    """
    source = (
        "type Pos = { @Int | @Int.0 > 0 };\n\n"
        "public fn f(@Unit -> @Int)\n"
        "  requires(true)\n  ensures(true)\n  effects(pure)\n"
        "{\n  handle[Exn<Int>] {\n    throw(@Pos) -> { 1 }\n"
        "  } in {\n    throw(0 - 5)\n  }\n}\n"
    )
    statuses = _refine_bind_statuses(_verify(tmp_path, source, "clause-plain"))
    assert statuses["tier3"] >= 1, statuses
    result = _run(tmp_path, source, "clause-plain")
    assert result.returncode != 0, (
        f"the clause binder's own predicate is claimed and not checked: "
        f"{result.stdout}"
    )


def test_the_same_nested_binder_is_refused_at_a_boundary(
    tmp_path: Path,
) -> None:
    """And at a position the element walk IS wired at, it is refused.

    The nested shape is not inherently unguardable — it is unguarded at a
    clause binder — so the boundary twin is what says the disclosure above is
    about the position rather than about the type.
    """
    source = (
        "type Pos = { @Int | @Int.0 > 0 };\n\n" + _NESTED_BINDER +
        "private fn consume(@NonEmptyPos -> @Int)\n"
        "  requires(true)\n  ensures(true)\n  effects(pure)\n"
        "{\n  array_length(@NonEmptyPos.0)\n}\n\n"
        "private fn launder(@Int -> @Array<Int>)\n"
        "  requires(true)\n  ensures(true)\n  effects(pure)\n"
        "{\n  array_append([], @Int.0)\n}\n\n"
        "public fn main(@Unit -> @Int)\n"
        "  requires(true)\n  ensures(true)\n  effects(pure)\n"
        "{\n  consume(launder(0 - 5))\n}\n"
    )
    envelope = _verify(tmp_path, source, "param-nested")
    assert envelope["ok"] is False, envelope
    result = _run(tmp_path, source, "param-nested")
    assert result.returncode != 0, result.stdout


_TWO_MAP_RESULTS = (
    "type Pos = { @Int | @Int.0 > 0 };\n\n"
    "type NonEmpty = { @String | string_length(@String.0) > 0 };\n\n"
    "private fn make(@Unit -> @Map<String, Pos>)\n"
    "  requires(true)\n  ensures(true)\n  effects(pure)\n"
    '{\n  map_insert(map_new(), "a", 5)\n}\n\n'
    "private fn make2(@Unit -> @Map<String, NonEmpty>)\n"
    "  requires(true)\n  ensures(true)\n  effects(pure)\n"
    '{\n  map_insert(map_new(), "a", "x")\n}\n\n'
    "private fn consume(@Map<String, Pos> -> @Int)\n"
    "  requires(true)\n  ensures(true)\n  effects(pure)\n"
    "{\n  map_size(@Map<String, Pos>.0)\n}\n\n"
    "private fn consume2(@Map<String, NonEmpty> -> @Int)\n"
    "  requires(true)\n  ensures(true)\n  effects(pure)\n"
    "{\n  map_size(@Map<String, NonEmpty>.0)\n}\n\n"
    "public fn main(@Unit -> @Int)\n"
    "  requires(true)\n  ensures(true)\n  effects(pure)\n"
    "{\n  consume(make(())) + consume2(make2(()))\n}\n"
)


def test_a_carrier_returning_callee_hands_back_a_usable_element_fact(
    tmp_path: Path,
) -> None:
    """A `Map`-returning call is declared in its CARRIER sort.

    `_get_or_create_adt_sort` has no entry for the built-in containers, so
    such a result fell through `declare_adt` to `declare_int` — an
    unconstrained integer, which the projection declines — and a callee's
    element facts were unusable at its call site (CodeRabbit, PR #1447).
    Declared through the carrier seam, the fact crosses the call.
    """
    envelope = _verify(tmp_path, _TWO_MAP_RESULTS, "map-result")
    assert envelope["ok"] is True, envelope.get("diagnostics")
    statuses = _refine_bind_statuses(envelope)
    assert statuses["verified"] >= 1, (
        f"no element fact survived a carrier-returning call: {statuses}"
    )
    assert statuses["violated"] == 0, statuses


def test_two_carrier_returning_callees_do_not_share_a_sort(
    tmp_path: Path,
) -> None:
    """Two `Map<String, …>` results with DIFFERENT element types, one module.

    The cache key for a projection includes the element sort, so the second
    callee cannot be handed the first's symbol — a sort error waiting for
    whichever program declared two such callees.  The cell runs the program
    as well, because a Z3 sort mismatch surfaces as a crash rather than as a
    status.
    """
    envelope = _verify(tmp_path, _TWO_MAP_RESULTS, "two-results")
    assert not envelope.get("diagnostics"), envelope["diagnostics"]
    result = _run(tmp_path, _TWO_MAP_RESULTS, "two-results-run")
    assert result.returncode == 0, f"{result.stdout}{result.stderr}"
    assert result.stdout.strip().endswith("2"), result.stdout
