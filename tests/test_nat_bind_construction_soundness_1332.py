"""#1332: a `@Nat` tuple-component narrowing at CONSTRUCTION is obligated, never assumed.

`let @Tuple<Nat, Int> = Tuple(@Int.0, 5);` narrows the `@Int` parameter into a
`@Nat` component.  That narrowing is an OBLIGATION — nothing has established the
parameter is non-negative — and the identical construction in return position
reports it as one (`violated`/E503, counterexample `@Int.0 = -1`).  Written as a
`let` and then destructured, it verified as **proved** while the compiled program
trapped on `-1`: the #392-class false Tier-1, a proof whose guard fires.

THE CIRCULARITY.  Translating the body's `match` calls
`_subpattern_source_facts`, which reads a `@Nat` sub-pattern binder and emits the
fact "this component is `>= 0`" from the scrutinee's DECLARED type.  A single
irrefutable arm has no preceding conditions, so `_translate_match` asserts that
fact **unconditionally at the solver's base level** — where it is visible to every
later obligation, including ones at program points BEFORE the match.  The
scrutinee's Z3 term is literally `Tuple(@Int.0, 5)`, so the datatype accessor
axiom reduces the fact to `@Int.0 >= 0` — exactly the goal the construction site
must prove.  The obligation discharged itself.

That fact is true at run time only because codegen plants a trapping guard at the
destructure, so using it to prove the guard can never fire assumes the
conclusion.  `_subpattern_source_facts` already carries the anti-circularity
guard — it returns no facts for a literal-constructor scrutinee, "concrete args,
not accessors" — but the test was SYNTACTIC (is the scrutinee AST a
`ConstructorCall`?) where the defect is SEMANTIC: a slot reference to a let-bound
tuple is not syntactically a constructor call, yet its term is one.

WHY THE CELLS ARE PAIRED.  A verdict alone cannot separate the fix from
over-rejection, so every cell below pins the verdict against a control that must
NOT move: the precondition-discharged form still proves and still runs, the
return-position form is unchanged in both directions, and the two construction
spellings — with and without the destructure — must agree with each other, which
is the internal inconsistency the bug consisted of.  The soundness differential
is the one TESTING.md prescribes for this class: verify-says-proved together
with a run that traps is the bug itself, so the two are asserted in ONE test
rather than split across siblings where each half could pass alone.

TWO OVER-REJECTION CONTROLS straddle the guard, because neither alone shows the
fix is both wide enough and narrow enough — one where the guard FIRES (a tuple
built from an already-`@Nat` parameter, which must still prove) and one where it
does NOT (an opaque `@Tuple<Nat, Int>` parameter, whose declared source facts
must survive).  The refutable two-arm sibling is here too: it was already
correct, which pins the defect to the irrefutable single-arm shape rather than
to `solver.add` in general.
"""

from __future__ import annotations

import json
import os
import re
import subprocess
import sys
import textwrap
from pathlib import Path

import pytest

import vera

# The subprocess must run the SAME compiler this session imported: in a linked
# git worktree `python -m vera.cli` would otherwise resolve the tree the
# editable install points at, and every cell would report on a compiler nobody
# edited.  A no-op wherever the two coincide.
_PKG_PARENT = str(Path(vera.__file__).resolve().parents[1])

# The tuple's second component.  A distinctive value that coincides with no
# default, no counterexample Z3 reaches for, and no Nat boundary — so a fact
# read off the WRONG component cannot look like the right answer.
_SECOND = 1234

# The negative input.  Deliberately not -1: that is the counterexample Z3
# reports, and an assertion that happened to match it would not distinguish a
# real trap from an echo of the diagnostic.
_NEGATIVE = -7
_POSITIVE = 7


def _construction(requires: str) -> str:
    """The repro: narrow into a `@Nat` tuple component, then destructure it."""
    return textwrap.dedent(f"""\
        public fn f(@Int -> @Int)
          requires({requires}) ensures(true) effects(pure)
        {{
          let @Tuple<Nat, Int> = Tuple(@Int.0, {_SECOND});
          match @Tuple<Nat, Int>.0 {{ Tuple(@Nat, @Int) -> nat_to_int(@Nat.0) }}
        }}
        """)


def _construction_no_destructure(requires: str) -> str:
    """The same construction with no `match` — the form that always reported it."""
    return textwrap.dedent(f"""\
        public fn f(@Int -> @Int)
          requires({requires}) ensures(true) effects(pure)
        {{
          let @Tuple<Nat, Int> = Tuple(@Int.0, {_SECOND});
          {_SECOND}
        }}
        """)


def _return_position(requires: str) -> str:
    """The control the issue names: the identical narrowing in return position."""
    return textwrap.dedent(f"""\
        public fn mk(@Int -> @Tuple<Nat, Int>)
          requires({requires}) ensures(true) effects(pure)
        {{
          Tuple(@Int.0, {_SECOND})
        }}
        """)


def _cli(*args: str) -> subprocess.CompletedProcess[str]:
    env = dict(os.environ)
    existing = env.get("PYTHONPATH", "")
    env["PYTHONPATH"] = (
        f"{_PKG_PARENT}{os.pathsep}{existing}" if existing else _PKG_PARENT
    )
    return subprocess.run(
        [sys.executable, "-m", "vera.cli", *args],
        capture_output=True, text=True, encoding="utf-8", check=False,
        env=env, timeout=300,
    )


def _verify(tmp_path: Path, source: str, name: str = "p.vera") -> dict:
    """`vera verify --json` for *source*, as a dict.

    A crash or non-JSON stdout is surfaced as itself rather than as a bare
    `JSONDecodeError`: these cells exist to report what the verifier said.
    """
    p = tmp_path / name
    p.write_text(source, encoding="utf-8")
    proc = _cli("verify", "--json", str(p))
    try:
        return json.loads(proc.stdout)
    except json.JSONDecodeError:  # pragma: no cover — diagnostic path
        raise AssertionError(
            f"verify emitted no JSON (exit {proc.returncode})\n"
            f"stdout: {proc.stdout[:2000]}\nstderr: {proc.stderr[:2000]}"
        ) from None


def _nat_binds(result: dict) -> list[dict]:
    return [o for o in result["obligations"] if o["kind"] == "nat_bind"]


def _sole_nat_bind(result: dict) -> dict:
    """The one `nat_bind` obligation, asserted to be the only one.

    Position matters here: a fix that merely ADDED a second, violated
    obligation beside the falsely-verified one would satisfy a
    "some obligation is violated" assertion while leaving the false
    Tier-1 in place.
    """
    binds = _nat_binds(result)
    assert len(binds) == 1, (
        f"expected exactly one nat_bind, got {len(binds)}: "
        f"{[(b['status'], b.get('description')) for b in binds]}"
    )
    return binds[0]


def _run(tmp_path: Path, source: str, arg: int,
         fn: str = "f", name: str = "p.vera") -> subprocess.CompletedProcess[str]:
    p = tmp_path / name
    p.write_text(source, encoding="utf-8")
    return _cli("run", str(p), "--fn", fn, "--", str(arg))


#: What a tripped `@Int` -> `@Nat` narrowing guard says.  Since #754 the guard
#: signals `vera.nat_guard_trap` before its `unreachable`, so the trap carries
#: its own kind and its own message instead of the generic instruction name —
#: which is a STRONGER reading here, not merely a different one: "unreachable"
#: also matches a non-exhaustive match and a shadow-stack overflow, either of
#: which would have read as "the narrowing guard fired".
_NAT_GUARD_TRAP = "Negative value bound into a @Nat slot"


def _traps(proc: subprocess.CompletedProcess[str]) -> bool:
    """ANY trap — for the cells asserting that none occurs.

    Deliberately broad on that side: a cell claiming a proved narrowing does
    not trap must fail on an unexpected trap of any kind, so widening this
    predicate makes those assertions stronger, not weaker.
    """
    out = proc.stdout + proc.stderr
    return proc.returncode != 0 and (
        _NAT_GUARD_TRAP in out or "unreachable" in out
    )


def _traps_on_the_narrowing_guard(
    proc: subprocess.CompletedProcess[str],
) -> bool:
    """The NARROWING guard specifically — for the cells expecting it.

    `_traps` accepts a bare `unreachable`, which is also what a
    non-exhaustive match, a compiler assertion and a shadow-stack overflow
    produce.  Used on the expecting side it would let a regression that
    removes the `vera.nat_guard_trap` signal — the exact thing #754 added —
    pass as a guard that fired (PR review).
    """
    out = proc.stdout + proc.stderr
    return proc.returncode != 0 and _NAT_GUARD_TRAP in out


# ---------------------------------------------------------------------------
# 1. The bug itself
# ---------------------------------------------------------------------------

def test_construction_narrowing_is_not_falsely_verified(tmp_path: Path) -> None:
    """The construction obligation is `violated`/E503, not `verified`.

    Nothing in `requires(true)` establishes `@Int.0 >= 0`, so the narrowing
    cannot be proved; reporting it proved is the false Tier-1.
    """
    result = _verify(tmp_path, _construction("true"))
    bind = _sole_nat_bind(result)
    assert bind["status"] == "violated", (
        f"construction nat_bind reported {bind['status']!r} — a proof of a "
        f"narrowing nothing establishes (#1332)"
    )
    assert bind.get("error_code") == "E503"
    assert result["ok"] is False
    assert "E503" in [d.get("error_code") for d in result["diagnostics"]]


def test_the_refutation_names_a_negative_counterexample(tmp_path: Path) -> None:
    """The counterexample witnesses the violation rather than filling a default.

    A model completed with an arbitrary `@Int.0 = 0` would satisfy `>= 0` and
    witness nothing, so the SIGN is the assertion.  The value is carried by the
    E503 diagnostic (the obligation's own JSON record reports status and code
    only), which is also where a reader meets it.
    """
    result = _verify(tmp_path, _construction("true"))
    e503 = [d for d in result["diagnostics"] if d.get("error_code") == "E503"]
    assert len(e503) == 1, f"expected one E503, got {len(e503)}"
    text = e503[0].get("description", "")
    match = re.search(r"@Int\.0 = (-?\d+)", text)
    assert match, f"no @Int.0 counterexample in the diagnostic: {text!r}"
    assert int(match.group(1)) < 0, (
        f"counterexample does not witness the violation: {text!r}"
    )


# ---------------------------------------------------------------------------
# 2. The over-rejection control — the fix must not cost provable programs
# ---------------------------------------------------------------------------

def test_precondition_discharges_the_construction_narrowing(tmp_path: Path) -> None:
    """With `requires(@Int.0 >= 0)` the same construction still proves.

    This is the cell a blunt fix (drop the facts, obligate everything) fails:
    the narrowing IS provable here, from the precondition rather than from
    itself.
    """
    result = _verify(tmp_path, _construction("@Int.0 >= 0"))
    bind = _sole_nat_bind(result)
    assert bind["status"] == "verified", (
        f"a precondition-discharged narrowing reported {bind['status']!r} — "
        f"the fix over-rejects"
    )
    assert result["ok"] is True
    assert result["diagnostics"] == []


def test_precondition_discharged_program_runs(tmp_path: Path) -> None:
    """And it still compiles and runs, returning the narrowed value."""
    proc = _run(tmp_path, _construction("@Int.0 >= 0"), _POSITIVE)
    assert proc.returncode == 0, f"stdout={proc.stdout}\nstderr={proc.stderr}"
    assert proc.stdout.strip() == str(_POSITIVE)


# ---------------------------------------------------------------------------
# 3. The return-position control — correct before and after
# ---------------------------------------------------------------------------

def test_return_position_control_unchanged(tmp_path: Path) -> None:
    """The reference behaviour the construction site must match."""
    result = _verify(tmp_path, _return_position("true"), name="r.vera")
    bind = _sole_nat_bind(result)
    assert bind["status"] == "violated"
    assert bind.get("error_code") == "E503"


def test_return_position_discharges_under_precondition(tmp_path: Path) -> None:
    """Its positive control, so the return-position pair is pinned both ways."""
    result = _verify(tmp_path, _return_position("@Int.0 >= 0"), name="r.vera")
    assert _sole_nat_bind(result)["status"] == "verified"


# ---------------------------------------------------------------------------
# 4. The two construction spellings must agree with each other
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("requires,expected", [
    ("true", "violated"),
    ("@Int.0 >= 0", "verified"),
])
def test_destructure_does_not_change_the_construction_verdict(
    tmp_path: Path, requires: str, expected: str,
) -> None:
    """Adding a `match` that destructures the tuple cannot change whether the
    CONSTRUCTION was provable.

    This is the inconsistency the bug consisted of: the same construction under
    the same contract reported `violated` without the destructure and
    `verified` with it.  Asserted as an agreement between two runs of the same
    compiler, so it needs no external oracle.
    """
    with_match = _sole_nat_bind(
        _verify(tmp_path, _construction(requires), name="a.vera"))
    without_match = _sole_nat_bind(
        _verify(tmp_path, _construction_no_destructure(requires), name="b.vera"))
    assert with_match["status"] == without_match["status"] == expected, (
        f"destructured={with_match['status']!r} "
        f"bare={without_match['status']!r} — the destructure changed the "
        f"verdict on a narrowing that happens before it"
    )


def test_construction_agrees_with_return_position(tmp_path: Path) -> None:
    """The issue's own control: the same narrowing, two positions, one verdict."""
    construction = _sole_nat_bind(
        _verify(tmp_path, _construction("true"), name="a.vera"))
    ret = _sole_nat_bind(
        _verify(tmp_path, _return_position("true"), name="r.vera"))
    assert construction["status"] == ret["status"] == "violated"


# ---------------------------------------------------------------------------
# 5. The soundness differential: proved-and-trapping must be impossible
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("requires", ["true", "@Int.0 >= 0"])
def test_a_proved_narrowing_never_traps(tmp_path: Path, requires: str) -> None:
    """`vera verify` clean and `vera run` trapping cannot both hold.

    The TESTING.md soundness rule for this class: a proved obligation whose
    runtime guard fires is the contradiction, so the verdict and the run are
    asserted together in ONE test.  Pre-fix the `requires(true)` cell fails
    exactly here — verify clean, run trapping.

    Non-vacuous by construction: the `@Int.0 >= 0` cell IS verify-clean, so the
    implication is exercised with a true antecedent rather than passing only
    because nothing verifies.
    """
    source = _construction(requires)
    result = _verify(tmp_path, source)
    verify_clean = result["ok"] is True

    if not verify_clean:
        # Refused — the compiler made no claim, so there is nothing to
        # contradict.  Pin that it refused for the reason under test.
        assert "E503" in [d.get("error_code") for d in result["diagnostics"]]
        return

    # Verify claims the narrowing is proved.  The guard must therefore be
    # unreachable for every input the contract admits.
    admitted = _POSITIVE if requires != "true" else _NEGATIVE
    proc = _run(tmp_path, source, admitted)
    assert not _traps(proc), (
        f"verify proved the narrowing and the program trapped at "
        f"{admitted} — a false Tier-1 (#1332)\n"
        f"stdout={proc.stdout}\nstderr={proc.stderr}"
    )


def test_the_negative_input_really_reaches_the_guard(tmp_path: Path) -> None:
    """The trap the differential watches for is real and reachable.

    Without this, the differential above could pass because the input never
    reaches the guard rather than because the guard is unreachable.  `requires(true)` admits
    `-7`, the program compiles, and the run traps — which is what makes
    `verified` a lie rather than a harmless imprecision.
    """
    proc = _run(tmp_path, _construction("true"), _NEGATIVE)
    assert _traps_on_the_narrowing_guard(proc), (
        f"expected a trap at {_NEGATIVE}\n"
        f"exit={proc.returncode} stdout={proc.stdout}\nstderr={proc.stderr}"
    )


def test_the_positive_input_returns_the_narrowed_value(tmp_path: Path) -> None:
    """And the same program answers correctly where the narrowing holds."""
    proc = _run(tmp_path, _construction("true"), _POSITIVE)
    assert proc.returncode == 0, f"stdout={proc.stdout}\nstderr={proc.stderr}"
    assert proc.stdout.strip() == str(_POSITIVE)


def test_refined_component_narrowing_is_also_obligated(tmp_path: Path) -> None:
    """The refined-type sibling, which shares the code path — and was worse.

    `_subpattern_source_facts_term` reads a REFINED binder's predicate from the
    same declared source type, so a refinement carried the identical
    circularity: `let @Tuple<PosInt, Int> = Tuple(@Int.0, N)` verified its
    `refine_bind` as PROVED.  The `@Nat` case at least trapped; this one
    returns a wrong ANSWER, because a refined tuple component carries no
    runtime guard at all — pre-fix `vera run --fn f -- -7` printed `-7`, a
    value the program's own type says is positive, from a verify-clean build.

    Now refused as E505, which is the same repair reaching a second obligation
    kind rather than a separate one.
    """
    source = textwrap.dedent(f"""\
        type PosInt = {{ @Int | @Int.0 > 0 }};

        public fn f(@Int -> @Int)
          requires(true) ensures(true) effects(pure)
        {{
          let @Tuple<PosInt, Int> = Tuple(@Int.0, {_SECOND});
          match @Tuple<PosInt, Int>.0 {{ Tuple(@PosInt, @Int) -> @PosInt.0 }}
        }}
        """)
    result = _verify(tmp_path, source, name="ref.vera")
    binds = [o for o in result["obligations"] if o["kind"] == "refine_bind"]
    assert len(binds) == 1, f"expected one refine_bind, got {binds}"
    assert binds[0]["status"] == "violated", (
        f"refined construction narrowing reported {binds[0]['status']!r}"
    )
    assert result["ok"] is False
    assert "E505" in [d.get("error_code") for d in result["diagnostics"]]


def test_refined_component_still_proves_under_its_precondition(
    tmp_path: Path,
) -> None:
    """And the refined sibling's over-rejection control."""
    source = textwrap.dedent(f"""\
        type PosInt = {{ @Int | @Int.0 > 0 }};

        public fn f(@Int -> @Int)
          requires(@Int.0 > 0) ensures(true) effects(pure)
        {{
          let @Tuple<PosInt, Int> = Tuple(@Int.0, {_SECOND});
          match @Tuple<PosInt, Int>.0 {{ Tuple(@PosInt, @Int) -> @PosInt.0 }}
        }}
        """)
    result = _verify(tmp_path, source, name="ref.vera")
    binds = [o for o in result["obligations"] if o["kind"] == "refine_bind"]
    assert binds and all(b["status"] == "verified" for b in binds), (
        f"a precondition-discharged refined narrowing was refused: {binds}"
    )
    assert result["ok"] is True


def test_multi_arm_construction_was_and_stays_refused(tmp_path: Path) -> None:
    """The refutable sibling, which was already correct — and must stay so.

    With two arms the fact is asserted as `arm-matched => fact` rather than
    unconditionally, and this shape reported `violated`/E503 before the fix as
    well.  It marks the boundary of the defect: had the fix been written at
    `_translate_match`'s unconditional `solver.add` instead of at the fact
    source, this cell and the falsely-verified one would disagree about what
    was repaired.
    """
    source = textwrap.dedent(f"""\
        public fn f(@Int -> @Int)
          requires(true) ensures(true) effects(pure)
        {{
          let @Option<Nat> = Some(@Int.0);
          match @Option<Nat>.0 {{ Some(@Nat) -> nat_to_int(@Nat.0), None -> {_SECOND} }}
        }}
        """)
    result = _verify(tmp_path, source, name="o.vera")
    assert _sole_nat_bind(result)["status"] == "violated"
    assert "E503" in [d.get("error_code") for d in result["diagnostics"]]


# ---------------------------------------------------------------------------
# 6. The fact that caused it is still available where it IS established
# ---------------------------------------------------------------------------

def test_already_nat_component_still_proves_through_the_destructure(
    tmp_path: Path,
) -> None:
    """The guard FIRES here, and nothing is lost.

    The strongest over-rejection control: the scrutinee IS a constructor
    application, so the fix drops its source facts — but the component came
    from a `@Nat` PARAMETER, so no narrowing happened and the postcondition
    still needs the component's sign.  It proves, because the parameter's own
    Z3 variable carries `>= 0` from its declaration; the dropped fact was
    redundant, which is the claim the fix rests on.

    Distinct from the opaque-scrutinee cell below, where the guard does NOT
    fire — this one exercises the dropped path directly.
    """
    source = textwrap.dedent(f"""\
        public fn f(@Nat -> @Int)
          requires(true) ensures(@Int.result >= 0) effects(pure)
        {{
          let @Tuple<Nat, Int> = Tuple(@Nat.0, {_SECOND});
          match @Tuple<Nat, Int>.0 {{ Tuple(@Nat, @Int) -> nat_to_int(@Nat.0) }}
        }}
        """)
    result = _verify(tmp_path, source, name="n.vera")
    assert result["ok"] is True, (
        f"a construction from an already-@Nat value was refused: "
        f"{[d.get('error_code') for d in result['diagnostics']]}"
    )
    assert all(o["status"] != "violated" for o in result["obligations"])


def test_opaque_scrutinee_still_carries_its_declared_facts(tmp_path: Path) -> None:
    """A `@Nat` component of a PARAMETER keeps its source-type fact.

    The parameter's declared type establishes the component's sign — no
    construction in this function put it there — so the sub-pattern fact is
    sound and must survive the fix.  Measured by a postcondition that only
    holds if the fact is available: the bound `@Nat` widens back to a
    non-negative `@Int`.
    """
    source = textwrap.dedent("""\
        public fn g(@Tuple<Nat, Int> -> @Int)
          requires(true) ensures(@Int.result >= 0) effects(pure)
        {
          match @Tuple<Nat, Int>.0 { Tuple(@Nat, @Int) -> nat_to_int(@Nat.0) }
        }
        """)
    result = _verify(tmp_path, source, name="g.vera")
    assert result["ok"] is True, (
        f"an established source-type fact was lost: "
        f"{[d.get('error_code') for d in result['diagnostics']]}"
    )
    assert all(o["status"] != "violated" for o in result["obligations"])


# ---------------------------------------------------------------------------
# 7. The laundering matrix: every way of PRODUCING the scrutinee
# ---------------------------------------------------------------------------
#
# A guard that asks "is this term literally `C(args)`" is defeated by anything
# that wraps the construction.  The first version of this fix was: an `if`
# producing the tuple launders straight past it, and both invariants named
# above — the destructure not changing the verdict, and construction agreeing
# with return position — break on that six-line program.  So the suite is
# parametrised over SCRUTINEE SHAPE rather than carrying one spelling, because
# a single shape can only ever pin the spelling someone happened to think of.
#
# Each shape is paired with a family (`@Nat` and refined) since the two travel
# through different obligation kinds.  The refined one had no runtime guard at
# all when this suite was written; #765 gave it one at the pattern binds and
# #1426 at the construction positions, so both families are now checked at run
# time and the differential below reads the same either way.

_FAMILY = {
    # family: (prelude, component type, binder, arm body, obligation kind)
    "nat": ("", "Nat", "@Nat", "nat_to_int(@Nat.0)", "nat_bind"),
    "refined": ("type PosInt = { @Int | @Int.0 > 0 };\n\n", "PosInt",
                "@PosInt", "@PosInt.0", "refine_bind"),
}

# A helper whose OWN construction obligation is discharged internally (it
# builds from a literal), so its result's component fact is legitimately
# grounded by the declared return type.  This is the boundary the guard must
# respect: a call-produced value's facts are established elsewhere, a locally
# constructed value's are still outstanding.
_MK = ("private fn mk(@Int -> @Tuple<{comp}, Int>)\n"
       "  requires(true) ensures(true) effects(pure)\n"
       "{{\n  Tuple(7, 9)\n}}\n\n")

_LETS = {
    "bare_ctor": "  let @{T} = Tuple(@Int.0, 5);\n",
    # The branch that defeated the first guard.
    "ite_both_ctor": ("  let @{T} = if @Int.0 > 100 then {{ Tuple(@Int.0, 5) }}"
                      " else {{ Tuple(@Int.0, 6) }};\n"),
    # One constructed arm, one call-produced.  `< 100` so a negative input
    # reaches the CONSTRUCTED arm — under `> 100` that arm is guarded by a
    # condition already implying non-negativity and measures nothing.
    "ite_mixed": ("  let @{T} = if @Int.0 < 100 then {{ Tuple(@Int.0, 5) }}"
                  " else {{ mk(@Int.0) }};\n"),
    "match_produced": ("  let @{T} = match @Int.0 > 100 {{"
                       " true -> Tuple(@Int.0, 5),"
                       " false -> Tuple(@Int.0, 6) }};\n"),
    "let_of_let": ("  let @{T} = Tuple(@Int.0, 5);\n"
                   "  let @{T} = @{T}.0;\n"),
    # CONTROL: grounded elsewhere, so the facts must be KEPT.
    "call_produced": "  let @{T} = mk(@Int.0);\n",
}

_LAUNDERABLE = ["bare_ctor", "ite_both_ctor", "ite_mixed", "match_produced",
                "let_of_let"]


def _shaped(shape: str, family: str) -> str:
    prelude, comp, binder, body, _kind = _FAMILY[family]
    T = f"Tuple<{comp}, Int>"
    helper = (_MK.format(comp=comp)
              if shape in ("ite_mixed", "call_produced") else "")
    let = _LETS[shape].format(T=T)
    return (
        f"{prelude}{helper}"
        f"public fn f(@Int -> @Int)\n"
        f"  requires(true) ensures(true) effects(pure)\n"
        f"{{\n{let}"
        f"  match @{T}.0 {{ Tuple({binder}, @Int) -> {body} }}\n}}\n"
    )


@pytest.mark.parametrize("shape", _LAUNDERABLE)
@pytest.mark.parametrize("family", ["nat", "refined"])
def test_no_shape_launders_the_construction_obligation(
    tmp_path: Path, shape: str, family: str,
) -> None:
    """However the scrutinee is produced, a local construction stays obligated.

    Red at `600f5ac5` for `ite_both_ctor` and `match_produced` (both families:
    reported `verified`, and the `@Nat` pair trapped at run time while the
    refined pair returned a value its own type forbids), and for `ite_mixed`,
    which crashed the verifier outright.
    """
    kind = _FAMILY[family][4]
    result = _verify(tmp_path, _shaped(shape, family), name="s.vera")
    binds = [o for o in result["obligations"] if o["kind"] == kind]
    assert binds, f"{shape}/{family}: no {kind} obligation was recorded at all"
    assert any(o["status"] == "violated" for o in binds), (
        f"{shape}/{family}: {[o['status'] for o in binds]} — a narrowing "
        f"nothing establishes was not refuted"
    )
    assert result["ok"] is False


@pytest.mark.parametrize("shape", _LAUNDERABLE)
@pytest.mark.parametrize("family", ["nat", "refined"])
def test_no_shape_is_proved_and_then_wrong(
    tmp_path: Path, shape: str, family: str,
) -> None:
    """The soundness differential, over every shape.

    Verify-clean must imply the program is right on the value the narrowing
    forbids, and BOTH halves are asserted for both families: no trap, and not
    returning the forbidden value.  When this was written the refined family
    had no runtime guard, so only the second half could bite for it; since
    #765 and #1426 it is guarded too, and a proved program that trapped would
    be just as much a contradiction there.
    """
    source = _shaped(shape, family)
    result = _verify(tmp_path, source, name="s.vera")
    if result["ok"] is not True:
        return  # refused: the compiler made no claim to contradict
    proc = _run(tmp_path, source, _NEGATIVE, name="s.vera")
    assert not _traps(proc), f"{shape}/{family}: proved, and trapped"
    assert proc.stdout.strip() != str(_NEGATIVE), (
        f"{shape}/{family}: proved, and returned {_NEGATIVE} — a value the "
        f"program's own type forbids"
    )


@pytest.mark.parametrize("family", ["nat", "refined"])
def test_a_call_produced_scrutinee_keeps_its_facts(
    tmp_path: Path, family: str,
) -> None:
    """CONTROL: the over-rejection boundary.

    `mk`'s result is grounded by its declared return type — its own
    construction obligation was discharged inside `mk` — so the facts are
    legitimate here and must survive.  Without this cell the matrix above
    would be satisfied by a guard that simply dropped every fact.
    """
    result = _verify(tmp_path, _shaped("call_produced", family), name="c.vera")
    assert result["ok"] is True, (
        f"{family}: a grounded scrutinee was refused — "
        f"{[d.get('error_code') for d in result['diagnostics']]}"
    )
    assert all(o["status"] != "violated" for o in result["obligations"])


# ---------------------------------------------------------------------------
# 8. The arm reading itself: `any` over the ITE arms, not `all`
# ---------------------------------------------------------------------------

def test_a_mixed_branch_launders_under_an_all_reading(tmp_path: Path) -> None:
    """Pins `any` over the ITE arms — nothing else in this file does.

    WHY THE `ite_mixed` CELL ABOVE CANNOT PIN IT.  That shape joins a locally
    built `Tuple<Int, Int>` with a callee's declared `Tuple<Int, Nat>`; the two
    are distinct Z3 sorts, so `_translate_if` declines the join and the guard
    is never reached with a mixed term at all.  It passes under either reading
    for a reason that has nothing to do with the reading.

    So this cell uses a non-generic single-constructor ADT, where both arms
    genuinely share one sort and the predicate really is consulted.

    AND THE CONSTRUCTING ARM IS THE `else`.  Under `> 100` in the `then`, the
    arm's own path condition already implies non-negativity and the obligation
    discharges legitimately — a fixture structurally incapable of showing
    laundering, which is the trap the `ite_mixed` comment above warns about.
    In the `else` the path condition is `@Int.0 <= 100`, which admits the
    negative.

    Measured: under an `all` reading this verifies clean and then traps; under
    the shipped `any` it is `violated`/E503.
    """
    source = textwrap.dedent("""\
        private data Box { MkBox(Nat, Int) }

        private fn mk(@Int -> @Box)
          requires(true) ensures(true) effects(pure)
        {
          MkBox(7, 9)
        }

        public fn f(@Int -> @Int)
          requires(true) ensures(true) effects(pure)
        {
          let @Box = if @Int.0 > 100 then { mk(@Int.0) } else { MkBox(@Int.0, 5) };
          match @Box.0 { MkBox(@Nat, @Int) -> nat_to_int(@Nat.0) }
        }
        """)
    result = _verify(tmp_path, source, name="box.vera")
    bind = _sole_nat_bind(result)
    assert bind["status"] == "violated", (
        f"the constructing arm's narrowing reported {bind['status']!r} — an "
        f"`all` reading over the branch arms assumes what it must prove"
    )
    assert "E503" in [d.get("error_code") for d in result["diagnostics"]]
    assert result["ok"] is False


def test_the_mixed_branch_traps_when_it_is_believed(tmp_path: Path) -> None:
    """The other half: the value that makes the `all` reading a false Tier-1.

    Asserted separately from the verdict because the trap is what proves the
    verdict matters — `-7` reaches the constructed arm and the destructure
    guard fires.
    """
    source = textwrap.dedent("""\
        private data Box { MkBox(Nat, Int) }

        private fn mk(@Int -> @Box)
          requires(true) ensures(true) effects(pure)
        {
          MkBox(7, 9)
        }

        public fn f(@Int -> @Int)
          requires(true) ensures(true) effects(pure)
        {
          let @Box = if @Int.0 > 100 then { mk(@Int.0) } else { MkBox(@Int.0, 5) };
          match @Box.0 { MkBox(@Nat, @Int) -> nat_to_int(@Nat.0) }
        }
        """)
    proc = _run(tmp_path, source, _NEGATIVE, name="box.vera")
    assert _traps_on_the_narrowing_guard(proc), (
        f"expected the destructure guard to fire at {_NEGATIVE}\n"
        f"exit={proc.returncode} stdout={proc.stdout}\nstderr={proc.stderr}"
    )
