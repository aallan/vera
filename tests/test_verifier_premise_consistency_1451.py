"""A function's premise set is checked for satisfiability before it is trusted
(#1451).

An UNSAT premise set discharges every obligation in the function VACUOUSLY:
`Not(goal)` is unsatisfiable alongside contradictory assumptions whatever the
goal is, so `check_valid` answers `verified` for all of them and the summary
reports Tier 1.  `requires(@Int.0 > 5 && @Int.0 < 3)` over a body returning `0`
proved `ensures(@Int.result == 42)` at Tier 1, exit 0, no diagnostic.

The premise set is not built only from `requires`.  It carries param-type
constraints, refinement predicates, refined-return assumptions and injected
call facts, and ANY of those going over-strong produces the same silent, total
false Tier 1 — indistinguishable in the output from a real proof.  The codebase
already knew the failure mode and defended against two specific producers (the
unmodelled-base refined-return refusal and #953's path-guarded call facts, both
documented in `vera/smt.py`); there was no general check, so every new premise
source reintroduced the class.

Two layers, so the diagnostic can name the culprit:

* **Layer 1**, the user's contract alone — param types and refinements plus
  `requires`.  UNSAT means no call can reach the body: **E538**, a warning,
  and every obligation in the function demoted to `tier3_unguarded`.
* **Layer 2**, the full premise set including verifier-derived facts.  SAT at
  layer 1 and UNSAT at layer 2 means the VERIFIER introduced the
  contradiction, which is an internal soundness failure rather than anything
  the author wrote: **E539**, and the same refusal to certify.

The layer-2 cell plants the contradiction by neutering `_guard_fact` — the
#953 defence — on a program with two calls in mutually exclusive arms whose
postconditions each pin the parameter to a disjoint range.  That is the exact
shape `vera/smt.py` says goes "UNSAT, and *every* obligation discharges
vacuously", so the cell measures the general check against a real premise-source
regression rather than against an injected `False`.
"""

from __future__ import annotations

import json
import os
import subprocess
import sys
from pathlib import Path

import pytest

import vera

_PKG_PARENT = str(Path(vera.__file__).resolve().parents[1])


def _cli(*args: str) -> subprocess.CompletedProcess[str]:
    env = dict(os.environ)
    existing = env.get("PYTHONPATH", "")
    env["PYTHONPATH"] = (
        f"{_PKG_PARENT}{os.pathsep}{existing}" if existing else _PKG_PARENT
    )
    return subprocess.run(
        [sys.executable, "-m", "vera.cli", *args],
        capture_output=True, text=True, encoding="utf-8", check=False,
        env=env, timeout=600,
    )


def _write(tmp_path: Path, source: str, name: str = "p") -> Path:
    tmp_path.mkdir(parents=True, exist_ok=True)
    p = tmp_path / f"{name}.vera"
    p.write_text(source, encoding="utf-8")
    return p


def _verify(path: Path) -> dict:
    proc = _cli("verify", "--json", str(path))
    try:
        result = json.loads(proc.stdout)
    except json.JSONDecodeError:
        raise AssertionError(
            f"verify emitted no envelope for {path.name} "
            f"(exit {proc.returncode})\n{proc.stdout[:400]}\n"
            f"{proc.stderr[-800:]}"
        ) from None
    # An unresolved bare call is only a WARNING, so a typo'd callee verifies a
    # program that does not do what it reads as doing (the trap #1403's file
    # records).  Every fixture here names its own helpers.
    unresolved = [
        w for w in result.get("warnings", [])
        if w.get("error_code") == "E200"
    ]
    assert not unresolved, (
        f"{path.name}: fixture names a function that does not resolve — "
        f"{[w['description'] for w in unresolved]}"
    )
    return result


def _triples(result: dict) -> list[tuple[str, str, str | None]]:
    return [
        (o["kind"], o["status"], o.get("error_code"))
        for o in result["obligations"]
    ]


def _codes(result: dict, key: str = "warnings") -> list[str | None]:
    return [d.get("error_code") for d in result[key]]


# ---------------------------------------------------------------------------
# The isolation table from the issue: hold the postcondition, vary the premise
# ---------------------------------------------------------------------------

_SAT_REQUIRES_FALSE_ENSURES = """\
public fn f(@Int -> @Int)
  requires(@Int.0 > 5)
  ensures(@Int.result == 999 && @Int.result == 1000)
  effects(pure)
{
  0
}
"""

_UNSAT_REQUIRES = """\
public fn f(@Int -> @Int)
  requires(@Int.0 > 5 && @Int.0 < 3)
  ensures(@Int.result == 42)
  effects(pure)
{
  0
}
"""

_UNSAT_REQUIRES_SELF_CONTRADICTORY_ENSURES = """\
public fn f(@Int -> @Int)
  requires(@Int.0 > 5 && @Int.0 < 3)
  ensures(@Int.result == 999 && @Int.result == 1000)
  effects(pure)
{
  0
}
"""


def test_1451_a_satisfiable_premise_still_refutes_a_false_ensures(
    tmp_path: Path,
) -> None:
    """The control leg of the issue's table: green before and after.

    An unsatisfiable POSTCONDITION is caught when the premises are consistent,
    and must stay caught — a check that demoted every function with an
    unprovable contract would pass the other cells here while destroying the
    verifier's whole point.
    """
    result = _verify(_write(tmp_path, _SAT_REQUIRES_FALSE_ENSURES))
    assert result["ok"] is False, _triples(result)
    assert ("ensures", "violated") in [
        (o["kind"], o["status"]) for o in result["obligations"]
    ], _triples(result)


def test_1451_an_unsat_requires_no_longer_certifies_the_body(
    tmp_path: Path,
) -> None:
    """RED before: the issue's headline repro.

    The precondition is unsatisfiable and the body returns `0`, not `42`, and
    the run reported `tier1_verified: 2`, `ok: true`, no diagnostic.
    """
    result = _verify(_write(tmp_path, _UNSAT_REQUIRES))
    assert "E538" in _codes(result), _codes(result)
    assert all(
        o["status"] == "tier3_unguarded" for o in result["obligations"]
    ), _triples(result)
    v = result["verification"]
    assert v["tier1_verified"] == 0, v
    assert v["total"] == 0, v


def test_1451_the_demotion_says_no_call_can_reach_the_body(
    tmp_path: Path,
) -> None:
    """The warning has to name the function and say what it means.

    "Unsatisfiable" on its own reads as a solver complaint; the consequence —
    that no call can satisfy the contract, so nothing static about the body
    was established — is what the author acts on.
    """
    result = _verify(_write(tmp_path, _UNSAT_REQUIRES))
    e538 = [w for w in result["warnings"] if w.get("error_code") == "E538"]
    assert len(e538) == 1, _codes(result)
    text = e538[0]["description"]
    assert "'f'" in text, text
    assert "no call" in text, text
    assert e538[0]["rationale"], e538[0]
    assert e538[0]["spec_ref"], e538[0]


def test_1451_a_self_contradictory_ensures_is_demoted_not_proved(
    tmp_path: Path,
) -> None:
    """The issue's second repro: `result == 999 && result == 1000`.

    Reported `verified` under the UNSAT precondition, which is the same
    vacuity wearing a different hat.  It must not read `verified`; whether it
    reads `violated` or `tier3_unguarded` is the demotion's business, and the
    demotion wins because nothing about this function was established.
    """
    result = _verify(
        _write(tmp_path, _UNSAT_REQUIRES_SELF_CONTRADICTORY_ENSURES))
    assert "E538" in _codes(result), _codes(result)
    assert not [
        o for o in result["obligations"] if o["status"] == "verified"
    ], _triples(result)


# ---------------------------------------------------------------------------
# The premise set is not only `requires`
# ---------------------------------------------------------------------------

_REFINEMENT_CONTRADICTS_REQUIRES = """\
type Neg = { @Int | @Int.0 < 0 };

public fn f(@Neg -> @Int)
  requires(@Neg.0 > 0)
  ensures(@Int.result == 42)
  effects(pure)
{
  0
}
"""

_NAT_CONTRADICTS_REQUIRES = """\
public fn f(@Nat -> @Int)
  requires(nat_to_int(@Nat.0) < 0)
  ensures(@Int.result == 42)
  effects(pure)
{
  0
}
"""


@pytest.mark.parametrize(
    "source,id_", [
        pytest.param(_REFINEMENT_CONTRADICTS_REQUIRES, "refinement",
                     id="refined-param"),
        pytest.param(_NAT_CONTRADICTS_REQUIRES, "nat", id="nat-param"),
    ],
)
def test_1451_a_param_type_can_supply_half_the_contradiction(
    tmp_path: Path, source: str, id_: str,
) -> None:
    """Layer 1 is the whole user contract, not the `requires` clause alone.

    A refined parameter's predicate and `@Nat`'s implicit `>= 0` are premises
    the author wrote just as much as a `requires` is, and either can be the
    half that makes the set unsatisfiable.  Checking only the `requires`
    would leave both of these proving `result == 42` from a body of `0`.
    """
    result = _verify(_write(tmp_path / id_, source))
    assert "E538" in _codes(result), (_codes(result), _triples(result))
    assert not [
        o for o in result["obligations"] if o["status"] == "verified"
    ], _triples(result)


_WHERE_HELPER_UNSAT = """\
public fn outer(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  helper(@Int.0)
}
where {
  fn helper(@Int -> @Int)
    requires(@Int.0 > 5 && @Int.0 < 3)
    ensures(@Int.result == 42)
    effects(pure)
  {
    0
  }
}
"""


def test_1451_a_where_helper_is_checked_like_any_other_function(
    tmp_path: Path,
) -> None:
    """`where` helpers are verified through the same entry point.

    The check lives in the per-function path rather than a top-level sweep, so
    a helper gets it for free — pinned because a sweep over `program.
    declarations` would silently miss every helper.
    """
    result = _verify(_write(tmp_path, _WHERE_HELPER_UNSAT))
    e538 = [w for w in result["warnings"] if w.get("error_code") == "E538"]
    assert len(e538) == 1, _codes(result)
    assert "'helper'" in e538[0]["description"], e538[0]["description"]
    # The JSON obligation carries its expression text, not its function, so
    # the helper's two contracts are named by what they say.
    helper_obls = [
        o for o in result["obligations"]
        if o["kind"] in ("requires", "ensures")
        and o["description"] in ("@Int.0 > 5 && @Int.0 < 3",
                                 "@Int.result == 42")
    ]
    assert len(helper_obls) == 2, _triples(result)
    # And the parent's call to it is a genuine E501: no argument satisfies the
    # helper's precondition, which the caller now has to answer for.
    assert ("call_pre", "violated", "E501") in _triples(result), _triples(result)
    assert all(o["status"] == "tier3_unguarded" for o in helper_obls), (
        _triples(result))


# ---------------------------------------------------------------------------
# A satisfiable program is untouched
# ---------------------------------------------------------------------------

_HEALTHY = """\
private fn dec5(@Nat -> @Nat)
  requires(@Nat.0 >= 5)
  ensures(nat_to_int(@Nat.result) == nat_to_int(@Nat.0) - 5)
  effects(pure)
{
  @Nat.0 - 5
}

public fn main(@Nat -> @Nat)
  requires(@Nat.0 >= 5)
  ensures(true)
  effects(pure)
{
  dec5(@Nat.0)
}
"""


def test_1451_a_consistent_program_keeps_its_tier_1(tmp_path: Path) -> None:
    """The over-reach control.

    Every other cell asks for a demotion, so a check that demoted everything
    would pass them all.  This one fails unless real proofs survive: no E538,
    no E539, and Tier-1 obligations still counted.
    """
    result = _verify(_write(tmp_path, _HEALTHY))
    assert result["ok"] is True, result["diagnostics"]
    assert "E538" not in _codes(result), _codes(result)
    assert "E539" not in _codes(result), _codes(result)
    assert result["verification"]["tier1_verified"] > 0, result["verification"]
    assert not [
        o for o in result["obligations"] if o["status"] == "tier3_unguarded"
    ], _triples(result)


# ---------------------------------------------------------------------------
# Layer 2: the verifier's own facts
# ---------------------------------------------------------------------------

#: Two calls in mutually exclusive arms whose postconditions pin `@Nat.0` to
#: disjoint ranges: `r1 == @Nat.0 - 5` with `r1 >= 0` entails `@Nat.0 >= 5`,
#: and `r2 == 4 - @Nat.0` with `r2 >= 0` entails `@Nat.0 <= 4`.  Guarded by
#: their path conditions (#953) these coexist; unguarded they are UNSAT.
_TWO_ARMS = """\
private fn dec5(@Nat -> @Nat)
  requires(@Nat.0 >= 5)
  ensures(nat_to_int(@Nat.result) == nat_to_int(@Nat.0) - 5)
  effects(pure)
{
  @Nat.0 - 5
}

private fn upto4(@Nat -> @Nat)
  requires(nat_to_int(@Nat.0) < 5)
  ensures(nat_to_int(@Nat.result) == 4 - nat_to_int(@Nat.0))
  effects(pure)
{
  4 - @Nat.0
}

public fn caller(@Nat -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  if @Nat.0 >= 5 then {
    dec5(@Nat.0)
  } else {
    upto4(@Nat.0)
  }
}
"""


def _verify_in_process(path: Path) -> object:
    from vera.checker import typecheck_with_artifacts
    from vera.parser import parse
    from vera.resolver import ModuleResolver
    from vera.transform import transform
    from vera.verifier import verify

    text = path.read_text(encoding="utf-8")
    program = transform(parse(text, file=str(path)))
    resolved = ModuleResolver(_root=path.parent).resolve_imports(
        program, path)
    _diags, artifacts = typecheck_with_artifacts(
        program, text, file=str(path), resolved_modules=resolved,
    )
    return verify(
        program, text, file=str(path), resolved_modules=resolved,
        expr_types=artifacts.expr_semantic_types,
        expr_target_types=artifacts.expr_target_types,
    )


def test_1451_the_two_arms_fixture_is_clean_while_the_guard_holds(
    tmp_path: Path,
) -> None:
    """The layer-2 plant's control: with #953's guard in place, nothing fires.

    Without this the next cell proves nothing — a fixture that was already
    contradictory would raise E539 whether or not the plant did anything.
    """
    result = _verify(_write(tmp_path, _TWO_ARMS))
    assert "E539" not in _codes(result), _codes(result)
    assert "E538" not in _codes(result), _codes(result)
    assert result["verification"]["tier1_verified"] > 0, result["verification"]


def test_1451_a_verifier_derived_contradiction_refuses_to_certify(
    tmp_path: Path,
) -> None:
    """Layer 2, planted at a real premise source.

    `_guard_fact` scopes an assumed callee postcondition to the branch that
    earned it; `vera/smt.py` records what happens without it — "two calls in
    mutually-exclusive arms inject contradictory facts, the base solver goes
    UNSAT, and *every* obligation discharges vacuously".  Neutering it is
    therefore a faithful stand-in for any premise source going over-strong,
    which is the class this check exists to catch rather than the one
    producer.

    Layer 1 is SAT here — the caller's contract is `requires(true)` — so the
    contradiction is the verifier's own, and the diagnostic must say so
    rather than blaming the author's contract.
    """
    from vera import smt as smt_mod

    path = _write(tmp_path, _TWO_ARMS)
    original = smt_mod.SmtContext._guard_fact
    smt_mod.SmtContext._guard_fact = lambda self, fact: fact  # type: ignore[assignment]
    try:
        result = _verify_in_process(path)
    finally:
        smt_mod.SmtContext._guard_fact = original  # type: ignore[assignment]

    codes = [d.error_code for d in result.diagnostics]
    assert "E539" in codes, codes
    assert "E538" not in codes, (
        "layer 1 is satisfiable here, so the author's contract must not be "
        f"blamed: {codes}"
    )
    caller = [o for o in result.obligations if o.fn_name == "caller"]
    assert caller, [o.fn_name for o in result.obligations]
    assert all(o.status == "tier3_unguarded" for o in caller), [
        (o.kind, o.status) for o in caller
    ]
    text = next(d.description for d in result.diagnostics
                if d.error_code == "E539")
    assert "internal" in text.lower(), text
    assert "'caller'" in text, text


# ---------------------------------------------------------------------------
# The envelope, warm and cold
# ---------------------------------------------------------------------------

@pytest.mark.parametrize(
    "source", [
        pytest.param(_UNSAT_REQUIRES, id="unsat-requires"),
        pytest.param(_HEALTHY, id="healthy"),
    ],
)
def test_1451_json_accounting_identity_holds_through_the_demotion(
    tmp_path: Path, source: str,
) -> None:
    """`total == tier1 + tier3` and `len(obligations) == total + violated +
    tier3_unguarded`, per CLAUDE.md's partition table.

    The demotion moves obligations out of the counted tiers and into the
    uncounted bucket, which is precisely the move that breaks an accounting
    kept by hand.
    """
    result = _verify(_write(tmp_path, source))
    v = result["verification"]
    obls = result["obligations"]
    uncounted = sum(
        1 for o in obls if o["status"] in ("violated", "tier3_unguarded")
    )
    assert v["total"] == v["tier1_verified"] + v["tier3_runtime"], v
    assert len(obls) == v["total"] + uncounted, (
        f"{len(obls)} != total={v['total']} + {uncounted}: {_triples(result)}"
    )


@pytest.mark.parametrize(
    "source", [
        pytest.param(_UNSAT_REQUIRES, id="unsat-requires"),
        pytest.param(_HEALTHY, id="healthy"),
    ],
)
def test_1451_warm_and_cold_agree(tmp_path: Path, source: str) -> None:
    """The warm session must reach the same verdict as a cold run.

    The check reads the solver's own base context, which a warm session reuses
    across functions — so a `reset()` that left an assertion standing would
    show up here as a demotion the cold path does not make.
    """
    from vera.obligations.session import VerificationSession

    path = _write(tmp_path, source)
    cold = _verify_in_process(path)
    warm = VerificationSession().verify_source(
        source, file=str(path))

    def key(obls: object) -> list[tuple[str, str, str, str]]:
        return [
            (o.fn_name, o.kind, o.status, o.error_code or "")
            for o in obls  # type: ignore[attr-defined]
        ]

    assert key(warm.obligations) == key(cold.obligations), (
        key(warm.obligations), key(cold.obligations))
    assert sorted(d.error_code for d in warm.diagnostics) == sorted(
        d.error_code for d in cold.diagnostics)


def test_1451_the_run_traps_on_the_precondition_it_cannot_satisfy(
    tmp_path: Path,
) -> None:
    """The `ensures` + `vera run` differential, with the honest oracle.

    For most false Tier-1s the witness is a run that contradicts the proof.
    Not here: an UNSAT precondition means no call reaches the body at all, so
    the runtime precondition guard traps first and the body's false
    postcondition is never exercised.  That is exactly WHY the static claim
    was invisible, and it is why this cell asserts the status change plus the
    trap, rather than a runtime value that cannot exist.
    """
    source = _UNSAT_REQUIRES + """
public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  f(7)
}
"""
    path = _write(tmp_path, source)
    result = _verify(path)
    assert "E538" in _codes(result), _codes(result)
    demoted = [
        o for o in result["obligations"]
        if o["kind"] in ("requires", "ensures")
        and o["description"] in ("@Int.0 > 5 && @Int.0 < 3",
                                 "@Int.result == 42")
    ]
    assert len(demoted) == 2, _triples(result)
    assert all(o["status"] == "tier3_unguarded" for o in demoted), (
        _triples(result))

    proc = _cli("run", str(path))
    assert proc.returncode != 0, (proc.stdout, proc.stderr)
    assert "recondition" in proc.stderr, proc.stderr[:600]


def test_1451_the_codes_are_registered_and_attributed() -> None:
    """Both codes are in the registry with a `since`, like every other code."""
    from vera._since import SINCE
    from vera.errors import ERROR_CODES

    for code in ("E538", "E539"):
        assert code in ERROR_CODES, sorted(ERROR_CODES)[-6:]
        assert ERROR_CODES[code], code
        assert SINCE.get(code), code


_WIDE_CONTRADICTION = """\
type Small = { @Int | @Int.0 < 100 };

public fn f(@Small, @Nat, @Bool -> @Int)
  requires(@Small.0 > 10)
  requires(nat_to_int(@Nat.0) > @Small.0 * 1)
  requires(nat_to_int(@Nat.0) < 5)
  requires(@Bool.0 || !@Bool.0)
  ensures(@Int.result == 42)
  effects(pure)
{
  0
}
"""


def test_1451_a_wider_contradiction_is_still_reached_inside_the_budget(
    tmp_path: Path,
) -> None:
    """The screening budget has to be wide enough for a real contract.

    250 ms is chosen against a measurement, not a guess, and the risk of
    choosing it is a contradiction the check no longer has time to find.  This
    one spans three parameters, a refinement, a `@Nat`'s implicit `>= 0` and
    four `requires` clauses — an order more premises than the headline repro —
    and must still be refuted.
    """
    result = _verify(_write(tmp_path, _WIDE_CONTRADICTION))
    assert "E538" in _codes(result), (_codes(result), _triples(result))
    assert not [
        o for o in result["obligations"] if o["status"] == "verified"
    ], _triples(result)


def test_1451_the_screening_budget_does_not_widen_a_smaller_one(
    tmp_path: Path,
) -> None:
    """`--timeout-ms` below the screening budget stays the cap.

    The solver is shared with every obligation still to be discharged, so the
    check both takes the smaller of the two budgets and puts the run's own
    back before returning — a check that left 250 ms standing would silently
    widen a deliberately tiny budget for everything after it.
    """
    path = _write(tmp_path, _UNSAT_REQUIRES)
    proc = _cli("verify", "--json", "--timeout-ms", "50", str(path))
    result = json.loads(proc.stdout)
    assert result["verification"]["timeout_ms"] == 50, result["verification"]
    assert "E538" in _codes(result), _codes(result)
