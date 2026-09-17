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
from typing import NamedTuple

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


def _codes(result: dict, key: str | None = None) -> list[str | None]:
    """The codes the run reported, at either severity unless *key* says which.

    The envelope splits by severity — errors into `diagnostics`, warnings into
    `warnings` — and E538 is an error while E539 is a warning, so a cell that
    read one key would be asserting the severity by accident every time it
    meant to assert that the vacuity was reported at all.  The severity is a
    claim in its own right and is pinned in one place, by
    `test_1451_the_refusal_lands_at_the_definition`.
    """
    keys = (key,) if key is not None else ("diagnostics", "warnings")
    return [d.get("error_code") for k in keys for d in result[k]]


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
    # E538 is an ERROR, so it arrives in `diagnostics`, not `warnings`.
    e538 = [d for d in result["diagnostics"] if d.get("error_code") == "E538"]
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
    # E538 is an ERROR, so it arrives in `diagnostics`, not `warnings`.
    e538 = [d for d in result["diagnostics"] if d.get("error_code") == "E538"]
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


def _verify_in_process(path: Path, timeout_ms: int | None = None) -> object:
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
        timeout_ms=timeout_ms,
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
    e539 = next(d for d in result.diagnostics if d.error_code == "E539")
    assert "derived from the program" in e539.description, e539.description
    assert "'caller'" in e539.description, e539.description
    # E539 must NOT open by calling itself internal (#1457 review, Medium 3).
    # The same code is reached when an `assume` the author wrote contradicts a
    # callee's postcondition, which is the program disagreeing with itself and
    # not a compiler defect; the bug report belongs in the `fix`, as the last
    # resort it is, rather than in the sentence the reader sees first.
    assert "internal" not in e539.description.lower(), e539.description
    assert "report this program" not in e539.description.lower(), (
        e539.description)
    assert "report the program" in (e539.fix or "").lower(), e539.fix
    # ... and it stays a WARNING where its sibling E538 is an error.  The
    # premise at fault here is one the author may not control — a callee's
    # postcondition, a refined return, a declared-type fact — so refusing the
    # program would refuse it for a clause that is not in it.  E538's premises
    # are all the author's own, which is what makes refusal precise there.
    assert e539.severity == "warning", (e539.severity, e539.description)


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


_UNSAT_GENERIC = """\
private forall<T> fn callee(@T -> @Int)
  requires(false)
  ensures(@Int.result == 0)
  effects(pure)
{
  0
}

public fn caller(@Int -> @Int)
  requires(true)
  ensures(@Int.result == 0)
  effects(pure)
{
  callee(@Int.0)
}
"""

_SAT_GENERIC = _UNSAT_GENERIC.replace("requires(false)", "requires(true)")


def test_1451_an_instantiated_generic_reports_its_refusal(
    tmp_path: Path,
) -> None:
    """The demotion survives the generic aggregation, at its own severity.

    A generic's obligations are discharged once per instantiation into a
    scratch buffer and then collapsed one per source site, and the
    representative instance's diagnostic is RE-EMITTED for the survivor.
    That re-emission looked its diagnostic up by span, code and a severity
    derived from the STATUS — `error` for `violated`, `warning` for everything
    else — which held for every code until E538 became an error on a
    `tier3_unguarded` obligation.  With the inference in place the lookup
    missed, the fallback declined to synthesise what it took for an
    informational warning, and the run reported the obligation as
    `tier3_unguarded`/E538 with no diagnostic in either stream and `ok: true`.
    That is this PR's own class — a demotion no reader sees — in the one path
    that re-emits a diagnostic rather than emitting it.

    The prefix is asserted and not only the code, because the prefix is what
    distinguishes a re-emitted per-instance diagnostic from one emitted
    directly: without it the cell would pass on a refusal that reached the
    reader by some other route. The satisfiable twin is the differential —
    without it, a check that refused every generic would pass the first half.
    """
    unsat = _verify(_write(tmp_path / "unsat", _UNSAT_GENERIC))
    assert unsat["ok"] is False, unsat["diagnostics"]
    e538 = [d for d in unsat["diagnostics"] if d.get("error_code") == "E538"]
    assert len(e538) == 1, (unsat["diagnostics"], _triples(unsat))
    assert e538[0]["severity"] == "error", e538[0]
    assert "instantiated at" in e538[0]["description"], e538[0]["description"]
    assert "'callee'" in e538[0]["description"], e538[0]["description"]

    # ... and the obligation array agrees with it at the same line.
    demoted = [
        o for o in unsat["obligations"] if o.get("error_code") == "E538"
    ]
    assert demoted, _triples(unsat)
    assert all(o["status"] == "tier3_unguarded" for o in demoted), demoted
    assert e538[0]["location"]["line"] in [
        o["location"]["line"] for o in demoted
    ], (e538[0]["location"], _triples(unsat))

    # The twin: the same generic with a satisfiable precondition keeps its
    # proofs and reports nothing, so neither leg is satisfied by a screen that
    # had stopped discriminating.
    sat = _verify(_write(tmp_path / "sat", _SAT_GENERIC))
    assert "E538" not in _codes(sat), _codes(sat)
    assert "E539" not in _codes(sat), _codes(sat)
    assert sat["verification"]["tier1_verified"] > 0, sat["verification"]


def test_1451_the_refusal_lands_at_the_definition(tmp_path: Path) -> None:
    """E538 is an ERROR, at the clause that is wrong, and the run exits 1.

    A premise set with no model is a contract that admits no argument, so it
    constrains no behaviour: there is nothing for a tier to describe, and
    leaving the program to stand made the signal something the author had to
    go and read.  The refusal is reported where the clause is, not at a call
    site — a caller may be in another module, or may not exist yet.

    Asserted as the whole shape rather than "an E538 exists somewhere": the
    severity, the key of the envelope it arrives in, the exit code, the line,
    and the `fix` an error is required to carry.  `_codes` reads both keys, so
    without this cell the severity would be unpinned everywhere.
    """
    path = _write(tmp_path, _UNSAT_REQUIRES)
    proc = _cli("verify", "--json", str(path))
    result = json.loads(proc.stdout)

    assert proc.returncode == 1, (proc.returncode, proc.stdout[:400])
    assert result["ok"] is False, result["diagnostics"]
    assert "E538" not in _codes(result, "warnings"), _codes(result, "warnings")

    errors = [
        d for d in result["diagnostics"] if d.get("error_code") == "E538"
    ]
    assert len(errors) == 1, result["diagnostics"]
    e538 = errors[0]
    assert e538["severity"] == "error", e538
    # The `requires` line of the fixture — the premise the author can edit —
    # rather than the body or the `ensures` that discharged vacuously.
    assert e538["location"]["line"] == 2, (e538["location"], _UNSAT_REQUIRES)
    # `check_diagnostic_fields` requires a fix on an error; a warning is
    # exempt, so the flip makes this field load-bearing.
    assert e538["fix"], e538
    # And the run still says what it established, which is nothing.
    assert result["verification"]["tier1_verified"] == 0, (
        result["verification"])


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


# ---------------------------------------------------------------------------
# `assume` is a premise too (#1457 review, F1)
# ---------------------------------------------------------------------------

_ONE_ASSUME = """\
public fn f(@Int -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  assume(@Int.0 < 3);
  let @Nat = @Int.0;
  @Nat.0
}
"""

_TWO_ASSUMES = """\
public fn f(@Int -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  assume(@Int.0 < 3);
  assume(@Int.0 > 5);
  let @Nat = @Int.0;
  @Nat.0
}
"""


def test_1451_one_assume_alone_still_refutes_the_narrowing(
    tmp_path: Path,
) -> None:
    """The control leg for the `assume` layer: green before and after.

    `assume(@Int.0 < 3)` leaves the narrowing `let @Nat = @Int.0` refutable,
    and it must stay refuted — a check that demoted any function containing an
    `assume` would pass the next cell while destroying this one.
    """
    result = _verify(_write(tmp_path, _ONE_ASSUME))
    assert ("nat_bind", "violated", "E503") in _triples(result), _triples(result)
    assert "E538" not in _codes(result), _codes(result)


def test_1451_a_contradictory_assume_is_a_premise_too(tmp_path: Path) -> None:
    """RED before: `assume` facts were invisible to both layers.

    They live in `SmtContext._path_conditions` (#804) and are folded into
    every `check_valid` query rather than asserted into the base context, and
    step 8's restore point drops them before the consistency check ran — so
    adding a second, contradictory `assume` flipped the refuted narrowing
    above to `verified` with `tier1_verified: 3`, exit 0, and no E538 or E539,
    while `vera run -- -5` still trapped on that very narrowing.

    An `assume` is taken on trust, which makes it exactly the premise a
    contradiction is cheapest to smuggle in through: `requires(x > 5 && x < 3)`
    and two contradictory assumes are the same garbage-in.
    """
    result = _verify(_write(tmp_path, _TWO_ASSUMES))
    assert "E538" in _codes(result), (_codes(result), _triples(result))
    assert not [
        o for o in result["obligations"] if o["status"] == "verified"
    ], _triples(result)
    assert result["verification"]["tier1_verified"] == 0, (
        result["verification"])


def test_1451_the_demotion_points_at_the_assume_line(tmp_path: Path) -> None:
    """... and names the line that contributed the contradiction.

    The `requires` here is `true` and blameless; pointing the diagnostic at it
    would send the reader to a clause with nothing wrong with it.
    """
    result = _verify(_write(tmp_path, _TWO_ASSUMES))
    # E538 is an ERROR, so it arrives in `diagnostics`, not `warnings`.
    e538 = [d for d in result["diagnostics"] if d.get("error_code") == "E538"]
    assert len(e538) == 1, _codes(result)
    assert e538[0]["source_line"].strip().startswith("assume("), e538[0]
    assert "assume" in e538[0]["fix"], e538[0]["fix"]


_UNREACHABLE_ARM = """\
public fn f(@Int -> @Int)
  requires(@Int.0 > 5)
  ensures(true)
  effects(pure)
{
  if @Int.0 < 3 then {
    @Int.0
  } else {
    1
  }
}
"""


def test_1451_an_unreachable_arm_is_not_a_contradiction(
    tmp_path: Path,
) -> None:
    """Branch path conditions stay OUT of both layers, deliberately.

    `_path_conditions` carries two different things: the `assume` facts the
    cell above folds in, and the guard of whichever branch is being walked.
    An arm whose guard cannot hold under the precondition is *unreachable*,
    not contradictory — its obligations are discharged under that guard by
    construction, and demoting the function for it would report the program's
    own shape as a defect.
    """
    result = _verify(_write(tmp_path, _UNREACHABLE_ARM))
    assert result["ok"] is True, result["diagnostics"]
    assert "E538" not in _codes(result), _codes(result)
    assert "E539" not in _codes(result), _codes(result)
    assert result["verification"]["tier1_verified"] > 0, result["verification"]


# ---------------------------------------------------------------------------
# The demotion leaves an already-disclosed obligation's code alone (F3)
# ---------------------------------------------------------------------------

# An UNGUARDED disclosure: `@Unit` is erased, so codegen cannot emit a
# boundary predicate check and the refinement is recorded `tier3_unguarded`
# with its own E506 (the shape `test_verifier_refinements.py` pins).  That is
# what the carve-out is about — an obligation already outside every counted
# tier, carrying a reason the demotion did not create.
_DISCLOSED_UNDER_UNSAT = """\
private fn always_false(@Unit -> @Bool)
  requires(true)
  ensures(true)
  effects(pure)
{
  false
}

type Checked = { @Unit | always_false(()) };

public fn f(@Int, @Unit -> @Checked)
  requires(@Int.0 > 5 && @Int.0 < 3)
  ensures(true)
  effects(pure)
{
  ()
}
"""

# A GUARDED one, for contrast: the refinement over a `@PosInt` payload gets a
# real runtime check, so it is `tier3` and counted in `tier3_runtime`.
_GUARDED_UNDER_UNSAT = """\
type PosInt = { @Int | @Int.0 > 0 };

public fn f(@Int -> @Option<PosInt>)
  requires(@Int.0 > 5 && @Int.0 < 3)
  ensures(true)
  effects(pure)
{
  Some(handle[Exn<Int>] {
    throw(@PosInt) -> { @PosInt.0 }
  } in {
    throw(@Int.0)
  })
}
"""


def test_1451_an_already_disclosed_obligation_keeps_its_code(
    tmp_path: Path,
) -> None:
    """The demotion has nothing to do to an obligation already out of the tiers.

    Rewriting its `error_code` to E538 left the obligation array and the
    diagnostic stream naming DIFFERENT codes for one line — the E506 warning
    survives at the site while the obligation claimed E538 (#1457 review, F3).
    The same carve-out `violated` gets, one layer along: it is already counted
    in no tier, so the demotion is a no-op on it and should read as one.
    """
    result = _verify(_write(tmp_path, _DISCLOSED_UNDER_UNSAT))
    disclosed = [
        o for o in result["obligations"] if o["kind"] == "refine_bind"
    ]
    assert len(disclosed) == 1, _triples(result)
    assert disclosed[0]["status"] == "tier3_unguarded", _triples(result)
    assert disclosed[0]["error_code"] == "E506", _triples(result)
    # ... and the warning at that line agrees with it.
    at_line = [
        w for w in result["warnings"]
        if w["location"]["line"] == disclosed[0]["location"]["line"]
    ]
    assert [w["error_code"] for w in at_line] == ["E506"], at_line
    # The contract obligations still demote, so the cell is not vacuous.
    assert "E538" in _codes(result), _codes(result)


def test_1451_a_guarded_tier3_obligation_keeps_its_status_and_code(
    tmp_path: Path,
) -> None:
    """The carve-out's general form: only a `verified` obligation is demoted.

    An obligation that came back anything but `verified` under a premise set
    with no model reached that verdict for a reason the contradiction did not
    supply — `check_valid` answers `unsat` for EVERY goal here, so `tier3`,
    `timeout` and `tier3_unguarded` can only have come from untranslatability,
    an unmodelled base, or an expired budget (#1457 review, Medium 1).  Each
    already carries the code of its own reason and a warning at its own line,
    so rewriting it left the obligation array and the diagnostic stream naming
    different codes for one site.  A GUARDED `tier3` is the sharpest case: it
    would be relabelled `tier3_unguarded`, whose documented meaning is
    "neither proved nor guarded", while codegen — which consults no verdict at
    all — still emits the guard.

    The premise beside it is the satisfiable twin, which must report the same
    status and code, so the cell measures the carve-out rather than a compiler
    that had stopped guarding anything.
    """
    sat = _verify(_write(
        tmp_path / "sat",
        _GUARDED_UNDER_UNSAT.replace("@Int.0 > 5 && @Int.0 < 3", "@Int.0 > 5"),
    ))
    guarded = [o for o in sat["obligations"] if o["kind"] == "refine_bind"]
    assert guarded, _triples(sat)
    assert all(
        (o["status"], o["error_code"]) == ("tier3", "E506") for o in guarded
    ), _triples(sat)

    unsat = _verify(_write(tmp_path / "unsat", _GUARDED_UNDER_UNSAT))
    kept = [o for o in unsat["obligations"] if o["kind"] == "refine_bind"]
    assert len(kept) == len(guarded), _triples(unsat)
    assert all(
        (o["status"], o["error_code"]) == ("tier3", "E506") for o in kept
    ), _triples(unsat)
    # ... and the diagnostics agree with the array at every one of those lines.
    for o in kept:
        at_line = [
            w["error_code"] for w in unsat["warnings"]
            if w["location"]["line"] == o["location"]["line"]
        ]
        assert at_line == ["E506"], (o, at_line)
    # The cell is not vacuous: the CONTRACT obligations still demote, and
    # nothing in the function is certified.
    assert "E538" in _codes(unsat), _codes(unsat)
    assert unsat["verification"]["tier1_verified"] == 0, unsat["verification"]


# ---------------------------------------------------------------------------
# One query per function (F2)
# ---------------------------------------------------------------------------

def test_1451_the_check_costs_one_query_per_function(tmp_path: Path) -> None:
    """The full set is asked FIRST, and its `sat` settles both layers.

    The author's premises are a SUBSET of the full set, so a model of the
    full set is a model of theirs — which means the second query is reachable
    only when there is something to attribute. Asking the author's layer
    first, as the first draft did, was unconditionally two queries per
    function and the heading said one (#1457 review, F2).
    """
    from vera import verifier as vmod

    seen = {"full": 0, "author": 0, "fns": 0}
    of = vmod.ContractVerifier._full_premises_satisfiable
    oa = vmod.ContractVerifier._contract_premises_satisfiable
    oe = vmod.ContractVerifier._enforce_premise_consistency

    def full(self, smt, assumed):  # type: ignore[no-untyped-def]
        seen["full"] += 1
        return of(self, smt, assumed)

    def author(self, contract, assumed, smt):  # type: ignore[no-untyped-def]
        seen["author"] += 1
        return oa(self, contract, assumed, smt)

    def enforce(self, decl, smt, obl_start, contract, assumed):  # type: ignore[no-untyped-def]
        seen["fns"] += 1
        return oe(self, decl, smt, obl_start, contract, assumed)

    vmod.ContractVerifier._full_premises_satisfiable = full  # type: ignore[assignment]
    vmod.ContractVerifier._contract_premises_satisfiable = author  # type: ignore[assignment]
    vmod.ContractVerifier._enforce_premise_consistency = enforce  # type: ignore[assignment]
    try:
        _verify_in_process(_write(tmp_path / "ok", _HEALTHY))
        clean = dict(seen)
        _verify_in_process(_write(tmp_path / "bad", _UNSAT_REQUIRES))
    finally:
        vmod.ContractVerifier._full_premises_satisfiable = of  # type: ignore[assignment]
        vmod.ContractVerifier._contract_premises_satisfiable = oa  # type: ignore[assignment]
        vmod.ContractVerifier._enforce_premise_consistency = oe  # type: ignore[assignment]

    assert clean["fns"] == clean["full"], (
        f"the full set must be asked exactly once per function: {clean}")
    assert clean["author"] == 0, (
        f"a satisfiable function must cost ONE query: {clean}")
    # The contradictory one pays the second, which is what buys the
    # attribution between E538 and E539.  Counted as a DELTA: the fixpoint in
    # `verify_program` re-verifies when the disclosed set moves, so absolute
    # totals are not one-per-source-function and pinning them would make this
    # cell about that loop rather than about the query order.
    assert seen["author"] > clean["author"], (clean, seen)
    assert seen["full"] - clean["full"] == seen["fns"] - clean["fns"], (
        clean, seen)


def test_1451_stage_two_is_asked_only_when_stage_one_decided_nothing(
    tmp_path: Path,
) -> None:
    """A `sat` at stage 1 settles stage 2, so stage 2 is not asked.

    A model of the whole premise set is a model of every SUBSET of it, the
    quantifier-free one included, so once stage 1 has exhibited a model the
    only answer stage 2 can give is `sat` — and it asks at the full DISCHARGE
    budget to be told so.  RED before the gate, which ran stage 2 whenever
    stage 1 was `is not False`: that is every clean function in the corpus
    (#1457 review, CodeRabbit).

    Both legs, because the gate has to be shown to lose no DETECTION as well
    as to save the query.  With stage 1 blinded to `unknown` — the one verdict
    that now reaches stage 2 — the same program must still be asked, so an
    unsatisfiable quantifier-free subset is still refuted wherever stage 1
    fails to decide.
    """
    from vera import verifier as vmod

    seen: list[tuple[str, str]] = []
    o_full = vmod.ContractVerifier._full_premises_satisfiable
    o_qf = vmod.ContractVerifier._quantifier_free_premises_satisfiable
    label = {True: "sat", False: "unsat", None: "unknown"}

    def spy_full(self, smt, assumed):  # type: ignore[no-untyped-def]
        v = o_full(self, smt, assumed)
        seen.append(("stage1", label[v]))
        return v

    def blind_stage1(self, smt, assumed):  # type: ignore[no-untyped-def]
        seen.append(("stage1", "unknown"))
        return None

    def spy_qf(self, smt, assumed):  # type: ignore[no-untyped-def]
        v = o_qf(self, smt, assumed)
        seen.append(("stage2", label[v]))
        return v

    vmod.ContractVerifier._quantifier_free_premises_satisfiable = spy_qf  # type: ignore[assignment]
    try:
        vmod.ContractVerifier._full_premises_satisfiable = spy_full  # type: ignore[assignment]
        seen.clear()
        decided = _verify_in_process(_write(tmp_path / "ok", _HEALTHY))
        decided_seen = list(seen)

        vmod.ContractVerifier._full_premises_satisfiable = blind_stage1  # type: ignore[assignment]
        seen.clear()
        blinded = _verify_in_process(_write(tmp_path / "blind", _HEALTHY))
        blinded_seen = list(seen)
    finally:
        vmod.ContractVerifier._full_premises_satisfiable = o_full  # type: ignore[assignment]
        vmod.ContractVerifier._quantifier_free_premises_satisfiable = o_qf  # type: ignore[assignment]

    # The status premise beside the assertion: stage 1 really answered `sat`,
    # and the screen really ran.  Without it the cell is satisfied by a run
    # that never reached the check — which is what a broken screen looks like.
    assert ("stage1", "sat") in decided_seen, decided_seen
    assert not [s for s in decided_seen if s[0] == "stage2"], decided_seen
    assert decided.summary.tier1_verified > 0, decided.summary  # type: ignore[attr-defined]

    # ... and the detection the gate must not cost: blinded, stage 2 is asked,
    # and on a healthy program it answers `sat` and demotes nothing.
    assert ("stage2", "sat") in blinded_seen, blinded_seen
    assert not [
        d for d in blinded.diagnostics  # type: ignore[attr-defined]
        if d.error_code in ("E538", "E539")
    ], blinded_seen
    assert blinded.summary.tier1_verified > 0, blinded.summary  # type: ignore[attr-defined]


# ---------------------------------------------------------------------------
# An undecided premise query is not a contradiction
# ---------------------------------------------------------------------------

_RECURSIVE_MEASURE = """\
private data List<T> {
  Nil,
  Cons(T, List<T>)
}

public fn length(@List<Int> -> @Nat)
  requires(true)
  ensures(@Nat.result >= 0)
  decreases(@List<Int>.0)
  effects(pure)
{
  match @List<Int>.0 {
    Nil -> 0,
    Cons(@Int, @List<Int>) -> 1 + length(@List<Int>.0)
  }
}
"""

_RECURSIVE_MEASURE_UNSAT = """\
private data List<T> {
  Nil,
  Cons(T, List<T>)
}

public fn length_from(@List<Int>, @Int -> @Nat)
  requires(@Int.0 > 5 && @Int.0 < 3)
  ensures(@Nat.result >= 0)
  decreases(@List<Int>.0)
  effects(pure)
{
  match @List<Int>.0 {
    Nil -> 0,
    Cons(@Int, @List<Int>) -> 1 + length_from(@List<Int>.1, @Int.1)
  }
}
"""


def _premise_verdicts(path: Path) -> tuple[list[str], object]:
    """Verify in process, recording what each premise query answered.

    The verdict itself is the label these two cells assert: without it they
    would pass on a program whose full premise set came back `sat` in a
    millisecond, which exercises nothing about the undecided branch.
    """
    from vera import verifier as vmod

    seen: list[str] = []
    original = vmod.ContractVerifier._full_premises_satisfiable

    def spy(self, smt, assumed):  # type: ignore[no-untyped-def]
        verdict = original(self, smt, assumed)
        seen.append({True: "sat", False: "unsat", None: "unknown"}[verdict])
        return verdict

    vmod.ContractVerifier._full_premises_satisfiable = spy  # type: ignore[assignment]
    try:
        return seen, _verify_in_process(path)
    finally:
        vmod.ContractVerifier._full_premises_satisfiable = original  # type: ignore[assignment]


def test_1451_an_undecided_premise_query_is_not_a_contradiction(
    tmp_path: Path,
) -> None:
    """RED before: a `decreases` measure over a recursive ADT got a false E539.

    Those rank axioms are quantified, so the full premise set sends Z3 to MBQI
    and reliably exhausts the 250 ms screening budget — the PR's own cost table
    is the measurement, seven corpus programs, every one a timeout.  Reading
    that `unknown` as "unsatisfiable" reported the verifier's own premises as
    contradictory over `length` and demoted every obligation in it, on a
    program that verifies.

    `unknown` decides nothing.  The premise beside the assertion is the verdict
    itself: this cell is about the undecided branch, and a fixture whose full
    set came back `sat` would exercise the ordinary path instead.
    """
    seen, result = _premise_verdicts(_write(tmp_path, _RECURSIVE_MEASURE))
    assert "unknown" in seen, seen
    codes = [d.error_code for d in result.diagnostics]
    assert "E539" not in codes, codes
    assert "E538" not in codes, codes
    assert result.summary.tier1_verified > 0, result.summary


def test_1451_a_contradiction_in_the_same_context_is_still_refuted(
    tmp_path: Path,
) -> None:
    """... and the repair does not buy its silence by giving up detection.

    The complement, without which the cell above is satisfied by a check that
    returns early on `unknown` and never reports anything again: the SAME
    quantified context, with a contradictory `requires`.  It is refuted rather
    than left undecided, which is why only a refutation needs to demote — Z3
    reaches UNSAT by propagation before it instantiates a rank axiom, so the
    contradictions this check exists to catch are the ones it answers fastest,
    and the budget that expires on a consistent premise set is not the budget
    a contradiction has to fit inside.
    """
    seen, result = _premise_verdicts(
        _write(tmp_path, _RECURSIVE_MEASURE_UNSAT))
    assert "unsat" in seen and "unknown" not in seen, seen
    codes = [d.error_code for d in result.diagnostics]
    assert "E538" in codes, codes
    assert result.summary.tier1_verified == 0, result.summary


def test_1451_an_undecided_full_set_still_asks_the_author_layer(
    tmp_path: Path,
) -> None:
    """A contradiction the author wrote survives an undecided full set.

    `unknown` on the full set means nothing may be blamed on the VERIFIER —
    but the author's layer is the pre-body snapshot, with no rank axiom and
    no derived fact in it, so it is still answerable and a refutation there is
    as real as one found in the full set.  Skipping it would make the whole
    check conditional on the verifier's own derived facts being decidable,
    which is backwards: the premise set would go unchecked on exactly the
    programs whose reasoning is hardest.

    No whole program is known to reach this pairing — a contradictory premise
    set is refuted by propagation before any quantifier is instantiated, so
    the full set answers `unsat` even under rank axioms (the cell above
    measures that) — so the verdict is injected, the same way `check_valid`'s
    `opaque` branch is driven in `test_verifier_refinements.py`.  Injected or
    not, the branch has a contract, and it is pinned here rather than left
    unfalsifiable.
    """
    from vera import verifier as vmod

    original = vmod.ContractVerifier._full_premises_satisfiable
    vmod.ContractVerifier._full_premises_satisfiable = (  # type: ignore[assignment]
        lambda self, smt, assumed: None
    )
    try:
        result = _verify_in_process(_write(tmp_path / "bad", _UNSAT_REQUIRES))
        healthy = _verify_in_process(_write(tmp_path / "ok", _HEALTHY))
    finally:
        vmod.ContractVerifier._full_premises_satisfiable = original  # type: ignore[assignment]

    codes = [d.error_code for d in result.diagnostics]
    assert "E538" in codes, codes
    assert "E539" not in codes, codes
    assert result.summary.tier1_verified == 0, result.summary
    # ... and an undecided full set over a HEALTHY contract still says
    # nothing, so the branch reports a refutation rather than the `unknown`.
    assert not [
        d for d in healthy.diagnostics if d.error_code in ("E538", "E539")
    ], [d.error_code for d in healthy.diagnostics]
    assert healthy.summary.tier1_verified > 0, healthy.summary


def test_1451_an_undecidable_author_layer_demotes_without_attributing(
    tmp_path: Path,
) -> None:
    """The third verdict of the attribution query, reached by injection.

    A refuted full premise set whose AUTHOR layer comes back `unknown` cannot
    be blamed on either side: calling it internal would accuse the compiler of
    something that may be the contract, and saying nothing would keep a
    vacuous proof.  No whole program is known to reach it — the author layer
    is the pre-body snapshot, small and quantifier-free — so the outcome is
    injected directly, the same way `check_valid`'s `opaque` and `unknown`
    branches are driven in `test_verifier_refinements.py`.  Without a cell the
    branch is unfalsifiable; with one, its contract is pinned: demote, warn
    under the code that claims least, and do NOT say E539.
    """
    from vera import verifier as vmod

    original = vmod.ContractVerifier._contract_premises_satisfiable
    vmod.ContractVerifier._contract_premises_satisfiable = (  # type: ignore[assignment]
        lambda self, contract, assumed, smt: None
    )
    try:
        result = _verify_in_process(_write(tmp_path, _UNSAT_REQUIRES))
    finally:
        vmod.ContractVerifier._contract_premises_satisfiable = original  # type: ignore[assignment]

    codes = [d.error_code for d in result.diagnostics]
    assert "E538" in codes, codes
    assert "E539" not in codes, codes
    assert "could not be determined" in "".join(
        d.description for d in result.diagnostics), codes
    assert result.summary.tier1_verified == 0, result.summary
    assert all(
        o.status == "tier3_unguarded" for o in result.obligations
    ), [(o.kind, o.status) for o in result.obligations]


# ---------------------------------------------------------------------------
# The class instrument: the vacuity matrix
# ---------------------------------------------------------------------------
#
# The class is not "a contradictory `requires`".  It is: an obligation
# discharged against a premise set with no model, reported as a proof.  The
# matrix therefore ranges over every ROUTE by which the premise set an
# obligation runs under can go unsatisfiable, crossed with every KIND of
# obligation that can be discharged against it.
#
# The routes are read off the code that COLLECTS the premises, not off the
# bug reports, so a source the collector has and the matrix does not shows up
# as a missing row.  `_verify_fn` builds them in three places:
#
#   * the solver's base context (step 4) — a parameter's declared-type
#     constraint (`@Nat`'s implicit `>= 0`), each refined parameter's
#     predicate, and every translatable `requires`;
#   * `SmtContext._path_conditions` (#804) — the top-level `assume` facts,
#     AND the guard of whichever branch or arm is being walked;
#   * the base context again, after the body (step 5 onward) — the facts the
#     verifier itself derives: a callee's postcondition, a refined return, a
#     declared-type fact off a constructor sub-pattern.
#
# The third is layer 2 and is not reachable from source (the two producers
# `vera/smt.py` knows about are both defended against by hand), so it is
# measured by the `_guard_fact` plant above rather than by a cell here.  The
# second splits: an `assume` is a PREMISE and belongs in the author's layer,
# while a branch guard is the program's own shape — an arm that cannot run is
# unreachable, not contradictory.  Both halves are cells, with opposite
# expectations, because getting either backwards is a defect: folding a guard
# in would demote every function with a dead arm, and leaving an `assume` out
# was the bug #1457's review found.

class _Route(NamedTuple):
    """One way to make the premise set an obligation is discharged under UNSAT.

    *shape* selects the rendering; *layer* is what the design owes the cell —
    ``"author"`` must report the vacuity and certify nothing, ``"path"`` must
    NOT, because the obligation sits in an arm no call can enter.
    """

    shape: str
    layer: str
    params: str
    unsat_requires: tuple[str, ...]
    sat_requires: tuple[str, ...]
    unsat_preamble: str = ""
    sat_preamble: str = ""


_ROUTES: dict[str, _Route] = {
    # --- the base context: `requires` ---------------------------------
    "requires_conjunction": _Route(
        "plain", "author", "",
        ("@Int.0 > 5 && @Int.0 < 3",), ("@Int.0 > 5 && @Int.0 > 3",),
    ),
    "requires_two_clauses": _Route(
        "plain", "author", "",
        ("@Int.0 > 5", "@Int.0 < 3"), ("@Int.0 > 5", "@Int.0 > 3"),
    ),
    # --- the base context: a parameter's declared type -----------------
    "nat_bound_vs_requires": _Route(
        "plain", "author", ", @Nat", ("@Nat.0 < 0",), ("@Nat.0 > 0",),
    ),
    # --- the base context: a refined parameter's predicate -------------
    "refinement_vs_requires": _Route(
        "plain", "author", ", @Neg", ("@Neg.0 > 5",), ("@Neg.0 < -5",),
    ),
    "refinement_vs_refinement": _Route(
        "plain", "author", ", @Neg, @Pos",
        ("@Neg.0 == @Pos.0",), ("@Neg.0 < @Pos.0",),
    ),
    # --- `_path_conditions`: the `assume` half -------------------------
    "assume_pair": _Route(
        "plain", "author", "", ("true",), ("true",),
        "assume(@Int.0 > 5);\n  assume(@Int.0 < 3);",
        "assume(@Int.0 > 5);\n  assume(@Int.0 > 3);",
    ),
    "assume_vs_requires": _Route(
        "plain", "author", "", ("@Int.0 > 5",), ("@Int.0 > 5",),
        "assume(@Int.0 < 3);", "assume(@Int.0 > 3);",
    ),
    "refinement_vs_assume": _Route(
        "plain", "author", ", @Neg", ("true",), ("true",),
        "assume(@Neg.0 > 5);", "assume(@Neg.0 < -5);",
    ),
    # --- a nested scope with its own contract --------------------------
    "where_helper_contract": _Route(
        "where", "author", "",
        ("@Int.0 > 5 && @Int.0 < 3",), ("@Int.0 > 5 && @Int.0 > 3",),
    ),
    # --- `_path_conditions`: the branch half, which must NOT demote -----
    "branch_guard": _Route(
        "branch", "path", "", ("@Int.0 > 5",), ("@Int.0 > 5",),
    ),
    "match_arm_fact": _Route(
        "match", "path", "", ("@Int.0 > 5",), ("@Int.0 >= 0",),
    ),
}


class _Kind(NamedTuple):
    """One kind of obligation to discharge against the route's premises.

    *ensures* is the subject's postcondition and *body* its body, chosen so
    that under a SATISFIABLE premise set the obligation is NOT verified — the
    status premise each cell asserts, without which "not verified under the
    contradiction" would be satisfied by an obligation that was never
    provable in the first place.
    """

    ensures: str
    body: str


_KINDS: dict[str, _Kind] = {
    "ensures": _Kind("@Int.result == 42", "0"),
    "assert": _Kind("true", "assert(@Int.0 == 424242);\n  0"),
    "call_pre": _Kind("true", "needs_big(@Int.0)"),
    "refine_bind": _Kind("true", "let @Pos = @Int.0;\n  @Pos.0"),
    "nat_bind": _Kind("true", "let @Nat = @Int.0 - 100;\n  @Nat.0"),
    "int_overflow": _Kind("true", "@Int.0 * @Int.0"),
}

# Products that are NOT cells, with the reason (CONTRIBUTING.md § Bugs: the
# class, not the instance requires each one stated).
_NOT_CELLS = {
    # A literal pattern PINS the scrutinee, so the product is a constant on
    # both sides of the differential and `int_overflow` reads `verified`
    # whether or not the arm fact contradicts anything.  The cell could not
    # tell the contradiction from the bound, which is worse than not having
    # it.
    ("match_arm_fact", "int_overflow"),
}

_MATRIX_PRELUDE = """\
type Pos = { @Int | @Int.0 > 1000000 };
type Neg = { @Int | @Int.0 < 0 };

private fn needs_big(@Int -> @Int)
  requires(@Int.0 > 1000000)
  ensures(true)
  effects(pure)
{
  @Int.0
}
"""


def _indent(text: str, spaces: int) -> str:
    pad = " " * spaces
    return ("\n" + pad).join(text.split("\n"))


def _render(route_name: str, kind_name: str, *, sat: bool) -> str:
    """The subject program for one cell, on the satisfiable or the UNSAT side."""
    route, kind = _ROUTES[route_name], _KINDS[kind_name]
    clauses = route.sat_requires if sat else route.unsat_requires
    preamble = route.sat_preamble if sat else route.unsat_preamble
    req = "".join(f"  requires({c})\n" for c in clauses)
    pre = f"  {preamble}\n" if preamble else ""

    if route.shape == "where":
        # The contradiction is the HELPER's, so the parent stays healthy and
        # the helper's own slice is what must be refused.
        return (
            f"{_MATRIX_PRELUDE}\n"
            f"public fn subject(@Int -> @Int)\n"
            f"  requires(@Int.0 > 5)\n"
            f"  ensures(true)\n"
            f"  effects(pure)\n"
            f"{{\n  helper(@Int.0)\n}}\n"
            f"where {{\n"
            f"  fn helper(@Int -> @Int)\n"
            f"{_indent(req.rstrip(), 2)}\n"
            f"    ensures({kind.ensures})\n"
            f"    effects(pure)\n"
            f"  {{\n    {_indent(kind.body, 4)}\n  }}\n"
            f"}}\n"
        )

    if route.shape == "branch":
        # dead vs live, with a live guard that does NOT bound the arithmetic —
        # `@Int.0 < 300` would make `int_overflow` verified on both sides.
        guard = "@Int.0 < 3" if not sat else "@Int.0 > 3"
        body = (
            f"if {guard} then {{\n    {_indent(kind.body, 4)}\n"
            f"  }} else {{\n    0\n  }}"
        )
    elif route.shape == "match":
        body = (
            f"match @Int.0 {{\n    0 -> {{\n      "
            f"{_indent(kind.body, 6)}\n    }},\n    _ -> 0\n  }}"
        )
    else:
        body = kind.body

    return (
        f"{_MATRIX_PRELUDE}\n"
        f"public fn subject(@Int{route.params} -> @Int)\n"
        f"{req}"
        f"  ensures({kind.ensures})\n"
        f"  effects(pure)\n"
        f"{{\n{pre}  {body}\n}}\n"
    )


def _slice_from(result: dict, source: str, marker: str) -> list[dict]:
    """The obligations of the function whose declaration starts at *marker*.

    Scoped by line rather than by counting, so a fixture that stops producing
    the shape it means to produce shows up as an empty slice rather than as
    an assertion that happens to hold over someone else's obligations.
    """
    first = [
        i for i, line in enumerate(source.splitlines(), start=1)
        if line.lstrip().startswith(marker)
    ]
    assert len(first) == 1, f"{marker!r} is not unique in the fixture"
    return [o for o in result["obligations"] if o["location"]["line"] >= first[0]]


_MATRIX_CELLS = [
    (r, k) for r in _ROUTES for k in _KINDS if (r, k) not in _NOT_CELLS
]


@pytest.mark.parametrize(("route_name", "kind_name"), _MATRIX_CELLS)
def test_1451_vacuity_matrix(
    route_name: str, kind_name: str, tmp_path: Path,
) -> None:
    """Every route to an unsatisfiable premise set, crossed with every kind.

    Each cell is a DIFFERENTIAL, not a literal-status assertion: the same body
    and the same obligation kind are rendered twice, once with the route's
    premises contradictory and once with them satisfiable, and both sides are
    asserted.  The satisfiable side is the status premise — it proves the
    fixture really produces an obligation of this kind and that the obligation
    is NOT provable, so "not verified under the contradiction" cannot be
    satisfied by an obligation that was absent or unprovable anyway.

    For an ``author``-layer route the contradictory side must report the
    vacuity (E538) and certify NOTHING in the affected function.  For a
    ``path``-layer route it must do neither: a branch or arm whose guard
    cannot hold under the precondition is unreachable, its obligations are
    discharged under that guard by construction, and demoting the function for
    it would report the program's own shape as a defect.  That cell is the
    over-reach guard on the other cells — a check that folded path conditions
    into layer 1 would pass every ``author`` row and fail these.
    """
    route = _ROUTES[route_name]
    marker = "fn helper(" if route.shape == "where" else "public fn subject("

    sat_src = _render(route_name, kind_name, sat=True)
    sat = _verify(_write(tmp_path / "sat", sat_src))
    sat_slice = _slice_from(sat, sat_src, marker)
    assert "E538" not in _codes(sat), (route_name, kind_name, _codes(sat))
    assert "E539" not in _codes(sat), (route_name, kind_name, _codes(sat))
    if kind_name == "call_pre":
        # A PROVABLE call precondition records no obligation at all (only the
        # `violated` and `tier3` recorders exist), so the premise here is the
        # refusal itself: with satisfiable premises this program is rejected.
        assert ("call_pre", "violated", "E501") in _triples(sat), _triples(sat)
        assert sat["ok"] is False, sat["verification"]
    else:
        target = [o for o in sat_slice if o["kind"] == kind_name]
        assert target, (
            f"{route_name}/{kind_name}: the fixture produced no {kind_name} "
            f"obligation, so the cell would hold vacuously — "
            f"{[o['kind'] for o in sat_slice]}"
        )
        assert all(o["status"] != "verified" for o in target), (
            f"{route_name}/{kind_name}: provable under satisfiable premises, "
            f"so the contradictory side proves nothing — "
            f"{[(o['status'], o.get('error_code')) for o in target]}"
        )

    unsat_src = _render(route_name, kind_name, sat=False)
    unsat = _verify(_write(tmp_path / "unsat", unsat_src))
    unsat_slice = _slice_from(unsat, unsat_src, marker)

    if route.layer == "author":
        assert "E538" in _codes(unsat), (
            f"{route_name}/{kind_name}: the premise set has no model and the "
            f"run said nothing — {_codes(unsat)} / {_triples(unsat)}"
        )
        assert not [o for o in unsat_slice if o["status"] == "verified"], (
            f"{route_name}/{kind_name}: certified under a premise set with no "
            f"model — {[(o['kind'], o['status']) for o in unsat_slice]}"
        )
        assert all(
            o["status"] in ("tier3_unguarded", "violated") for o in unsat_slice
        ), [(o["kind"], o["status"]) for o in unsat_slice]
        # ... and the program is REFUSED, on every author row.  E538 is an
        # error, so the refusal is the signal the author gets at the
        # definition rather than a tier they have to go and read.
        assert unsat["ok"] is False, (route_name, kind_name, _codes(unsat))
        if kind_name == "call_pre":
            # Say what the contradiction actually bought, rather than only
            # that E538 fired: the call whose precondition the satisfiable
            # side REFUSES is here proved from the contradiction, so it
            # records no obligation IN THIS FUNCTION and the disclosure is the
            # only thing standing between that and a silent false Tier 1.
            assert not [
                o for o in unsat_slice if o["kind"] == "call_pre"
            ], _triples(unsat)
            # The `where` shape refuses TWICE over, and the second refusal is
            # load-bearing: the contradiction is the HELPER's, so the PARENT's
            # call to it is a genuine E501 beside the helper's own E538.  The
            # call site answering separately is what covers a callee compiled
            # from another module, where this run never sees the definition.
            if route.shape == "where":
                assert ("call_pre", "violated", "E501") in _triples(
                    unsat), _triples(unsat)
            else:
                assert "E501" not in _codes(unsat), _codes(unsat)
    else:
        assert "E538" not in _codes(unsat), (
            f"{route_name}/{kind_name}: an unreachable arm is the program's "
            f"shape, not a contradictory premise set — {_codes(unsat)}"
        )
        assert "E539" not in _codes(unsat), _codes(unsat)
        # ... and the differential holds: the arm fact really does contradict
        # the precondition, which is what the `verified` above rests on.
        dead = [o for o in unsat_slice if o["kind"] == kind_name]
        live = [o for o in sat_slice if o["kind"] == kind_name]
        if kind_name == "ensures":
            # A function-level obligation is outside the arm, so the dead arm
            # must not move it: it stays refuted on both sides.
            assert [o["status"] for o in dead] == ["violated"], dead
        elif kind_name == "call_pre":
            # The satisfiable side refuses this program (asserted above); the
            # dead arm's call precondition is proved from the arm fact, so it
            # records nothing and the program is accepted.  Assert BOTH, or
            # the cell says only that no E538 fired — which a check that had
            # stopped running entirely would also satisfy.
            assert unsat["ok"] is True, _triples(unsat)
            assert dead == [], _triples(unsat)
        else:
            assert [o["status"] for o in dead] == ["verified"], dead
            assert all(o["status"] != "verified" for o in live), live


@pytest.mark.parametrize("route_name", ["branch_guard", "match_arm_fact"])
def test_1451_a_path_local_contradiction_certifies_nothing_a_run_reaches(
    route_name: str, tmp_path: Path,
) -> None:
    """The soundness the `path` rows rest on, measured rather than argued.

    Those rows accept a `verified` obligation discharged under a premise set
    with no model, on the ground that no call can enter the arm.  That is a
    claim about the RUN, so the run is what settles it: the `nat_bind` the
    dead arm certifies is one whose violation traps loudly, and an argument
    satisfying the precondition must return the other branch's value instead
    of reaching it.
    """
    src = _render(route_name, "nat_bind", sat=False)
    path = _write(tmp_path, src)
    verdict = _verify(path)
    assert "E538" not in _codes(verdict), _codes(verdict)
    # The premise: the arm really does certify a `nat_bind` from the
    # contradiction.  Without it the run below would pass over a program that
    # had no vacuous proof in it to be unreachable.
    assert ("nat_bind", "verified", None) in _triples(verdict), _triples(verdict)
    proc = _cli("run", str(path), "--fn", "subject", "--", "7")
    assert proc.returncode == 0, (proc.stdout, proc.stderr[-600:])
    # The OTHER branch's value, exactly — `in` would be satisfied by a trap
    # message that happened to contain a zero.
    assert proc.stdout.strip() == "0", proc.stdout
    assert "Nat" not in proc.stderr, proc.stderr[-600:]


# ---------------------------------------------------------------------------
# Round two of the adversarial review of PR #1457
# ---------------------------------------------------------------------------

_ASSUME_OVER_A_CALL = """\
private fn g(@Int -> @Int)
  requires(true)
  ensures(@Int.result > 100)
  effects(pure)
{
  101
}

public fn caller(@Int -> @Int)
  requires(@Int.0 == 1)
  ensures(@Int.result == 42)
  effects(pure)
{
  assume(g(@Int.0) < 0);
  0
}
"""

_ASSUME_AFTER_A_LET = _ASSUME_OVER_A_CALL.replace(
    "  assume(g(@Int.0) < 0);\n",
    "  let @Int = g(@Int.0);\n  assume(@Int.0 < 0);\n",
)


@pytest.mark.parametrize(
    "source", [
        pytest.param(_ASSUME_OVER_A_CALL, id="assume-over-a-call"),
        pytest.param(_ASSUME_AFTER_A_LET, id="assume-after-a-let"),
    ],
)
def test_1451_the_screen_reads_the_terms_the_obligations_ran_under(
    source: str, tmp_path: Path,
) -> None:
    """RED before: a second walk answered about a premise set nobody ran under.

    Translating a predicate has EFFECTS.  A call inside one mints a fresh call
    constant, constrained only by the guarded implication the same walk adds
    to the base context.  The first draft of the `assume` layer walked the
    body TWICE — once to thread `_path_conditions`, once with `assumes_only`
    to collect premises — so the screen was handed a fact about `_call_g_5`
    while every obligation had been discharged under `_call_g_4`.  It answered
    `sat` about a set no obligation ran under, and `ensures(@Int.result ==
    42)` stayed VERIFIED over a body returning `0`, with `vera run --fn caller
    -- 1` trapping on the postcondition the run had just certified.

    Both spellings are cells because the second walk re-translated preceding
    top-level `let` right-hand sides too, not only the `assume` predicate, so
    a `let` in front of the `assume` reproduced it identically.  One walk now,
    partitioned, handing the screen the very terms `_path_conditions` got.
    """
    result = _verify(_write(tmp_path, source))
    assert not [
        o for o in result["obligations"]
        if o["kind"] == "ensures" and o["status"] == "verified"
        and o["location"]["line"] > 8
    ], _triples(result)
    assert "E539" in _codes(result), (_codes(result), _triples(result))
    caller_obls = [
        o for o in result["obligations"] if o["location"]["line"] > 8
    ]
    assert caller_obls and all(
        o["status"] == "tier3_unguarded" for o in caller_obls
    ), _triples(result)


_PELL_50 = """\
public fn f(@Int, @Int -> @Int)
  requires(@Int.0 > 0 && @Int.0 < 50 && @Int.1 > 0 && @Int.1 < 50 && @Int.0 * @Int.0 == 2 * (@Int.1 * @Int.1))
  ensures(@Int.result == 42)
  effects(pure)
{
  0
}
"""

_PELL_60 = """\
public fn f(@Int, @Int -> @Int)
  requires(@Int.0 > 0 && @Int.0 < 60 && @Int.1 > 0 && @Int.1 < 60 && @Int.0 * @Int.0 == 2 * (@Int.1 * @Int.1))
  ensures(@Int.result == 42)
  effects(pure)
{
  0
}
"""


def test_1451_a_contradiction_beyond_the_screening_budget_is_still_caught(
    tmp_path: Path,
) -> None:
    """RED before: the screen was narrower than the budget the vacuity used.

    `x * x == 2 * (y * y)` with `0 < x, y < 60` has no integer model — the
    irrationality of the square root of two, in sixty cases — but Z3 needs
    about a second to say so, not the 250 ms the screening query is given.
    The first draft demoted only on a REFUTATION and asked nothing else, so
    every contradiction refutable between 250 ms and the run's budget was
    missed in silence: `ensures(@Int.result == 42)` VERIFIED over a body
    returning `0`, exactly the issue's repro with a slower contradiction.

    The author's layer is what closes it, and it is asked at the RUN's budget
    rather than the screen's, so `--timeout-ms` now widens detection instead
    of only widening the obligation queries it is competing with.
    """
    # An explicit, generous budget, because the point of the cell is that
    # detection now scales with `--timeout-ms` rather than with stage 1's
    # 250 ms: this refutation needs about eight seconds of real search, and a
    # cell that raced the default would measure the machine's load rather
    # than the check.  The cost is paid once, here, deliberately — the
    # division of labour between the stages is pinned by the cell below,
    # which injects stage 1's verdict instead of waiting for it.
    path = _write(tmp_path, _PELL_60)
    proc = _cli("verify", "--json", "--timeout-ms", "120000", str(path))
    result = json.loads(proc.stdout)
    assert "E538" in _codes(result), (_codes(result), _triples(result))
    assert result["verification"]["tier1_verified"] == 0, (
        result["verification"])
    assert not [
        o for o in result["obligations"]
        if o["kind"] == "ensures" and o["status"] == "verified"
    ], _triples(result)


def test_1451_the_second_stage_refutes_on_the_quantifier_free_subset(
    tmp_path: Path,
) -> None:
    """The two stages divide the work the way their budgets can afford.

    Stage 1 asks the WHOLE premise set at a short budget: a contradiction
    that propagates is refuted there even under rank axioms.  Stage 2 asks the
    quantifier-free SUBSET at the discharge budget, which is sound because a
    refutation on a subset is a refutation on the whole, and affordable
    because the rank axioms are what send Z3 to MBQI.

    Both verdicts are asserted, on both fixtures, because the division is the
    claim: the Pell contradiction must be invisible to stage 1 and refuted by
    stage 2 (a one-stage screen at the short budget misses it, which is what
    #1457's High 2 measured), while a recursive-ADT measure must be undecided
    at stage 1 and ACCEPTED by stage 2 — a stage 2 that refuted it would be
    demoting a program that verifies.
    """
    from vera import verifier as vmod

    seen: list[tuple[str, str]] = []
    o_full = vmod.ContractVerifier._full_premises_satisfiable
    o_qf = vmod.ContractVerifier._quantifier_free_premises_satisfiable
    label = {True: "sat", False: "unsat", None: "unknown"}

    def blind_stage1(self, smt, assumed):  # type: ignore[no-untyped-def]
        seen.append(("stage1", "unknown"))
        return None

    def spy_full(self, smt, assumed):  # type: ignore[no-untyped-def]
        v = o_full(self, smt, assumed)
        seen.append(("stage1", label[v]))
        return v

    def spy_qf(self, smt, assumed):  # type: ignore[no-untyped-def]
        v = o_qf(self, smt, assumed)
        seen.append(("stage2", label[v]))
        return v

    vmod.ContractVerifier._quantifier_free_premises_satisfiable = spy_qf  # type: ignore[assignment]
    try:
        # Stage 1 BLINDED, on a contradiction it would otherwise refute in a
        # fifth of a second.  The alternative — a fixture hard enough that
        # stage 1 really times out — costs eight seconds of search and races
        # the machine's load, which measures the host rather than the design.
        # Injecting the verdict pins the same property in milliseconds: what
        # stage 1 does not decide, stage 2 must refute.
        vmod.ContractVerifier._full_premises_satisfiable = blind_stage1  # type: ignore[assignment]
        seen.clear()
        # An explicit, generous budget for the same reason the end-to-end cell
        # carries one: this refutation needs seconds of real search, and at
        # the default 10 s it finishes with about 2.8 s to spare on a loaded
        # host.  A cell that close to its budget measures the machine, and
        # what it would report is `unknown` — the verdict this leg exists to
        # rule out.  Stage 2's budget IS the discharge budget, so raising it
        # is the whole remedy; it caps the query and does not lengthen it.
        hard = _verify_in_process(
            _write(tmp_path / "hard", _PELL_50), timeout_ms=120_000,
        )
        hard_seen = list(seen)

        # Unblinded, so the rank-axiom leg measures the real stage 1.
        vmod.ContractVerifier._full_premises_satisfiable = spy_full  # type: ignore[assignment]
        seen.clear()
        rank = _verify_in_process(_write(tmp_path / "rank", _RECURSIVE_MEASURE))
        rank_seen = list(seen)
    finally:
        vmod.ContractVerifier._full_premises_satisfiable = o_full  # type: ignore[assignment]
        vmod.ContractVerifier._quantifier_free_premises_satisfiable = o_qf  # type: ignore[assignment]

    # `verify_program` re-verifies while the disclosed set moves, so both
    # fixtures are screened more than once and the verdicts are asserted as
    # OCCURRENCES rather than as a fixed sequence.
    assert ("stage2", "unsat") in hard_seen, hard_seen
    assert "E538" in [d.error_code for d in hard.diagnostics], hard_seen
    assert hard.summary.tier1_verified == 0, hard.summary

    # And the other half of the division: a recursive-ADT measure must be
    # UNDECIDED at stage 1 — the real one, not the blind one — and ACCEPTED by
    # stage 2, since a stage 2 that refuted it would demote a program that
    # verifies.
    assert ("stage1", "unknown") in rank_seen, rank_seen
    assert ("stage2", "unsat") not in rank_seen, rank_seen
    assert not [
        d for d in rank.diagnostics if d.error_code in ("E538", "E539")
    ], rank_seen
    assert rank.summary.tier1_verified > 0, rank.summary


def test_1451_vera_test_does_not_call_a_demoted_function_tier_1(
    tmp_path: Path,
) -> None:
    """The demotion has to reach every consumer, not only `verify --json`.

    `vera test` partitioned functions by `status in ("tier3", "timeout")` to
    decide which contracts were proved.  A demoted obligation is neither, so
    the issue's own repro printed "VERIFIED (Tier 1)" and skipped its trials —
    the false Tier 1 this PR exists to stop, surviving in a second reader
    (#1457 review, Medium 2).  The class property is observable: no consumer
    may report a premise set with no model as a proof.
    """
    proc = _cli("test", str(_write(tmp_path, _UNSAT_REQUIRES)))
    assert "Tier 1" not in proc.stdout, proc.stdout
    assert "VERIFIED" not in proc.stdout, proc.stdout
    assert "unsatisfiable" in proc.stdout, proc.stdout
    # ... and it agrees with `vera verify` about the program, now that E538 is
    # an error: a reader that printed the refusal and exited 0 would be the
    # same disagreement between two consumers in a quieter form.
    assert proc.returncode == 1, (proc.returncode, proc.stdout)


def test_1451_the_lsp_does_not_call_a_demoted_function_tier_1(
    tmp_path: Path,
) -> None:
    """... and neither does the editor.

    `_tier_hints` said "Tier 1 — all contracts proven by Z3" whenever no
    obligation was `tier3` or `timeout`, which a wholly demoted slice
    satisfies.  The control is the healthy twin, which must still read Tier 1:
    a hint that had stopped claiming anything would pass the first assertion
    on its own.
    """
    from types import SimpleNamespace

    from vera.lsp.features import _tier_hints

    def hints(path: Path) -> str:
        result = _verify_in_process(path)
        analysis = SimpleNamespace(
            obligations=result.obligations,  # type: ignore[attr-defined]
            path=str(path),
        )
        return " ".join(
            d.message for d in _tier_hints(analysis))  # type: ignore[arg-type]

    bad_text = hints(_write(tmp_path / "bad", _UNSAT_REQUIRES))
    good_text = hints(_write(tmp_path / "ok", _HEALTHY))
    assert "Tier 1" not in bad_text, bad_text
    assert "neither proved nor guarded" in bad_text, bad_text
    assert "Tier 1" in good_text, good_text


# ---------------------------------------------------------------------------
# The completeness condition, asserted rather than measured
# ---------------------------------------------------------------------------
#
# Stage 2 drops the QUANTIFIED premises and asks the rest.  That is sound
# whatever it drops — a refutation on a subset is a refutation on the whole —
# and it is COMPLETE, so that a `sat` there really does mean the whole set has
# a model, exactly while the two halves share no uninterpreted symbol: a model
# of the quantifier-free half then extends to one of the whole set by
# interpreting the dropped symbols freely, which for the rank axioms a
# `decreases` measure installs is structural depth.
#
# That is a property of what the verifier ASSERTS, not of this check, so it
# can lapse from anywhere — a new quantified premise (Tier 2 hints, #427), or
# an existing one growing a term over a rank symbol.  Asserting it here is
# what turns "by measurement at this revision" into a condition that cannot
# lapse in silence.


def _uninterpreted_symbols(expr: object) -> set[str]:
    """The uninterpreted function and constant names occurring in *expr*.

    Datatype constructors, accessors and recognizers carry their own decl
    kinds and are NOT collected: they are interpreted by the datatype
    declaration, shared by construction, and a model of one half never has to
    disagree with the other about them.  A quantifier's body is walked so a
    symbol applied only under a binder still counts; the bound variables
    themselves are `Var` nodes rather than applications, so they contribute
    nothing.
    """
    import z3

    out: set[str] = set()
    stack: list[object] = [expr]
    seen: set[int] = set()
    while stack:
        node = stack.pop()
        node_id = node.get_id()  # type: ignore[attr-defined]
        if node_id in seen:
            continue
        seen.add(node_id)
        if z3.is_quantifier(node):
            stack.append(node.body())  # type: ignore[attr-defined]
            continue
        if z3.is_app(node):
            decl = node.decl()  # type: ignore[attr-defined]
            if decl.kind() == z3.Z3_OP_UNINTERPRETED:
                out.add(decl.name())
            stack.extend(node.children())  # type: ignore[attr-defined]
    return out


def _symbol_halves(facts: list[object]) -> tuple[set[str], set[str]]:
    """Split *facts* the way stage 2 does, and collect each half's symbols."""
    import z3

    quantified: set[str] = set()
    free: set[str] = set()
    for fact in facts:
        has_q = any(
            z3.is_quantifier(sub)
            for sub in _subterms(fact)
        )
        (quantified if has_q else free).update(_uninterpreted_symbols(fact))
    return quantified, free


def _subterms(expr: object) -> list[object]:
    import z3

    out: list[object] = []
    stack: list[object] = [expr]
    seen: set[int] = set()
    while stack:
        node = stack.pop()
        node_id = node.get_id()  # type: ignore[attr-defined]
        if node_id in seen:
            continue
        seen.add(node_id)
        out.append(node)
        if z3.is_quantifier(node):
            stack.append(node.body())  # type: ignore[attr-defined]
        elif z3.is_app(node):
            stack.extend(node.children())  # type: ignore[attr-defined]
    return out


def test_1451_the_instrument_sees_a_shared_symbol() -> None:
    """The differential's negative control: it can fail.

    A quantified fact and a quantifier-free one over the SAME uninterpreted
    function is the shape that would make stage 2's `sat` mean nothing, since
    the quantifier-free model would then have to agree with the dropped axiom.
    Built by hand rather than found, because no program produces it — which is
    the claim the corpus leg makes, and which would be unfalsifiable without
    this one.
    """
    import z3

    rank = z3.Function("rank_list", z3.IntSort(), z3.IntSort())
    x, y = z3.Int("x"), z3.Int("y")

    shared_q, shared_free = _symbol_halves(
        [z3.ForAll([x], rank(x) >= 0), rank(3) == 7],
    )
    assert shared_q & shared_free == {"rank_list"}, (shared_q, shared_free)

    ok_q, ok_free = _symbol_halves([z3.ForAll([x], rank(x) >= 0), y > 0])
    assert not (ok_q & ok_free), (ok_q, ok_free)
    # ... and the halves are both non-empty, or "disjoint" would be the
    # instrument reporting that it collected nothing.
    assert ok_q == {"rank_list"} and ok_free == {"y"}, (ok_q, ok_free)


def test_1451_no_corpus_premise_set_shares_a_symbol_across_the_split() -> None:
    """Stage 2 is refutation-COMPLETE on every corpus program that has ranks.

    The context step 8c screens is captured as the check sees it — the
    solver's base assertions plus the top-level `assume` facts folded in by
    `check_valid` — split into the two halves stage 2 splits it into, and the
    uninterpreted symbols of each collected.  An empty intersection is the
    hypothesis of the extension argument in spec §6.8.2; a shared symbol is a
    soundness finding about the SCREEN, not about the program.

    Over every corpus program carrying a `decreases` measure, which is where
    quantified premises come from today.  Two counts are asserted beside the
    disjointness: the programs really were screened, and at least one context
    really had a quantified half — without which every intersection is empty
    because one side is.
    """
    import vera
    from vera import verifier as vmod

    root = Path(vera.__file__).resolve().parents[1]
    programs = sorted(
        p for p in (
            *(root / "tests" / "conformance").glob("*.vera"),
            *(root / "examples").glob("*.vera"),
        )
        if "decreases(" in p.read_text(encoding="utf-8")
    )
    assert len(programs) >= 10, [p.name for p in programs]

    captured: list[tuple[str, str, list[object]]] = []
    original = vmod.ContractVerifier._enforce_premise_consistency

    def capture(self, decl, smt, obl_start, contract, assumed):  # type: ignore[no-untyped-def]
        captured.append(
            (self._current_file, decl.name,
             [*smt.solver.assertions(), *assumed]),
        )
        return original(self, decl, smt, obl_start, contract, assumed)

    vmod.ContractVerifier._enforce_premise_consistency = capture  # type: ignore[assignment]
    try:
        screened = 0
        for path in programs:
            try:
                _verify_in_process(path)
            except Exception:  # noqa: BLE001 — a negative fixture, skipped
                continue
            screened += 1
    finally:
        vmod.ContractVerifier._enforce_premise_consistency = original  # type: ignore[assignment]

    assert screened >= 10, screened
    assert captured, "no premise set was screened at all"

    with_quantifiers = 0
    shared: list[tuple[str, str, set[str]]] = []
    for file, fn_name, facts in captured:
        quantified, free = _symbol_halves(facts)
        if quantified:
            with_quantifiers += 1
        overlap = quantified & free
        if overlap:
            shared.append((Path(file).name, fn_name, overlap))

    assert with_quantifiers > 0, (
        f"no captured premise set had a quantified half, so the disjointness "
        f"below holds for the wrong reason — {len(captured)} contexts"
    )
    assert not shared, (
        f"a quantifier-free premise mentions a symbol only the quantified "
        f"premises constrain, so stage 2's `sat` no longer implies the whole "
        f"set has a model (spec §6.8.2) — {shared}"
    )
