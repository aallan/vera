"""#1406 / #1407 — a disclosed fact's taint follows the VALUE, not the syntax.

#1363 established the rule: a declared-type fact whose own obligation this run
DISCLOSED (`tier3_unguarded`, or `tier3` with E534 — neither proved nor
guarded) must not discharge a downstream goal at Tier 1.  Its implementation
asked a syntactic question — is this `match` scrutinee spelled as a call to a
disclosed function — and a syntactic question has as many answers as there are
spellings.  Two of them defeated it outright:

* **#1406** — `let @T = mk(x); match @T.0 { … }`.  The scrutinee arrives as a
  slot reference, so the test answered False and the facts were handed to the
  solver at full strength.  One token, and the rule was gone.
* **#1407** — `fn wrap(…) { mk(x) }`, then `match wrap(x) { … }`.  A forwarder
  makes no claim that needs the disclosed fact, so it contributes no
  obligation, so `disclosed_fn_names` — which reads the obligation stream —
  never sees it, at any depth.

Both are the same unsoundness as #1363, reached by a different route, and both
are measured here the only way that settles it: the postcondition is
`verified` at Tier 1 and the compiled program refutes it.

THE CARRIER IS LOAD-BEARING.  `Option<PosInt>` is used rather than the tuple
of #1363's own reproducer because codegen guards a refined RETURN and a
refined TUPLE COMPONENT at the function boundary — the tuple shape traps
inside `mk` and never reaches the caller's postcondition, so it can exhibit a
status difference but not a runtime one.  An ADT payload is guarded nowhere,
so the disclosed fact is genuinely unenforced and `f`'s contract really is
refutable.  `float_to_int` supplies the opacity: the payload's `> 0` can be
neither proved nor refuted, which is what `tier3_unguarded` means.  A
refutable narrowing would be `violated`/E505 — an error, not a disclosure —
and would exhibit nothing.

EVERY SPELLING CARRIES ITS CLEAN CONTROL.  The two differ in `mk`'s body
alone: `Some(float_to_int(@Float64.0))` discloses, `Some(7)` proves.  Same
name, same signature, same call at the caller.  Without the control a fix that
demoted every `match` would pass the whole file, and the controls are what
measure that it does not — none of them may leave `verified`.
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
        env=env, timeout=300,
    )


def _verify(tmp_path: Path, source: str, name: str = "p.vera") -> dict:
    p = tmp_path / name
    p.write_text(source, encoding="utf-8")
    proc = _cli("verify", "--json", str(p))
    try:
        result = json.loads(proc.stdout)
    except json.JSONDecodeError:
        raise AssertionError(
            f"verify emitted no envelope (exit {proc.returncode})\n"
            f"{proc.stdout[:400]}\n{proc.stderr[-600:]}"
        ) from None
    # An UNRESOLVED call verifies "clean" with only an E200 warning, and its
    # result is opaque — so a fixture that forgot to declare its producer
    # exhibits a plausible-looking demotion for a reason that has nothing to
    # do with disclosure.  That is not hypothetical: two cells in this file
    # were written without `mk` and passed.  Every fixture here is checked for
    # it before its verdict is read.
    assert "E200" not in [w.get("error_code") for w in result["warnings"]], (
        f"fixture calls an undeclared function, so its obligations are opaque "
        f"for a reason unrelated to disclosure:\n{source}"
    )
    return result


def _run(tmp_path: Path, source: str, arg: str = "-7.0") -> str:
    """Compile and call `f` with *arg*; return stdout+stderr.

    The default `-7.0` is chosen so no fallback can coincide with it: it is
    neither `0` nor the `None` arm's `41`, so a wrong answer cannot be read as
    a right one (the payload the disclosed `mk` builds is `-7`).
    """
    p = tmp_path / "r.vera"
    p.write_text(source, encoding="utf-8")
    proc = _cli("run", str(p), "--fn", "f", "--", arg)
    return proc.stdout + proc.stderr


# ---------------------------------------------------------------------------
# The fixture family: one caller spelling x {disclosed, clean} producer
# ---------------------------------------------------------------------------

_POSINT = "type PosInt = { @Int | @Int.0 > 0 };\n"

_MK_DISCLOSED = """
private fn mk(@Float64 -> @Option<PosInt>)
  requires(true)
  ensures(true)
  effects(pure)
{
  Some(float_to_int(@Float64.0))
}
"""

_MK_CLEAN = """
private fn mk(@Float64 -> @Option<PosInt>)
  requires(true)
  ensures(true)
  effects(pure)
{
  Some(7)
}
"""

# A second CLEAN producer, so the `if`-join has two arms neither of which is
# constructed here.  A `None` arm would make the joined term a constructor
# application, which `_is_locally_constructed` already drops the facts for
# (#1332) — the join would then fail for a reason that has nothing to do with
# disclosure, and would exhibit nothing about the `ite` walk.
_MK2 = """
private fn mk2(@Float64 -> @Option<PosInt>)
  requires(true)
  ensures(true)
  effects(pure)
{
  Some(9)
}
"""

_ARMS = """    Some(@PosInt) -> @PosInt.0,
    None -> 41"""

_F = """
public fn f(@Float64 -> @Int)
  requires(true)
  ensures(@Int.result > 0)
  effects(pure)
"""

_WRAP = """
private fn wrap(@Float64 -> @Option<PosInt>)
  requires(true)
  ensures(true)
  effects(pure)
{
  mk(@Float64.0)
}
"""

#: caller spelling → the declarations after `mk`.  Every one of them reaches
#: the same `match` over the same value; only the route differs.
_SPELLINGS: dict[str, str] = {
    # The one #1363 already handled — the control that pins the axis.
    "direct": _F + "{\n  match mk(@Float64.0) {\n" + _ARMS + "\n  }\n}\n",
    # #1406, the issue's own shape.
    "let_bound": _F + "{\n  let @Option<PosInt> = mk(@Float64.0);\n"
                      "  match @Option<PosInt>.0 {\n" + _ARMS + "\n  }\n}\n",
    # Rebound a second time: the taint has to survive a chain, not one hop.
    "let_chain": _F + "{\n  let @Option<PosInt> = mk(@Float64.0);\n"
                      "  let @Option<PosInt> = @Option<PosInt>.0;\n"
                      "  match @Option<PosInt>.0 {\n" + _ARMS + "\n  }\n}\n",
    # A branch join: disclosed on one arm only, so the `ite` walk is what
    # answers.  Reading only the root term would miss this.
    "ite_join": _MK2 + _F + "{\n  let @Option<PosInt> = if @Float64.0 > 0.0 then {\n"
                            "    mk(@Float64.0)\n  } else {\n"
                            "    mk2(@Float64.0)\n  };\n"
                            "  match @Option<PosInt>.0 {\n" + _ARMS + "\n  }\n}\n",
    # A pipe desugars to a call inside the SMT layer, but the AST node the
    # syntactic test sees is a pipe.  Nothing in the fix names pipes.
    "pipe": _F + "{\n  match @Float64.0 |> mk() {\n" + _ARMS + "\n  }\n}\n",
    # #1407, the issue's own shape.
    "wrap1": _WRAP + _F + "{\n  match wrap(@Float64.0) {\n" + _ARMS + "\n  }\n}\n",
    # Two hops: the fixpoint has to carry it further than one pass.
    "wrap2": _WRAP + """
private fn wrap_outer(@Float64 -> @Option<PosInt>)
  requires(true)
  ensures(true)
  effects(pure)
{
  wrap(@Float64.0)
}
""" + _F + "{\n  match wrap_outer(@Float64.0) {\n" + _ARMS + "\n  }\n}\n",
    # Both bugs at once: the wrapper reaches its result through a `let`.
    "wrap_let": """
private fn wrap(@Float64 -> @Option<PosInt>)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Option<PosInt> = mk(@Float64.0);
  @Option<PosInt>.0
}
""" + _F + "{\n  match wrap(@Float64.0) {\n" + _ARMS + "\n  }\n}\n",
    "wrap_pipe": """
private fn wrap(@Float64 -> @Option<PosInt>)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Float64.0 |> mk()
}
""" + _F + "{\n  match @Float64.0 |> wrap() {\n" + _ARMS + "\n  }\n}\n",
    # A `where` helper is a forwarder the flat registries cannot even name.
    "where_helper": _F + "{\n  match h(@Float64.0) {\n" + _ARMS + "\n  }\n}\n"
                    """where {
  fn h(@Float64 -> @Option<PosInt>)
    requires(true)
    ensures(true)
    effects(pure)
  {
    mk(@Float64.0)
  }
}
""",
}

#: The spellings that were `verified` on `origin/release/v0.2.0` and are
#: `tier3`/E534 now.  `direct` is excluded because #1363 already demoted it —
#: it is the control, not a mover.
_MOVERS = tuple(s for s in sorted(_SPELLINGS) if s != "direct")


def _source(spelling: str, *, disclosed: bool) -> str:
    mk = _MK_DISCLOSED if disclosed else _MK_CLEAN
    return _POSINT + mk + _SPELLINGS[spelling]


def _f_ensures(result: dict) -> tuple[str, str | None]:
    """`f`'s postcondition obligation, as (status, error_code).

    Keyed on the predicate text rather than on position: the spellings emit
    different numbers of obligations, and a positional read would silently
    follow the wrong one when a helper is added.
    """
    hits = [o for o in result["obligations"]
            if o["kind"] == "ensures" and o["description"] == "@Int.result > 0"]
    assert len(hits) == 1, [
        (o["kind"], o["description"], o["status"]) for o in result["obligations"]
    ]
    return hits[0]["status"], hits[0].get("error_code")


# ---------------------------------------------------------------------------
# The rule, over every spelling
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("spelling", sorted(_SPELLINGS))
def test_1406_a_disclosed_value_demotes_however_it_is_spelled(
    tmp_path: Path, spelling: str,
) -> None:
    """Same value, same `match`, ten routes — one verdict.

    The premise is checked in the same breath as the conclusion: `mk`'s own
    obligation must be `tier3_unguarded`, or this fixture is measuring
    something other than a disclosed fact and its verdict means nothing.
    """
    result = _verify(tmp_path, _source(spelling, disclosed=True))
    assert result["ok"] is True, result.get("diagnostics")
    statuses = [(o["kind"], o["status"], o.get("error_code"))
                for o in result["obligations"]]
    assert ("refine_bind", "tier3_unguarded", "E506") in statuses, (
        f"{spelling}: the producer did not disclose, so this fixture proves "
        f"nothing about a disclosed fact — {statuses}"
    )
    assert _f_ensures(result) == ("tier3", "E534"), (
        f"{spelling}: the postcondition holds only from a fact this run could "
        f"neither prove nor guard, so it is a Tier-3 truth — got "
        f"{_f_ensures(result)}"
    )


@pytest.mark.parametrize("spelling", sorted(_SPELLINGS))
def test_1406_a_clean_producer_stays_verified_through_every_spelling(
    tmp_path: Path, spelling: str,
) -> None:
    """The over-rejection control, one per spelling.

    A fix that demoted every `match` over a call result would satisfy the
    cells above and destroy Tier-1 verification for everyone else.  These are
    what measure that the demotion is keyed on DISCLOSURE: the only difference
    from the cell above is `mk`'s body.
    """
    result = _verify(tmp_path, _source(spelling, disclosed=False))
    assert result["ok"] is True, result.get("diagnostics")
    assert not [o for o in result["obligations"]
                if o["status"] == "tier3_unguarded"], (
        f"{spelling}: the control's producer disclosed something, so it is "
        f"not a clean control"
    )
    assert _f_ensures(result) == ("verified", None), (
        f"{spelling}: a clean producer's fact is established, so the "
        f"postcondition is proved — got {_f_ensures(result)}"
    )


# ---------------------------------------------------------------------------
# The runtime differential — why the demotion is not merely tidier
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("spelling", ["let_bound", "wrap1"])
def test_1406_the_demoted_contract_is_one_the_program_refutes(
    tmp_path: Path, spelling: str,
) -> None:
    """`verified` here would be a FALSE Tier 1, not a conservative one.

    The two issues' own shapes, run.  `-7.0` reaches `mk`, whose payload the
    run could neither prove nor guard, and `f`'s postcondition fails on the
    value that comes back.  Before the fix this contract was `verified` while
    the program did this, which is the definition of unsound; after it, the
    contract is Tier 3 and the runtime check is the thing that catches it.
    """
    source = _source(spelling, disclosed=True)
    assert _f_ensures(_verify(tmp_path, source)) == ("tier3", "E534")
    out = _run(tmp_path, source)
    assert "Postcondition violation in f" in out, (
        f"{spelling}: the fixture did not reach the postcondition, so it "
        f"reports no verdict about soundness — a trap or a setup failure "
        f"earlier in the run looks identical to a passing contract "
        f"here:\n{out[-700:]}"
    )


@pytest.mark.parametrize("spelling", ["let_bound", "wrap1"])
def test_1406_the_clean_twin_runs_clean(tmp_path: Path, spelling: str) -> None:
    """The other half of the differential.

    Without this, "the program refutes it" could be a property of the
    spelling rather than of the disclosure — the same route with an
    established fact returns its value and violates nothing.
    """
    out = _run(tmp_path, _source(spelling, disclosed=False))
    assert "violation" not in out, out[-700:]
    assert out.strip().endswith("7"), out[-300:]


# ---------------------------------------------------------------------------
# Shapes that do NOT move, pinned so a later change is visible against them
# ---------------------------------------------------------------------------

_CLOSURE = """
type IntThunk = fn(Int -> Int) effects(pure);
""" + _F + "{\n  let @Option<PosInt> = mk(@Float64.0);\n" \
           "  let @IntThunk = fn(@Int -> @Int) effects(pure) {\n" \
           "    match @Option<PosInt>.0 {\n" + _ARMS + "\n    }\n  };\n" \
           "  apply_fn(@IntThunk.0, 1)\n}\n"


@pytest.mark.parametrize("disclosed", [True, False])
def test_1406_a_closure_capture_cannot_produce_a_false_tier1(
    tmp_path: Path, disclosed: bool,
) -> None:
    """Captured in a lambda, the value reaches no Tier-1 proof either way.

    Recorded as a MEASURED non-result rather than left out.  A closure's
    result is opaque to the verifier, so the enclosing postcondition is
    already `tier3`/E522 — for both producers, which is what makes this a pin
    and not a mover.  If a later change makes a lambda's result transparent,
    the disclosed half of this cell must move with it or a new escape opens
    silently.
    """
    mk = _MK_DISCLOSED if disclosed else _MK_CLEAN
    result = _verify(tmp_path, _POSINT + mk + _CLOSURE)
    assert result["ok"] is True, result.get("diagnostics")
    unguarded = [o for o in result["obligations"]
                 if o["status"] == "tier3_unguarded"]
    assert bool(unguarded) is disclosed, (
        f"the producer's disclosure does not match the fixture's polarity: "
        f"{[(o['kind'], o['status']) for o in result['obligations']]}"
    )
    assert _f_ensures(result) == ("tier3", "E522"), _f_ensures(result)


_ARGUMENT = _POSINT + _MK_DISCLOSED + """
private fn consume(@Option<PosInt> -> @Int)
  requires(true)
  ensures(@Int.result > 0)
  effects(pure)
{
  match @Option<PosInt>.0 {
""" + _ARMS + """
  }
}
""" + _F + "{\n  consume(mk(@Float64.0))\n}\n"


def test_1410_the_argument_position_is_unchanged_by_this_fix(
    tmp_path: Path,
) -> None:
    """#1410's shape, pinned as measured — NOT fixed here.

    Passing a disclosed value as an ARGUMENT leaves `consume`'s postcondition
    `verified` while the program refutes it.  That is a different rule: the
    false proof lives in the callee, which modular verification makes once for
    every caller, so no amount of tainting in `f` reaches it.  It measures
    identically on `origin/release/v0.2.0` and here — for the direct, the
    `let`-bound and the wrapper spellings alike — which is the evidence that
    it is a separate root cause and not a gap in this one.

    Pinned so #1410's fix is visible against it: when the argument position
    gains the obligation the construction position already has, this cell
    changes and says so.
    """
    result = _verify(tmp_path, _ARGUMENT)
    assert result["ok"] is True, result.get("diagnostics")
    assert ("refine_bind", "tier3_unguarded", "E506") in [
        (o["kind"], o["status"], o.get("error_code"))
        for o in result["obligations"]
    ], "the producer did not disclose, so this pin measures nothing"
    consume_ens = [o for o in result["obligations"]
                   if o["kind"] == "ensures"
                   and o["description"] == "@Int.result > 0"]
    assert len(consume_ens) == 2, [
        (o["kind"], o["description"]) for o in result["obligations"]
    ]
    assert [o["status"] for o in consume_ens] == ["verified", "verified"], (
        f"#1410's shape moved — if that was intended, this cell records the "
        f"measurement it moved from: {[o['status'] for o in consume_ens]}"
    )
    out = _run(tmp_path, _ARGUMENT)
    assert "Postcondition violation in consume" in out, out[-700:]


# ---------------------------------------------------------------------------
# Warm == cold
# ---------------------------------------------------------------------------

@pytest.mark.parametrize(
    "spelling", ["let_bound", "wrap1", "where_helper"])
def test_1407_a_warm_session_agrees_with_the_cold_run(
    tmp_path: Path, spelling: str,
) -> None:
    """And keeps agreeing across a replay.

    `where_helper` is here because it is the one that broke (#1418 review
    F2).  The session's loop walks `program.declarations` and used to cache a
    bool about the top-level name, so a `where` helper that forwards a
    disclosed value — added to `_result_disclosed_fns` while its PARENT's
    slice was verified, never a `decl.name` itself — was dropped, the warm
    fixpoint settled one hop early, and warm proved at Tier 1 exactly what
    cold demoted.  Parametrising over only the two spellings that worked is
    what let it through, so the parametrisation is now the full set of
    forwarding shapes rather than a sample.

    The warm path assembles its stream from cached per-function slices, and a
    replayed slice re-runs no body — so the wrapper's "hands on a disclosed
    value" answer, which the cold path collects DURING translation, has to be
    cached with it.  Uncached, a replayed `wrap` drops out of the disclosed
    set and the warm session proves at Tier 1 exactly what the cold run
    demotes: the generous direction, and the one that matters.
    """
    from vera.obligations.session import VerificationSession

    source = _source(spelling, disclosed=True)
    cold = [(o["kind"], o["status"], o.get("error_code"))
            for o in _verify(tmp_path, source)["obligations"]]

    session = VerificationSession()
    first = session.verify_source(source, file=str(tmp_path / "s.vera"))
    warm = [(o.kind, o.status, o.error_code or None) for o in first.obligations]
    second = session.verify_source(source, file=str(tmp_path / "s.vera"))
    replay = [(o.kind, o.status, o.error_code or None) for o in second.obligations]

    assert warm == cold, f"warm/cold divergence:\n warm {warm}\n cold {cold}"
    assert replay == cold, f"replay divergence:\n replay {replay}\n cold {cold}"
    assert ("ensures", "tier3", "E534") in warm, warm


# ---------------------------------------------------------------------------
# The accounting identity, over the whole family
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("spelling", sorted(_SPELLINGS))
@pytest.mark.parametrize("disclosed", [True, False])
def test_1406_the_json_accounting_identity_holds(
    tmp_path: Path, spelling: str, disclosed: bool,
) -> None:
    """`len(obligations) == total + violated + tier3_unguarded`, everywhere.

    A demotion moves an obligation between buckets, and the summary is derived
    from the stream — so a fix that recorded a status the summary does not
    know how to count would break the partition `verify --json` documents
    rather than any single verdict.
    """
    result = _verify(tmp_path, _source(spelling, disclosed=disclosed))
    obs = result["obligations"]
    summary = result["verification"]
    violated = sum(1 for o in obs if o["status"] == "violated")
    unguarded = sum(1 for o in obs if o["status"] == "tier3_unguarded")
    assert len(obs) == summary["total"] + violated + unguarded, (
        f"{spelling}/{disclosed}: {len(obs)} obligations against total "
        f"{summary['total']} + violated {violated} + unguarded {unguarded}"
    )
    assert summary["total"] == (
        summary["tier1_verified"] + summary["tier3_runtime"]
    ), summary


# ---------------------------------------------------------------------------
# Selectivity — the control the corpus cannot supply
# ---------------------------------------------------------------------------

# NO corpus program discloses anything (measured: 0 of 472 carry a
# `tier3_unguarded` or E534 obligation), so a corpus differential over this
# change is silent by construction and can report no completeness regression
# because it exercises nothing.  This is the cell that does: ONE program in
# which a disclosed producer and a clean one both exist, so `_disclosed_fns`
# is non-empty and the taint machinery is live, and the caller that reads from
# the clean one must still prove at Tier 1.  A taint keyed on anything coarser
# than the value — the sort, the constructor, the presence of any disclosure
# in the run — passes every other cell in this file and fails here.
_SELECTIVE = _POSINT + _MK_DISCLOSED + """
private fn mk_ok(@Float64 -> @Option<PosInt>)
  requires(true)
  ensures(true)
  effects(pure)
{
  Some(7)
}

public fn f_dirty(@Float64 -> @Int)
  requires(true)
  ensures(@Int.result > 0)
  effects(pure)
{
  let @Option<PosInt> = mk(@Float64.0);
  match @Option<PosInt>.0 {
""" + _ARMS + """
  }
}

public fn f_clean(@Float64 -> @Int)
  requires(true)
  ensures(@Int.result > 0)
  effects(pure)
{
  let @Option<PosInt> = mk_ok(@Float64.0);
  match @Option<PosInt>.0 {
""" + _ARMS + """
  }
}
"""


def test_1406_disclosure_taints_the_value_not_the_run(tmp_path: Path) -> None:
    """Both callers in one program: only the one reading a disclosed value moves."""
    result = _verify(tmp_path, _SELECTIVE)
    assert result["ok"] is True, result.get("diagnostics")
    ensures = [(o["status"], o.get("error_code")) for o in result["obligations"]
               if o["kind"] == "ensures" and o["description"] == "@Int.result > 0"]
    assert ensures == [("tier3", "E534"), ("verified", None)], (
        f"f_dirty must demote and f_clean must not — got {ensures}"
    )


def test_1406_a_warm_session_does_not_carry_the_taint_between_functions(
    tmp_path: Path,
) -> None:
    """The same selectivity, on one shared solver.

    A warm session reuses one `SmtContext` across every function, and
    `reset()` restarts `_fresh_counter` — so the next function mints the same
    hash-consed `mk!0` constant the previous one's disclosed call produced.
    A recorded term left standing would match a CLEAN call's result by name
    collision alone, and `f_clean` would inherit a demotion from a function it
    has nothing to do with.
    """
    from vera.obligations.session import VerificationSession

    cold = [(o["kind"], o["status"], o.get("error_code"))
            for o in _verify(tmp_path, _SELECTIVE)["obligations"]]
    session = VerificationSession()
    res = session.verify_source(_SELECTIVE, file=str(tmp_path / "s.vera"))
    warm = [(o.kind, o.status, o.error_code or None) for o in res.obligations]
    assert warm == cold, f"warm/cold divergence:\n warm {warm}\n cold {cold}"
    assert warm.count(("ensures", "tier3", "E534")) == 1, warm


def test_1406_reset_forgets_the_previous_functions_disclosed_terms() -> None:
    """`SmtContext.reset()` drops the recorded terms — pinned directly.

    A warm session reuses one context across a whole program, so
    `_disclosed_terms` is per-function state that must not survive the
    boundary.  No whole program is known to distinguish keeping it —
    `_fresh_name` carries the callee's name, so a stale entry can only
    collide with a same-named callee's result, which has the same disclosure
    status — which is exactly why the invariant is pinned here rather than
    through a program that happens to exhibit it.  Left to a downstream
    symptom, this line would be unpinned and the next change to how a call's
    result is named would silently turn a defensive clear into a real leak.
    """
    import z3

    from vera.smt import SmtContext

    smt = SmtContext()
    term = z3.Int("_call_mk_1")
    smt._disclosed_terms.append(term)
    assert smt.term_is_disclosed(term) is True
    smt.reset()
    assert smt.term_is_disclosed(term) is False, (
        "a previous function's disclosed term is still recorded, so a later "
        "function's identically-named call result inherits its demotion"
    )


# ---------------------------------------------------------------------------
# #1413 — the other two readers of the same disclosed fact
# ---------------------------------------------------------------------------

# A disclosed value's declared-type facts are read at THREE places, and #1363
# gated one.  The cells above cover it.  These cover the other two, found by
# asking the question the matrix could not: not "which spelling reaches the
# gated reader" but "which readers are there".  Both are the same rule and the
# same mechanism — one fact, withheld rather than dropped — and both produce a
# `verified` obligation the program refutes with no trap.

_BIG = "type Big = { @Int | @Int.0 > -3 };\n"

# Reader 2: `_check_refined_binding_obligation_term`'s `src_fact`.  The arm
# binds the `PosInt` payload as a DIFFERENT refinement, and the narrowing is
# discharged from `PosInt`'s predicate — which the run disclosed.
_REBIND = _POSINT + _BIG + _MK_DISCLOSED + """
public fn f(@Float64 -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match mk(@Float64.0) {
    Some(@Big) -> @Big.0,
    None -> 41
  }
}
"""

# Reader 3: the let-destructure component seed.  The tuple is reached through
# an ADT payload on purpose — a refined tuple component IS guarded at the
# producer's return exit, so the bare `Tuple<PosInt, Int>` spelling is a false
# Tier-1 CLAIM whose value another guard happens to catch.  Through a payload
# there is no guard and the wrong value comes out, which is what makes this a
# soundness cell rather than a bookkeeping one.
_DESTRUCTURE = _POSINT + _BIG + """
private fn mk(@Float64 -> @Option<Tuple<PosInt, Int>>)
  requires(true)
  ensures(true)
  effects(pure)
{
  Some(Tuple(float_to_int(@Float64.0), 5))
}

public fn f(@Float64 -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match mk(@Float64.0) {
    Some(@Tuple<PosInt, Int>) -> {
      let Tuple<@PosInt, @Int> = @Tuple<PosInt, Int>.0;
      let @Big = @PosInt.0;
      @Big.0
    },
    None -> 41
  }
}
"""

# The clean twins: identical shape, a producer whose payload the solver
# settles.  `Some(7)` / `Some(Tuple(7, 5))` narrow into `Big` provably.
_REBIND_CLEAN = _REBIND.replace(
    "Some(float_to_int(@Float64.0))", "Some(7)")
_DESTRUCTURE_CLEAN = _DESTRUCTURE.replace(
    "Some(Tuple(float_to_int(@Float64.0), 5))", "Some(Tuple(7, 5))")


def _narrowing_binds(result: dict) -> list[tuple[str, str | None]]:
    """The `refine_bind` obligations that are NOT the producer's own.

    Keyed by excluding the producer's site (`float_to_int(...)`), so the cell
    reads the consumer's narrowing rather than the disclosure that feeds it —
    which are different obligations with different correct statuses.
    """
    return [(o["status"], o.get("error_code")) for o in result["obligations"]
            if o["kind"] == "refine_bind"
            and "float_to_int" not in (o.get("description") or "")]


@pytest.mark.parametrize(
    "label,source",
    [("rebind", _REBIND), ("destructure", _DESTRUCTURE)],
    ids=["rebind", "destructure"],
)
def test_1413_a_renarrowing_off_a_disclosed_value_is_not_tier_1(
    tmp_path: Path, label: str, source: str,
) -> None:
    """The second and third readers demote, and the run says why they must.

    Before this change both were `verified` — a Tier-1 claim — while the
    program returned `-7` for a value declared `Big` (`> -3`) and trapped
    nowhere: a refined ADT sub-pattern bind and a destructured component
    re-narrowing carry no codegen guard.
    """
    result = _verify(tmp_path, source)
    assert result["ok"] is True, result.get("diagnostics")
    assert _narrowing_binds(result) == [("tier3_unguarded", "E506")], (
        f"{label}: the narrowing holds only from a fact this run could "
        f"neither prove nor guard — got {_narrowing_binds(result)}"
    )
    out = _run(tmp_path, source)
    assert out.strip().endswith("-7"), (
        f"{label}: the fixture did not produce the offending value, so it "
        f"reports no verdict about soundness:\n{out[-700:]}"
    )


@pytest.mark.parametrize(
    "label,source",
    [("rebind", _REBIND_CLEAN), ("destructure", _DESTRUCTURE_CLEAN)],
    ids=["rebind", "destructure"],
)
def test_1413_a_renarrowing_off_a_clean_value_still_proves(
    tmp_path: Path, label: str, source: str,
) -> None:
    """The over-rejection control for both new readers.

    These premises exist to stop a false E505 — a projection out of a refined
    source must be able to use the invariant that source carries.  Withholding
    them unconditionally would restore exactly the bug `_term_source_fact` was
    written to fix, so each reader's gate is measured against a source whose
    fact the run DID establish.
    """
    result = _verify(tmp_path, source)
    assert result["ok"] is True, result.get("diagnostics")
    assert not [o for o in result["obligations"]
                if o["status"] == "tier3_unguarded"], (
        f"{label}: the control's producer disclosed something"
    )
    # TWO here, not one: the clean producer's own `Some(7)` narrowing into
    # `PosInt` is itself a `refine_bind`, and it has no `float_to_int` site for
    # `_narrowing_binds` to filter on — so the count is asserted rather than
    # the filter widened, which would let the consumer's bind go missing
    # unnoticed.
    binds = [(o["status"], o.get("error_code")) for o in result["obligations"]
             if o["kind"] == "refine_bind"]
    assert binds == [("verified", None), ("verified", None)], (
        f"{label}: a clean source's invariant must still discharge the "
        f"re-narrowing, and the producer's own narrowing must still prove — "
        f"got {binds}"
    )
    out = _run(tmp_path, source)
    assert "violation" not in out and out.strip().endswith("7"), out[-400:]


def test_1413_every_reader_of_a_source_fact_consults_the_one_gate() -> None:
    """No reader may decide for itself whether a fact was established.

    #1363's rule was correct and its single gate was correct; what let two
    false Tier-1s outlive it is that the rule lived at ONE of the three places
    a declared-type source fact is read, by convention rather than by
    construction.  Convention does not survive a fourth reader.

    The invariant, checked against the module's own AST: a function that calls
    a source-fact producer must also call `_established_facts` — unless it IS
    a producer, i.e. it hands the facts back to a caller instead of assuming
    them.  Adding a reader that assumes a fact without asking reddens this.

    The producer roster is asserted to still name real methods, so a rename
    cannot make the check vacuous by matching nothing, and the gate is
    asserted to have at least the three readers it has now, so deleting a
    call site is a failure rather than a silent narrowing.
    """
    import ast as pyast
    import inspect

    import vera.smt as smt_mod
    import vera.verifier as verifier_mod

    #: The functions that BUILD a declared-type fact about a value.  A reader
    #: is any function that calls one of these and then assumes the result.
    producers = {"_term_source_fact", "_subpattern_source_facts_term"}

    # Both modules (#1418 review F5).  Every producer lives in the verifier
    # today, so the SMT half of this walk currently finds none and is
    # VACUOUS there — it is included so that a premise seeded next to the
    # recording hook, which now lives in that layer, is inside the check by
    # existing code rather than by someone remembering to widen it.  The
    # roster assertion below is what stops the whole cell going vacuous.
    trees = []
    for mod in (verifier_mod, smt_mod):
        src_file = inspect.getsourcefile(mod)  # not cwd-dependent
        assert src_file is not None
        trees.append(pyast.parse(Path(src_file).read_text(encoding="utf-8")))

    defined: set[str] = set()
    calls: dict[str, set[str]] = {}
    for node in [n for tree in trees for n in pyast.walk(tree)]:
        if not isinstance(node, (pyast.FunctionDef, pyast.AsyncFunctionDef)):
            continue
        defined.add(node.name)
        named: set[str] = set()
        for inner in pyast.walk(node):
            if (isinstance(inner, pyast.Call)
                    and isinstance(inner.func, pyast.Attribute)
                    and isinstance(inner.func.value, pyast.Name)
                    and inner.func.value.id == "self"):
                named.add(inner.func.attr)
        calls[node.name] = named

    missing = sorted(producers - defined)
    assert not missing, (
        f"the producer roster names methods that no longer exist ({missing}), "
        f"so this check matches nothing and proves nothing — update it"
    )
    assert "_established_facts" in defined

    readers = sorted(
        name for name, named in calls.items()
        if named & producers and name not in producers
    )
    assert len(readers) >= 3, (
        f"expected at least the three known readers, found {readers} — a "
        f"call site was deleted or the walk stopped seeing them"
    )
    ungated = [r for r in readers if "_established_facts" not in calls[r]]
    assert not ungated, (
        f"{ungated} read a declared-type source fact and assume it without "
        f"asking `_established_facts` whether this run established it — that "
        f"is the shape of #1406 / #1407 / #1413, one reader further out"
    )


# ---------------------------------------------------------------------------
# Composition with #1399/#1402: the taint AND the citation cross the import
# ---------------------------------------------------------------------------

_IMP_LIB = _POSINT + """
public fn mk(@Float64 -> @Option<PosInt>)
  requires(true)
  ensures(true)
  effects(pure)
{
  Some(float_to_int(@Float64.0))
}
"""

_IMP_CALLERS = {
    # #1399/#1402's own shape — the control for this group.
    "direct": "import oplib;\n" + _POSINT + _F
              + "{\n  match oplib::mk(@Float64.0) {\n" + _ARMS + "\n  }\n}\n",
    # #1406 across the boundary: the scrutinee is a slot reference, so the
    # importer's manifest consult never fires on it.
    "let_bound": "import oplib;\n" + _POSINT + _F
                 + "{\n  let @Option<PosInt> = oplib::mk(@Float64.0);\n"
                   "  match @Option<PosInt>.0 {\n" + _ARMS + "\n  }\n}\n",
    # #1407 across the boundary: the wrapper is local and carries no
    # obligation, so neither this run's stream nor the manifest names it.
    "wrapper": "import oplib;\n" + _POSINT + """
private fn wrap(@Float64 -> @Option<PosInt>)
  requires(true)
  ensures(true)
  effects(pure)
{
  oplib::mk(@Float64.0)
}
""" + _F + "{\n  match wrap(@Float64.0) {\n" + _ARMS + "\n  }\n}\n",
}


def _verify_with_lib(tmp_path: Path, caller: str) -> dict:
    (tmp_path / "oplib.vera").write_text(_IMP_LIB, encoding="utf-8")
    return _verify(tmp_path, caller, name="main.vera")


@pytest.mark.parametrize("spelling", sorted(_IMP_CALLERS))
def test_1406_the_taint_crosses_an_import_in_every_spelling(
    tmp_path: Path, spelling: str,
) -> None:
    """#1402 gives the importer a disclosed set; this makes it survive.

    Measured through the rebase: on `release/v0.2.0` before #1402 all three
    escaped, with #1402 alone only `direct` demoted, and the two spellings
    this PR is about needed both changes. They compose rather than overlap
    because the hook the SMT layer records terms through IS
    `_scrutinee_is_disclosed_call` — whatever #1402 teaches that method about
    resolving an imported callee, the value taint inherits.
    """
    result = _verify_with_lib(tmp_path, _IMP_CALLERS[spelling])
    assert result["ok"] is True, result.get("diagnostics")
    assert _f_ensures(result) == ("tier3", "E534"), (
        f"{spelling}: an imported disclosure must demote its importer "
        f"whatever spelling reaches it — got {_f_ensures(result)}"
    )


@pytest.mark.parametrize("spelling", sorted(_IMP_CALLERS))
def test_1399_the_demotion_still_names_the_import_it_came_from(
    tmp_path: Path, spelling: str,
) -> None:
    """A demotion this PR newly causes must not be one nobody can act on.

    #1399's finding 4 was that an importer's E534 named nothing: the E504
    identifying the culprit belongs to the library's run, which this one
    discards. #1402 fixed that for the direct spelling by citing the site as
    it consults the manifest — at the place the fact is withheld. This PR
    withholds in two more places where that consult has long since happened
    (a `let`-bound value is a slot reference; a forwarder is a local call),
    so the citation is carried ON the value instead, and across the forwarder
    hop with it. Without that, the two spellings would demote with the
    generic text and re-open the finding.
    """
    result = _verify_with_lib(tmp_path, _IMP_CALLERS[spelling])
    e534 = [w for w in result["warnings"] if w.get("error_code") == "E534"]
    assert len(e534) == 1, [w.get("error_code") for w in result["warnings"]]
    text = e534[0]["description"]
    assert "oplib::mk" in text, (
        f"{spelling}: the demotion names no culprit, so the reader is told "
        f"only that something somewhere was not established — {text}"
    )
    assert "oplib.vera" in text and "E506" in text, text


# ---------------------------------------------------------------------------
# #1418 review F1 — the value the SMT layer LOST still carries its taint
# ---------------------------------------------------------------------------

# Where translation fails, a fresh stand-in constant replaces the value and
# the recorded provenance is severed — while every reader still takes the
# payload refinement off the binding's DECLARED type.  That is #1363's
# asymmetry one layer down, and it is carrier-dependent, which is what made
# it easy to miss: over an `Option<Nat>` payload the identical tuple spelling
# translates and demotes correctly, so only a carrier whose binding falls to
# `_fresh_opaque_slot` exhibits it.
_TUPLE_LAUNDER = """{
  let @Tuple<Option<PosInt>, Int> = Tuple(mk(@Float64.0), 1);
  let Tuple<@Option<PosInt>, @Int> = @Tuple<Option<PosInt>, Int>.0;
  match @Option<PosInt>.0 {
""" + _ARMS + """
  }
}
"""

_F1_BODIES = {
    # A `let` the SMT layer cannot translate: the stand-in is minted by
    # `_fresh_opaque_slot`, and the destructure projects out of it.
    "tuple_destructure": _F + _TUPLE_LAUNDER,
    # An array literal: its constant is related to its elements only by
    # axiom, so the occurrence walk cannot reach the element's term.
    "array_index": _F + "{\n  let @Array<Option<PosInt>> = [mk(@Float64.0)];\n"
                        "  match @Array<Option<PosInt>>.0[0] {\n"
                        + _ARMS + "\n  }\n}\n",
    # Both halves at once: the wrapper launders through the tuple, so the
    # INTER-function taint has to survive the lost value too.
    "wrapper_through_tuple": """
private fn wtup(@Float64 -> @Option<PosInt>)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Tuple<Option<PosInt>, Int> = Tuple(mk(@Float64.0), 1);
  let Tuple<@Option<PosInt>, @Int> = @Tuple<Option<PosInt>, Int>.0;
  @Option<PosInt>.0
}
""" + _F + "{\n  match wtup(@Float64.0) {\n" + _ARMS + "\n  }\n}\n",
}


@pytest.mark.parametrize("shape", sorted(_F1_BODIES))
def test_1418_f1_a_lost_value_still_carries_its_disclosure(
    tmp_path: Path, shape: str,
) -> None:
    """A stand-in inherits the disclosure of the expression it replaces.

    Each of these was `verified` at Tier 1 while `vera run --fn f -- -7.0`
    refuted the postcondition — on the pre-#1402 base, on this PR's first
    head, and on the rebase — because the gate compared a term the disclosed
    call never reached.  The repair is at the mint, not at the reader: the
    stand-in is recorded as a disclosed value, so every reader's gate answers
    True for it without any of them learning about opaque slots.
    """
    source = _POSINT + _MK_DISCLOSED + _F1_BODIES[shape]
    result = _verify(tmp_path, source)
    assert result["ok"] is True, result.get("diagnostics")
    assert ("refine_bind", "tier3_unguarded", "E506") in [
        (o["kind"], o["status"], o.get("error_code"))
        for o in result["obligations"]
    ], "the producer did not disclose, so this cell measures nothing"
    assert _f_ensures(result) == ("tier3", "E534"), _f_ensures(result)
    out = _run(tmp_path, source)
    assert "Postcondition violation in f" in out, (
        f"{shape}: the fixture did not reach the postcondition, so it reports "
        f"no verdict about soundness:\n{out[-700:]}"
    )


@pytest.mark.parametrize("shape", sorted(_F1_BODIES))
def test_1418_f1_a_lost_clean_value_still_proves(
    tmp_path: Path, shape: str,
) -> None:
    """The over-rejection control: losing the value is not itself a demotion.

    A stand-in is minted for the clean producer's binding too, so a fix that
    tainted every opaque slot would pass the cells above and destroy Tier-1
    verification for every untranslatable `let` in the language.
    """
    source = _POSINT + _MK_CLEAN + _F1_BODIES[shape]
    result = _verify(tmp_path, source)
    assert result["ok"] is True, result.get("diagnostics")
    assert _f_ensures(result) == ("verified", None), _f_ensures(result)
    out = _run(tmp_path, source)
    assert "violation" not in out and out.strip().endswith("7"), out[-400:]


# ---------------------------------------------------------------------------
# #1418 review F3 — a shared bare name must not demote a clean caller
# ---------------------------------------------------------------------------

def _collide_source(second_helper: str) -> str:
    """Two top-level functions, each with its own `where` helper: one
    forwarding the disclosed producer, one forwarding the clean one."""
    return _POSINT + _MK_DISCLOSED + """
private fn mk_ok(@Float64 -> @Option<PosInt>)
  requires(true)
  ensures(true)
  effects(pure)
{
  Some(7)
}

public fn tainted(@Float64 -> @Int)
  requires(true)
  ensures(@Int.result > 0)
  effects(pure)
{
  match h(@Float64.0) {
""" + _ARMS + """
  }
}
where {
  fn h(@Float64 -> @Option<PosInt>)
    requires(true)
    ensures(true)
    effects(pure)
  {
    mk(@Float64.0)
  }
}
""" + _F + "{\n  match " + second_helper + "(@Float64.0) {\n" + _ARMS + """
  }
}
where {
  fn """ + second_helper + """(@Float64 -> @Option<PosInt>)
    requires(true)
    ensures(true)
    effects(pure)
  {
    mk_ok(@Float64.0)
  }
}
"""


@pytest.mark.parametrize("second_helper", ["h", "h2"])
def test_1418_f3_a_shared_helper_name_does_not_demote_a_clean_caller(
    tmp_path: Path, second_helper: str,
) -> None:
    """Keyed by scope, so a bare name shared across owners is not shared.

    `_result_disclosed_fns` was keyed by `decl.name`, and a `where` helper's
    bare name means a different function in every top-level owner — so one
    owner's tainted helper took the other owner's clean caller down with it
    (#1418 review F3).  A completeness loss rather than a soundness one, but
    a loss, and one this PR introduced by extending the set to forwarders.

    Both parametrisations must give the same answer: the collision is now
    settled by scope, so renaming the helper changes nothing.
    """
    result = _verify(tmp_path, _collide_source(second_helper))
    assert result["ok"] is True, result.get("diagnostics")
    ensures = [(o["status"], o.get("error_code")) for o in result["obligations"]
               if o["kind"] == "ensures" and o["description"] == "@Int.result > 0"]
    assert ensures == [("tier3", "E534"), ("verified", None)], (
        f"helper named {second_helper!r}: the tainted caller must demote and "
        f"the clean one must not — got {ensures}"
    )
