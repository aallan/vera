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


def _run(tmp_path: Path, source: str, arg: str = "-7.0",
         name: str = "r.vera") -> str:
    """Compile and call `f` with *arg*; return stdout+stderr.

    The default `-7.0` is chosen so no fallback can coincide with it: it is
    neither `0` nor the `None` arm's `41`, so a wrong answer cannot be read as
    a right one (the payload the disclosed `mk` builds is `-7`).
    """
    p = tmp_path / name
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


def _rebuilder(name: str, inner: str) -> str:
    """A forwarder that takes the value APART and puts it back together.

    `Some(@PosInt.0)` in the arm is a CONSTRUCTION whose component is the
    disclosed payload — the projected-from case one step on, and the shape
    the [#1431](https://github.com/aallan/vera/pull/1431) reviewer raised
    against this branch.

    THE `None` ARM REBUILDS AS `Some(1)`, and that is not cosmetic.  Mixing a
    literal `None` arm with a `Some(<expr>)` arm hits the sort mismatch
    [#1421](https://github.com/aallan/vera/issues/1421) fixes: on this
    revision the program dies with an E699 before a single obligation is
    emitted, so the literal spelling would measure nothing here.  With both
    arms constructing, the same shape translates on both revisions and the
    differential is real.  The literal `None`-arm spelling is measured on the
    composed tree instead — see
    `test_1418_a_value_rebuilt_from_a_disclosed_component_is_disclosed`.
    """
    return f"""
private fn {name}(@Float64 -> @Option<PosInt>)
  requires(true)
  ensures(true)
  effects(pure)
{{
  match {inner}(@Float64.0) {{
    Some(@PosInt) -> Some(@PosInt.0),
    None -> Some(1)
  }}
}}
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
    # CONSTRUCTED-from, not merely projected-from: the value is taken apart
    # and put back together before the consumer ever sees it.  Nothing in the
    # rule names constructions — the walk asks by OCCURRENCE, so the disclosed
    # term inside the constructor's argument is still there to be found.
    "rebuild_ctor": _rebuilder("rebuild", "mk")
                    + _F + "{\n  match rebuild(@Float64.0) {\n"
                    + _ARMS + "\n  }\n}\n",
    # Rebuilt twice: taking a value apart and reassembling it must not launder
    # the disclosure at any depth.
    "rebuild_ctor2": _rebuilder("rebuild", "mk")
                     + _rebuilder("rebuild_outer", "rebuild")
                     + _F + "{\n  match rebuild_outer(@Float64.0) {\n"
                     + _ARMS + "\n  }\n}\n",
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

@pytest.mark.parametrize("spelling", ["let_bound", "wrap1", "rebuild_ctor"])
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


@pytest.mark.parametrize("spelling", ["let_bound", "wrap1", "rebuild_ctor"])
def test_1406_the_clean_twin_runs_clean(tmp_path: Path, spelling: str) -> None:
    """The other half of the differential.

    Without this, "the program refutes it" could be a property of the
    spelling rather than of the disclosure — the same route with an
    established fact returns its value and violates nothing.
    """
    out = _run(tmp_path, _source(spelling, disclosed=False))
    assert "violation" not in out, out[-700:]
    # The LAST TOKEN, exactly.  `endswith("7")` is satisfied by `-7`, which is
    # precisely the disclosed route's answer — so the control could not have
    # caught a clean route that returned the disclosed payload (CodeRabbit,
    # PR #1418).
    assert out.strip().split()[-1] == "7", out[-300:]


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

@pytest.mark.parametrize("spelling", sorted(_SPELLINGS))
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
    what let it through, so this runs over EVERY spelling rather than a
    sample — a sample is the defect, not the coverage (CodeRabbit, PR #1418:
    `wrap2` needs the warm fixpoint to carry the taint two hops, and
    `wrap_let`/`wrap_pipe` need it to survive a forwarder that reaches its
    result through a binding).

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
    assert "violation" not in out, out[-400:]
    assert out.strip().split()[-1] == "7", out[-400:]   # exact, not a suffix


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

    # Keyed by (module, name): merging the two namespaces would let a
    # same-named function in one module overwrite the other's entry, so a
    # reader could be judged by a namesake's call set (CodeRabbit, PR #1418).
    defined: set[str] = set()
    calls: dict[tuple[str, str], set[str]] = {}
    for mod_name, tree in zip(("verifier", "smt"), trees):
        for node in pyast.walk(tree):
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
            calls[(mod_name, node.name)] = named

    missing = sorted(producers - defined)
    assert not missing, (
        f"the producer roster names methods that no longer exist ({missing}), "
        f"so this check matches nothing and proves nothing — update it"
    )
    assert "_established_facts" in defined

    readers = sorted(
        f"{mod}:{name}" for (mod, name), named in calls.items()
        if named & producers and name not in producers
    )
    assert len(readers) >= 3, (
        f"expected at least the three known readers, found {readers} — a "
        f"call site was deleted or the walk stopped seeing them"
    )
    ungated = [
        r for r in readers
        if "_established_facts" not in calls[(r.split(":", 1)[0],
                                              r.split(":", 1)[1])]
    ]
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
    assert "violation" not in out, out[-400:]
    assert out.strip().split()[-1] == "7", out[-400:]   # exact, not a suffix


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


#: Two owners, two helpers of the SAME bare name, and NO forwarding: each
#: helper discloses (or does not) through an obligation of its OWN.  The
#: `_collide_source` family reaches the disclosed set through
#: `_result_disclosed_fns` — the result-derived half — so it cannot tell
#: whether the obligation-derived half is scoped too.  This one contains no
#: `mk` at all, so the ONLY route into the set is `disclosed_fn_names`.
_F3_OWN_OBLIGATION = """type PosInt = { @Int | @Int.0 > 0 };

public fn tainted(@Float64 -> @Int)
  requires(true)
  ensures(@Int.result > 0)
  effects(pure)
{
  match h(@Float64.0) {
    Some(@PosInt) -> @PosInt.0,
    None -> 41
  }
}
where {
  fn h(@Float64 -> @Option<PosInt>)
    requires(true)
    ensures(true)
    effects(pure)
  {
    Some(float_to_int(@Float64.0))
  }
}

public fn f(@Float64 -> @Int)
  requires(true)
  ensures(@Int.result > 0)
  effects(pure)
{
  match h(@Float64.0) {
    Some(@PosInt) -> @PosInt.0,
    None -> 41
  }
}
where {
  fn h(@Float64 -> @Option<PosInt>)
    requires(true)
    ensures(true)
    effects(pure)
  {
    Some(7)
  }
}
"""


def test_1418_f3_the_obligation_derived_half_is_scoped_too(
    tmp_path: Path,
) -> None:
    """The other half of the union, isolated — no forwarding anywhere.

    The disclosed set is the UNION of two derivations: the obligation-derived
    `disclosed_fn_names` and the result-derived `_result_disclosed_fns`.  F3
    scoped the second.  The first went on keying a ``where`` helper by its
    bare `fn_name`, which means a different function in every owner, so one
    owner's disclosing helper demoted another owner's clean caller.

    Measured, not inferred: this shape reports BOTH callers `tier3`/E534 on
    `release/v0.2.0` at `212f1a1d` AND at the tip `35ff4def`, with this branch
    absent.  So the defect is not #1420's — it was latent in that half from
    the start, reachable whenever a helper carried a disclosing obligation of
    its own.  What #1420 changed is the REACH: obligating a helper's return
    made a merely FORWARDING helper carry one too, which is what turned
    `test_1418_f3_a_shared_helper_name_does_not_demote_a_clean_caller[h]` red
    on the rebase and is why both cells are needed — that one goes green
    again if only the result-derived half is scoped, and this one does not.

    Both halves now spell a helper's key with one function, `disclosed_key`,
    since a set consulted as a union cannot have two spellings for a member.
    """
    result = _verify(tmp_path, _F3_OWN_OBLIGATION)
    assert result["ok"] is True, result.get("diagnostics")
    statuses = [(o["kind"], o["status"], o.get("error_code"))
                for o in result["obligations"]]
    assert ("refine_bind", "tier3_unguarded", "E506") in statuses, (
        f"the disclosing helper did not disclose, so this measures nothing "
        f"about the obligation-derived half — {statuses}"
    )
    ensures = [(o["status"], o.get("error_code")) for o in result["obligations"]
               if o["kind"] == "ensures" and o["description"] == "@Int.result > 0"]
    assert ensures == [("tier3", "E534"), ("verified", None)], (
        f"the owner whose helper discloses must demote and the other must "
        f"not — got {ensures}"
    )


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


_NESTED_HELPER = _POSINT + _MK_DISCLOSED + _F + """{
  match h1(@Float64.0) {
""" + _ARMS + """
  }
}
where {
  fn h1(@Float64 -> @Option<PosInt>)
    requires(true)
    ensures(true)
    effects(pure)
  {
    h2(@Float64.0)
  }
  where {
    fn h2(@Float64 -> @Option<PosInt>)
      requires(true)
      ensures(true)
      effects(pure)
    {
      mk(@Float64.0)
    }
  }
}
"""


def test_1418_a_nested_helper_is_keyed_under_the_top_level_owner(
    tmp_path: Path,
) -> None:
    """Two levels of `where`, and the scope key has to agree at both.

    `enclosing` is built by APPENDING each parent, so `f -> h1 -> h2` gives
    `h2` the chain `(f, h1)` — the OUTERMOST is index 0.  Keying on the last
    element recorded `h2` under `h1$where$h2` while `h1`, whose own chain is
    `(f,)`, looked it up as `f$where$h2`.  The miss was in the unsound
    direction: `h1` discharged from `h2`'s disclosed result, `f` from
    `h1`'s, and the whole chain kept Tier 1 (CodeRabbit, PR #1418).

    One owner per top-level function is the point of the key, so this fixture
    is the minimum that can tell the two readings apart — a single level of
    nesting cannot, because there `enclosing[0] is enclosing[-1]`.
    """
    result = _verify(tmp_path, _NESTED_HELPER)
    assert result["ok"] is True, result.get("diagnostics")
    assert ("refine_bind", "tier3_unguarded", "E506") in [
        (o["kind"], o["status"], o.get("error_code"))
        for o in result["obligations"]
    ], "the producer did not disclose, so this cell measures nothing"
    assert _f_ensures(result) == ("tier3", "E534"), (
        f"a disclosed value forwarded through two levels of `where` helper "
        f"must still demote its caller — got {_f_ensures(result)}"
    )


# ---------------------------------------------------------------------------
# #1418 review G1 — a forwarder INSIDE an imported module is disclosed too
# ---------------------------------------------------------------------------

# #1402's manifest is what an importer asks about a module it does not verify,
# and it was built from `disclosed_fn_names(obligations)` alone.  A forwarder
# makes no claim and so records no obligation, so a forwarder inside the
# LIBRARY was invisible while the same three declarations in one file demoted
# correctly — the rule cannot depend on which side of an import the forwarder
# sits.  The manifest now emits the union of the obligation-derived set and
# the result-derived one, which is the same union `_disclosed_fn_names` takes
# on this side.
_G1_LIB_ONE_HOP = _POSINT + """
public fn mk(@Float64 -> @Option<PosInt>)
  requires(true)
  ensures(true)
  effects(pure)
{
  Some(float_to_int(@Float64.0))
}

public fn wrap(@Float64 -> @Option<PosInt>)
  requires(true)
  ensures(true)
  effects(pure)
{
  mk(@Float64.0)
}
"""

# Two hops INSIDE the library: `outer` forwards `wrap` forwards `mk`.  The
# library's own fixpoint has to carry the taint across both before the
# manifest is read, so this fails differently from the one-hop shape if the
# manifest were computed from a single pass.
_G1_LIB_TWO_HOP = _G1_LIB_ONE_HOP + """
public fn outer(@Float64 -> @Option<PosInt>)
  requires(true)
  ensures(true)
  effects(pure)
{
  wrap(@Float64.0)
}
"""

_G1_LIB_CLEAN = _POSINT + """
public fn mk(@Float64 -> @Option<PosInt>)
  requires(true)
  ensures(true)
  effects(pure)
{
  Some(7)
}

public fn wrap(@Float64 -> @Option<PosInt>)
  requires(true)
  ensures(true)
  effects(pure)
{
  mk(@Float64.0)
}

public fn outer(@Float64 -> @Option<PosInt>)
  requires(true)
  ensures(true)
  effects(pure)
{
  wrap(@Float64.0)
}
"""


def _g1_caller(callee: str) -> str:
    return "import oplib;\n" + _POSINT + _F + (
        "{\n  match oplib::" + callee + "(@Float64.0) {\n" + _ARMS + "\n  }\n}\n")


@pytest.mark.parametrize(
    "callee,lib", [("wrap", _G1_LIB_ONE_HOP), ("outer", _G1_LIB_TWO_HOP)],
    ids=["one_hop", "two_hop"],
)
def test_1418_g1_an_imported_forwarder_is_disclosed(
    tmp_path: Path, callee: str, lib: str,
) -> None:
    """The library's forwarder demotes its importer, and the run says why.

    `verified` at Tier 1 on the pre-#1402 base, on #1402 alone, and on this
    branch before the manifest took the union — with `vera run --fn f -- -7.0`
    refuting the postcondition in every case.  The library alone reports
    `mk`'s `refine_bind` as `tier3_unguarded`/E506 throughout, so the fact was
    always disclosed; only the importer could not see who was handing it on.
    """
    (tmp_path / "oplib.vera").write_text(lib, encoding="utf-8")
    source = _g1_caller(callee)
    result = _verify(tmp_path, source, name="main.vera")
    assert result["ok"] is True, result.get("diagnostics")
    assert _f_ensures(result) == ("tier3", "E534"), _f_ensures(result)
    out = _run(tmp_path, source, name="main.vera")
    assert "Postcondition violation in f" in out, out[-700:]


@pytest.mark.parametrize("callee", ["wrap", "outer"])
def test_1418_g1_a_clean_imported_forwarder_still_proves(
    tmp_path: Path, callee: str,
) -> None:
    """The over-rejection control: forwarding is not itself a disclosure.

    A manifest that listed every forwarder — rather than every forwarder of a
    DISCLOSED value — would satisfy the cells above and take Tier 1 away from
    every library that wraps its own helpers.
    """
    (tmp_path / "oplib.vera").write_text(_G1_LIB_CLEAN, encoding="utf-8")
    source = _g1_caller(callee)
    result = _verify(tmp_path, source, name="main.vera")
    assert result["ok"] is True, result.get("diagnostics")
    assert _f_ensures(result) == ("verified", None), _f_ensures(result)
    out = _run(tmp_path, source, name="main.vera")
    assert "violation" not in out, out[-400:]
    assert out.strip().split()[-1] == "7", out[-400:]


# ---------------------------------------------------------------------------
# #1418 review G2 — the `_set_fn_scope` hoist, pinned
# ---------------------------------------------------------------------------

# `_verify_fn`'s generic branch returns BEFORE the old assignment site, and it
# translates a body on the way out (`_check_generic_refined_return`) with the
# disclosure hook installed.  So a generic read the PREVIOUS function's
# `where` helpers, and `_local_fn_names_in_scope()` is what decides whether a
# bare call reaches an IMPORT or a local name — which makes the stale read
# reachable only across an import, and unsound in one direction: a leftover
# helper name makes an imported disclosing callee look local, the manifest is
# never consulted, and the disclosure is suppressed.
#
# Ordering is the fixture.  `holder` is verified FIRST and declares a helper
# named `mk`, so `mk` is left in `_scope_fn_names`; the generic `g` that
# follows has no helper of its own and its bare `mk` is `oplib::mk`, the
# disclosing import.  With the binding hoisted to the entry of `_verify_fn`,
# `g` starts from its own (empty) scope and the manifest is consulted.
_G2_LIB = _POSINT + """
public fn mk(@Float64 -> @Option<PosInt>)
  requires(true)
  ensures(true)
  effects(pure)
{
  Some(float_to_int(@Float64.0))
}
"""

_G2_STALE_SCOPE = "import oplib;\n" + _POSINT + """
public fn holder(@Float64 -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match mk(@Float64.0) {
    Some(@PosInt) -> @PosInt.0,
    None -> 41
  }
}
where {
  fn mk(@Float64 -> @Option<PosInt>)
    requires(true)
    ensures(true)
    effects(pure)
  {
    Some(9)
  }
}

public forall<T> fn g(@T, @Float64 -> @PosInt)
  requires(true)
  ensures(true)
  effects(pure)
{
  match mk(@Float64.0) {
    Some(@PosInt) -> @PosInt.0,
    None -> 41
  }
}
"""


def test_1418_g2_a_generic_refined_return_reads_its_own_scope(
    tmp_path: Path,
) -> None:
    """The generic path sees ITS OWN helpers, not the previous function's.

    A generic's concrete refined return is checked on a path that returns
    before the rest of `_verify_fn` runs, so the per-function scope state has
    to be bound at the ENTRY or that path reads whatever the last function
    left behind.  Reverting the hoist leaves the whole suite green, which is
    why this cell exists; it reds on that revert.

    Asserted on the outcome, not the mechanism: `g`'s bare `mk` is the
    disclosing IMPORT, so its refined return must not come back `verified`.
    A stale scope carrying `holder`'s helper of the same name makes the call
    look local, skips the manifest, and suppresses the disclosure.
    """
    (tmp_path / "oplib.vera").write_text(_G2_LIB, encoding="utf-8")
    result = _verify(tmp_path, _G2_STALE_SCOPE, name="main.vera")
    assert result["ok"] is True, result.get("diagnostics")
    generic = [(o["status"], o.get("error_code")) for o in result["obligations"]
               if o["kind"] == "refine_bind"
               and o.get("description") == "<expr>"]
    assert generic == [("tier3", "E506")], (
        f"the generic's refined return proved from an imported disclosure "
        f"the previous function's scope hid — got {generic}"
    )


# ---------------------------------------------------------------------------
# #1418 review G3 — the F3 residual, pinned as measured
# ---------------------------------------------------------------------------

_G3_RESIDUAL = _POSINT + _MK_DISCLOSED + """
private fn mk_ok(@Float64 -> @Option<PosInt>)
  requires(true)
  ensures(true)
  effects(pure)
{
  Some(7)
}
""" + _F + "{\n  match h(@Float64.0) {\n" + _ARMS + "\n  }\n}\n" + (
    """where {
  fn h(@Float64 -> @Option<PosInt>)
    requires(true)
    ensures(true)
    effects(pure)
  {
    mk_ok(@Float64.0)
  }

  fn inner(@Float64 -> @Int)
    requires(true)
    ensures(true)
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
}
""")


def test_1418_g3_the_scope_key_residual_errs_toward_demotion(
    tmp_path: Path,
) -> None:
    """Two helpers under ONE owner still share a key — pinned, not claimed fixed.

    `_result_disclosed_key` qualifies a `where` helper by its top-level owner,
    which separates helpers in DIFFERENT owners.  Two helpers under the same
    owner — here `h` (clean) beside a nested `h2` (disclosed) — still share
    that owner, so the outer caller reading the CLEAN helper is demoted along
    with the tainted one.

    That is the safe direction: a Tier-3 report where a Tier-1 proof was
    available, never the reverse.  Narrowing it further means carrying the
    whole lexical chain as the key rather than its root, which is a bigger
    change than the soundness fix needed.  Pinned so the cost is a
    measurement rather than a claim, and so narrowing it later is visible.
    """
    result = _verify(tmp_path, _G3_RESIDUAL)
    assert result["ok"] is True, result.get("diagnostics")
    assert _f_ensures(result) == ("tier3", "E534"), (
        f"the residual moved — if that was intended, this cell records the "
        f"state it moved from: {_f_ensures(result)}"
    )
    # The safe direction, demonstrated: the value `f` actually returns is the
    # CLEAN helper's, so the demotion costs a proof and never soundness.
    out = _run(tmp_path, _G3_RESIDUAL)
    assert "violation" not in out, out[-400:]
    assert out.strip().split()[-1] == "7", out[-400:]


def test_1418_a_value_rebuilt_from_a_disclosed_component_is_disclosed() -> None:
    """CONSTRUCTED-from is covered by the same walk as PROJECTED-from.

    The rule says a value is disclosed when it is, or is projected from, a
    disclosed call's result.  Rebuilding — `Some(@PosInt.0)` in a match arm
    over a disclosed producer — is that situation one step on: the new
    payload's fact rests on the disclosed one.  It needs no separate rule
    because the walk asks by OCCURRENCE, so a constructor application
    containing the projection contains the disclosed term.

    A unit cell BESIDE the end-to-end ones, not instead of them: the
    `rebuild_ctor` / `rebuild_ctor2` spellings and
    `test_1418_a_single_arm_rebuild_is_disclosed` carry the whole-program
    shape.  What only a unit can pin is the walk's own answer, independent of
    which carrier the program happened to use.

    Only the LITERAL `None`-arm spelling the #1431 reviewer wrote —
    `match mk(x) { Some(@PosInt) -> Some(@PosInt.0), None -> None }` — cannot
    be an end-to-end cell here, because on this revision it dies with an E699
    sort mismatch before any obligation is emitted.  That is
    [#1421](https://github.com/aallan/vera/issues/1421)'s bug, not this one,
    and it was measured on four trees rather than argued:

    | tree                    | that spelling      |
    | ----------------------- | ------------------ |
    | `release/v0.2.0` base   | E699               |
    | #1421's sort fix only   | `verified`, run refutes |
    | this branch only        | E699               |
    | both                    | `tier3`/E534       |

    So the two fixes are orthogonal and compose: #1421 decides whether the
    term can be BUILT, this branch decides which facts may DISCHARGE a goal
    over it.  Note the second row — the sort fix alone makes a spelling that
    used to crash into one that falsely proves, so it wants this branch under
    it.
    """
    import z3

    from vera.smt import SmtContext

    smt = SmtContext()
    disclosed = z3.Int("_call_mk_1")
    smt._disclosed_terms.append(disclosed)

    project = z3.Function("Option_Some_0", z3.IntSort(), z3.IntSort())
    rebuild = z3.Function("Some", z3.IntSort(), z3.IntSort())

    payload = project(disclosed)          # @PosInt.0
    rebuilt = rebuild(payload)            # Some(@PosInt.0)
    reread = project(rebuilt)             # the consumer's own projection

    assert smt.term_is_disclosed(disclosed) is True
    assert smt.term_is_disclosed(payload) is True, "projected-from"
    assert smt.term_is_disclosed(rebuilt) is True, "constructed-from"
    assert smt.term_is_disclosed(reread) is True, "and back out again"
    # The control that keeps this from being vacuous: a term with no
    # disclosed component answers False however deeply it is nested.
    clean = rebuild(project(z3.Int("_call_mk_ok_1")))
    assert smt.term_is_disclosed(clean) is False


# A carrier with ONE constructor, so `rebuild`'s match has a single arm and
# there is no join of any kind.  The `rebuild_ctor` spellings above both join
# two arms, and a join is exactly the thing `ite_join` already exercises — if
# the demotion there came from the join rather than from the construction,
# these two cells are where that shows, because here there is no join to
# blame.  `mk` builds the payload with `float_to_int` as everywhere else, and
# an ADT payload is guarded by codegen nowhere, so the contract is genuinely
# refutable.
_BOX = """type PosInt = { @Int | @Int.0 > 0 };

private data Box {
  Wrap(PosInt)
}

private fn mk(@Float64 -> @Box)
  requires(true)
  ensures(true)
  effects(pure)
{
  Wrap(%s)
}

private fn rebuild(@Float64 -> @Box)
  requires(true)
  ensures(true)
  effects(pure)
{
  match mk(@Float64.0) {
    Wrap(@PosInt) -> Wrap(@PosInt.0)
  }
}

public fn f(@Float64 -> @Int)
  requires(true)
  ensures(@Int.result > 0)
  effects(pure)
{
  match rebuild(@Float64.0) {
    Wrap(@PosInt) -> @PosInt.0
  }
}
"""


def test_1418_a_single_arm_rebuild_is_disclosed(tmp_path: Path) -> None:
    """Construction alone demotes — with no arm join anywhere in the program.

    On `release/v0.2.0` this is `verified` at Tier 1 and the compiled program
    refutes it: the full soundness signature, on a shape with no `let`, no
    wrapper, and no join — only a value pulled apart and put back together.
    """
    src = _BOX % "float_to_int(@Float64.0)"
    result = _verify(tmp_path, src)
    assert result["ok"] is True, result.get("diagnostics")
    statuses = [(o["kind"], o["status"], o.get("error_code"))
                for o in result["obligations"]]
    assert ("refine_bind", "tier3_unguarded", "E506") in statuses, statuses
    assert _f_ensures(result) == ("tier3", "E534"), statuses
    # The claim the status is ABOUT: the program really does break it.
    out = _run(tmp_path, src)
    assert "Postcondition violation" in out, out[-400:]


def test_1418_a_single_arm_rebuild_of_a_clean_value_still_proves(
    tmp_path: Path,
) -> None:
    """The control: same construction, nothing disclosed, still Tier 1.

    Without this a fix that demoted every rebuild would pass the cell above.
    """
    src = _BOX % "7"
    result = _verify(tmp_path, src)
    assert result["ok"] is True, result.get("diagnostics")
    assert _f_ensures(result) == ("verified", None), [
        (o["kind"], o["status"], o.get("error_code"))
        for o in result["obligations"]
    ]
    out = _run(tmp_path, src)
    assert "violation" not in out, out[-400:]
    assert out.strip().split()[-1] == "7", out[-400:]
