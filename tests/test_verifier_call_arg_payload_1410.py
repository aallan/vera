"""Stream V3 — a call ARGUMENT establishes its parameter's nested refinements.

#1410.  A refinement written INSIDE a parameter's type — an ADT payload
(``Option<PosInt>``), a tuple component (``Tuple<PosInt, Int>``) — is *assumed*
by the callee: it is verified once, modularly, on the standing rule that some
producer discharged it (a construction site's ``refine_bind``, a refined
return's guard, R1's param-assume).  At an argument position nothing asked, so
a value no producer established satisfied the parameter silently and the
callee's postcondition proved at Tier 1 from a fact established nowhere.  Two
shapes reach it, and they are separate holes rather than one:

* a DISCLOSED producer — ``mk`` declares ``-> Option<PosInt>`` and its own
  construction obligation resolved ``tier3_unguarded``/E506, so the declared
  type is a claim this run admitted it could not establish (the parameter-side
  twin of #1363); and
* an UNREFINED producer — ``mkint`` declares ``-> Option<Int>``, which the
  checker accepts for an ``Option<PosInt>`` parameter (refinements are erased
  for compatibility), so the payload predicate is not even claimed.

The second needs no disclosure at all, which is the evidence that the repair
belongs in obligation EMISSION at the argument position rather than in the
disclosure taint: on ``origin/release/v0.2.0`` at ``aecc1a6a`` both verified
clean (exit 0) and both refuted at run time.

Every cell below pairs the obligation stream with what the compiled program
does — the ``ensures`` + ``vera run`` differential, never ``assert`` (an
``assert`` raises no Tier-1 obligation, so it cannot witness a false one).
"""

from __future__ import annotations

import json
import os
import subprocess
import sys
from pathlib import Path

import pytest

import vera
from tests.verifier_helpers import _verify as _verify_source

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


def _verify_json(tmp_path: Path, source: str, name: str = "p.vera") -> dict:
    """The `verify --json` envelope, for the accounting-identity cells."""
    p = tmp_path / name
    p.write_text(source, encoding="utf-8")
    proc = _cli("verify", "--json", str(p))
    try:
        return json.loads(proc.stdout)
    except json.JSONDecodeError:
        raise AssertionError(
            f"verify emitted no envelope (exit {proc.returncode})\n"
            f"{proc.stdout[:400]}\n{proc.stderr[-600:]}"
        ) from None


def _run(tmp_path: Path, source: str, arg: str,
         name: str = "p.vera") -> subprocess.CompletedProcess[str]:
    p = tmp_path / name
    p.write_text(source, encoding="utf-8")
    return _cli("run", str(p), "--fn", "f", "--", arg)


def _refine_binds(source: str, fn: str) -> list:
    """Every ``refine_bind`` obligation the stream attributes to *fn*."""
    result = _verify_source(source)
    return [
        o for o in result.obligations
        if o.kind == "refine_bind" and o.fn_name == fn
    ]


def _statuses(obs: list) -> list[tuple[str, str]]:
    return [(o.status, o.error_code) for o in obs]


def _assert_accounting(tmp_path: Path, source: str, name: str = "a.vera") -> dict:
    """``len(obligations) == total + violated + tier3_unguarded`` (CLAUDE.md)."""
    env = _verify_json(tmp_path, source, name)
    obs = env["obligations"]
    summary = env["verification"]
    violated = sum(1 for o in obs if o["status"] == "violated")
    unguarded = sum(1 for o in obs if o["status"] == "tier3_unguarded")
    assert len(obs) == summary["total"] + violated + unguarded, (
        f"accounting identity broken: {len(obs)} obligations vs "
        f"total={summary['total']} violated={violated} unguarded={unguarded}"
    )
    assert summary["total"] == (
        summary["tier1_verified"] + summary["tier3_runtime"]
    )
    return env


_PRELUDE = "type PosInt = { @Int | @Int.0 > 0 };\n"

# The issue's reproducer, verbatim.
_1410_REPRO = _PRELUDE + """
private fn mk(@Float64 -> @Option<PosInt>)
  requires(true)
  ensures(true)
  effects(pure)
{
  Some(float_to_int(@Float64.0))
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

public fn f(@Float64 -> @Int)
  requires(true)
  ensures(@Int.result > 0)
  effects(pure)
{
  consume(mk(@Float64.0))
}
"""

# The same program with the payload CONSTRUCTED at the call site.  Its
# obligation already exists (the constructor-field site) and must stay exactly
# one `violated`/E505 — the argument rule must not double-record it.
_CONSTRUCTED = _PRELUDE + """
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

public fn f(@Float64 -> @Int)
  requires(true)
  ensures(@Int.result > 0)
  effects(pure)
{
  consume(Some(0 - 7))
}
"""

# A CLEAN producer: its construction obligation discharges at Tier 1, so its
# declared return type is a fact and the argument proves.
_CLEAN_PRODUCER = _PRELUDE + """
private fn mk(@Float64 -> @Option<PosInt>)
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

public fn f(@Float64 -> @Int)
  requires(true)
  ensures(@Int.result > 0)
  effects(pure)
{
  consume(mk(@Float64.0))
}
"""

# The caller FORWARDS its own parameter: R1 param-assume establishes the
# payload refinement, so the argument proves at Tier 1.
_FORWARDED = _PRELUDE + """
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

private fn g(@Option<PosInt> -> @Int)
  requires(true)
  ensures(@Int.result > 0)
  effects(pure)
{
  consume(@Option<PosInt>.0)
}

public fn f(@Float64 -> @Int)
  requires(true)
  ensures(@Int.result > 0)
  effects(pure)
{
  g(Some(7))
}
"""

# A disclosed producer reached through a WRAPPER — the spelling #1406/#1407
# are about.  The obligation must be EMITTED here whatever the taint knows;
# whether it is `verified` or disclosed is the taint's answer, not this rule's.
_WRAPPER = _PRELUDE + """
private fn mk(@Float64 -> @Option<PosInt>)
  requires(true)
  ensures(true)
  effects(pure)
{
  Some(float_to_int(@Float64.0))
}

private fn wrap(@Float64 -> @Option<PosInt>)
  requires(true)
  ensures(true)
  effects(pure)
{
  mk(@Float64.0)
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

public fn f(@Float64 -> @Int)
  requires(true)
  ensures(@Int.result > 0)
  effects(pure)
{
  consume(wrap(@Float64.0))
}
"""

# The producer's payload is not even CLAIMED to be refined: `Option<Int>` is
# accepted for an `Option<PosInt>` parameter.  Nothing is disclosed anywhere,
# so no taint rule can reach this — only an argument-position obligation can.
_UNREFINED_PAYLOAD = _PRELUDE + """
private fn mkint(@Float64 -> @Option<Int>)
  requires(true)
  ensures(true)
  effects(pure)
{
  Some(float_to_int(@Float64.0))
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

public fn f(@Float64 -> @Int)
  requires(true)
  ensures(@Int.result > 0)
  effects(pure)
{
  consume(mkint(@Float64.0))
}
"""

# The TUPLE-component twin of the unrefined-payload cell.  Codegen DOES guard
# a tuple parameter's components at the callee's entry
# (`_emit_component_refinement_guards`), so the status has to say `tier3`
# (guarded) and the run has to trap on that guard — status and guard agreeing
# is the #1362 rule.
_TUPLE_UNREFINED = _PRELUDE + """
private fn mkint(@Float64 -> @Tuple<Int, Int>)
  requires(true)
  ensures(true)
  effects(pure)
{
  Tuple(float_to_int(@Float64.0), 5)
}

private fn consume(@Tuple<PosInt, Int> -> @Int)
  requires(true)
  ensures(@Int.result > 0)
  effects(pure)
{
  match @Tuple<PosInt, Int>.0 {
    Tuple(@PosInt, @Int) -> @PosInt.0
  }
}

public fn f(@Float64 -> @Int)
  requires(true)
  ensures(@Int.result > 0)
  effects(pure)
{
  consume(mkint(@Float64.0))
}
"""

# The pipe spelling of the reproducer: `mk(x) |> consume()` desugars to
# `consume(mk(x))`, so it must carry the identical obligation.
_PIPED = _PRELUDE + """
private fn mk(@Float64 -> @Option<PosInt>)
  requires(true)
  ensures(true)
  effects(pure)
{
  Some(float_to_int(@Float64.0))
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

public fn f(@Float64 -> @Int)
  requires(true)
  ensures(@Int.result > 0)
  effects(pure)
{
  mk(@Float64.0) |> consume()
}
"""


# =====================================================================
# The issue's reproducer
# =====================================================================

def test_1410_disclosed_producer_argument_is_not_verified(tmp_path: Path) -> None:
    """The argument carries an obligation, and it is NOT `verified`.

    Pre-fix `f` held no `refine_bind` at all and `consume`'s `ensures` proved
    at Tier 1 from the payload fact — while `vera run --fn f -- -7.0` refuted
    that very postcondition.
    """
    binds = _refine_binds(_1410_REPRO, "f")
    assert binds, "the call argument raised no refinement obligation at all"
    assert all(o.status != "verified" for o in binds), (
        "the argument's payload refinement was proved from a fact this run "
        f"disclosed it could not establish: {_statuses(binds)}"
    )
    # A disclosed producer feeding an ADT payload is neither proved nor
    # runtime-guarded — codegen component-guards tuples only — so the honest
    # bucket is the unguarded one, surfaced as E506.
    assert ("tier3_unguarded", "E506") in _statuses(binds), _statuses(binds)
    _assert_accounting(tmp_path, _1410_REPRO)


def test_1410_run_still_refutes_the_contract(tmp_path: Path) -> None:
    """The differential half: the compiled program disagrees with a Tier-1
    claim, which is what makes the obligation's absence a soundness bug."""
    proc = _run(tmp_path, _1410_REPRO, "-7.0")
    assert proc.returncode != 0, proc.stdout
    assert "Postcondition violation in consume" in (proc.stdout + proc.stderr)


def test_1410_verify_still_exits_zero_with_a_warning(tmp_path: Path) -> None:
    """A disclosure is a warning, not a refutation: `verify` stays exit 0 and
    the program is disclosed rather than rejected."""
    p = tmp_path / "e.vera"
    p.write_text(_1410_REPRO, encoding="utf-8")
    proc = _cli("verify", str(p))
    assert proc.returncode == 0, proc.stdout + proc.stderr


# =====================================================================
# Controls — the shapes the rule must NOT disturb
# =====================================================================

def test_constructed_argument_keeps_exactly_one_violation(tmp_path: Path) -> None:
    """`consume(Some(0 - 7))` is obligated at its CONSTRUCTION site already.
    The argument rule must not add a second record for the same fact."""
    binds = _refine_binds(_CONSTRUCTED, "f")
    assert _statuses(binds) == [("violated", "E505")], _statuses(binds)
    _assert_accounting(tmp_path, _CONSTRUCTED)


def test_clean_producer_argument_verifies(tmp_path: Path) -> None:
    """A producer whose own construction discharged at Tier 1 makes its
    declared return type a fact — the argument proves, and `verify` is clean."""
    binds = _refine_binds(_CLEAN_PRODUCER, "f")
    assert binds, "the argument obligation must be emitted here too"
    assert all(o.status == "verified" for o in binds), _statuses(binds)
    env = _assert_accounting(tmp_path, _CLEAN_PRODUCER)
    assert env["ok"] is True, env["diagnostics"]


def test_forwarded_parameter_argument_verifies(tmp_path: Path) -> None:
    """R1 param-assume establishes the caller's own parameter's payload
    refinement, so forwarding it discharges at Tier 1."""
    binds = _refine_binds(_FORWARDED, "g")
    assert binds, "the forwarded argument must still raise the obligation"
    assert all(o.status == "verified" for o in binds), _statuses(binds)
    env = _assert_accounting(tmp_path, _FORWARDED)
    assert env["ok"] is True, env["diagnostics"]


def test_wrapper_argument_raises_the_obligation(tmp_path: Path) -> None:
    """Through a wrapper the obligation is EMITTED regardless of what the
    disclosure taint currently reaches — the emission rule is
    spelling-independent, and the taint (#1406/#1407) decides the status."""
    assert _refine_binds(_WRAPPER, "f"), (
        "the wrapped argument raised no obligation; the emission rule must "
        "not depend on how the producer was spelled"
    )
    _assert_accounting(tmp_path, _WRAPPER)


# =====================================================================
# The unrefined-payload hole — no disclosure involved
# =====================================================================

def test_unrefined_payload_argument_is_refuted(tmp_path: Path) -> None:
    """`Option<Int>` into `Option<PosInt>`: the payload predicate is not even
    claimed by the producer, so the argument is a genuine refutation."""
    binds = _refine_binds(_UNREFINED_PAYLOAD, "f")
    assert binds, "the unrefined-payload argument raised no obligation"
    assert ("violated", "E505") in _statuses(binds), _statuses(binds)
    env = _assert_accounting(tmp_path, _UNREFINED_PAYLOAD)
    assert env["ok"] is False


def test_unrefined_payload_run_refutes(tmp_path: Path) -> None:
    proc = _run(tmp_path, _UNREFINED_PAYLOAD, "-7.0")
    assert proc.returncode != 0, proc.stdout
    assert "Postcondition violation in consume" in (proc.stdout + proc.stderr)


def test_tuple_component_argument_status_matches_its_guard(
    tmp_path: Path,
) -> None:
    """A tuple parameter's components ARE guarded at the callee's entry, so a
    tuple-component argument obligation must record a status consistent with
    that guard, and the run must trap on it."""
    binds = _refine_binds(_TUPLE_UNREFINED, "f")
    assert binds, "the tuple-component argument raised no obligation"
    assert all(o.status != "verified" for o in binds), _statuses(binds)
    assert all(o.status != "tier3_unguarded" for o in binds), (
        "codegen guards a tuple parameter's components at entry, so claiming "
        f"the site is unguarded contradicts the emitted guard: {_statuses(binds)}"
    )
    _assert_accounting(tmp_path, _TUPLE_UNREFINED)

    proc = _run(tmp_path, _TUPLE_UNREFINED, "-7.0", name="t.vera")
    assert proc.returncode != 0, proc.stdout
    out = proc.stdout + proc.stderr
    assert "Refinement violation in consume" in out and "parameter" in out, out


def test_piped_argument_matches_the_direct_spelling() -> None:
    """The pipe desugars to the same call, so it carries the same obligation
    with the same status — a spelling must not change the answer."""
    direct = _refine_binds(_1410_REPRO, "f")
    piped = _refine_binds(_PIPED, "f")
    assert piped, "the piped argument raised no obligation"
    assert sorted(_statuses(piped)) == sorted(_statuses(direct)), (
        _statuses(direct), _statuses(piped))


# =====================================================================
# The warm session must count what cold counts
# =====================================================================

@pytest.mark.parametrize("source", [
    _1410_REPRO, _CONSTRUCTED, _CLEAN_PRODUCER, _FORWARDED,
    _WRAPPER, _UNREFINED_PAYLOAD, _TUPLE_UNREFINED,
])
def test_warm_session_agrees_with_cold(source: str) -> None:
    """`VerificationSession` assembles its stream from per-function slices; a
    new obligation kind that cold emits and warm does not is a divergence in
    the one direction that matters (warm the more generous)."""
    from vera.obligations import VerificationSession

    cold = _verify_source(source).obligations
    warm = VerificationSession().verify_source(source).obligations
    cold_binds = sorted(
        (o.fn_name, o.status) for o in cold if o.kind == "refine_bind")
    warm_binds = sorted(
        (o.fn_name, o.status) for o in warm if o.kind == "refine_bind")
    assert warm_binds == cold_binds, (cold_binds, warm_binds)


# =====================================================================
# Positions the rule must state honestly rather than guess at
# =====================================================================

_ARRAY_ESTABLISHED = _PRELUDE + """
private fn mk(@Int -> @Array<PosInt>)
  requires(true)
  ensures(true)
  effects(pure)
{
  [1, 2, 3]
}

private fn consume(@Array<PosInt> -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  array_length(@Array<PosInt>.0) |> nat_to_int()
}

public fn f(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  consume(mk(@Int.0))
}
"""

_ARRAY_UNESTABLISHED = _ARRAY_ESTABLISHED.replace(
    "fn mk(@Int -> @Array<PosInt>)", "fn mk(@Int -> @Array<Int>)")


def test_array_element_refinement_from_its_own_type_verifies() -> None:
    """An ``Array<PosInt>`` argument whose SOURCE is an ``Array<PosInt>`` was
    established by its producer, so the rule proves it without having to state
    "every element satisfies P" — which would need a quantifier over indices.

    Losing this leg does not lose a bug, it invents a warning: every array of
    a refined element type would disclose E506 at every call.
    """
    binds = _refine_binds(_ARRAY_ESTABLISHED, "f")
    assert _statuses(binds) == [("verified", "")], _statuses(binds)


def test_array_element_refinement_otherwise_discloses_unguarded() -> None:
    """``Array<Int>`` into ``Array<PosInt>`` is NOT established, and the
    element predicate cannot be stated — so the honest answer is an UNGUARDED
    disclosure.  Codegen decomposes tuples at a boundary and nothing else, so
    claiming `tier3` here would promise a runtime check that does not exist."""
    binds = _refine_binds(_ARRAY_UNESTABLISHED, "f")
    assert _statuses(binds) == [("tier3_unguarded", "E506")], _statuses(binds)


def test_unguarded_disclosure_names_the_right_boundary(tmp_path: Path) -> None:
    """The E506 rationale must say what codegen actually does HERE.

    The #746 sentence — "not at this internal narrowing site" — is false of a
    call argument, whose site IS a function boundary; what the boundary lacks
    is that its decomposition stops at tuple components.  A rationale that
    names the wrong reason sends the reader to change the wrong thing.
    """
    env = _verify_json(tmp_path, _1410_REPRO, "r.vera")
    at_call = [
        w for w in env["warnings"]
        if w.get("error_code") == "E506" and "call argument" in w["description"]
    ]
    assert at_call, env["warnings"]
    rationale = at_call[0]["rationale"]
    assert "TUPLE components" in rationale, rationale
    assert "internal narrowing site" not in rationale, rationale


_GENERIC_FORMAL = _PRELUDE + """
private fn mk(@Float64 -> @Option<PosInt>)
  requires(true)
  ensures(true)
  effects(pure)
{
  Some(float_to_int(@Float64.0))
}

private forall<T> fn ident(@T -> @T)
  requires(true)
  ensures(true)
  effects(pure)
{
  @T.0
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

public fn f(@Float64 -> @Int)
  requires(true)
  ensures(@Int.result > 0)
  effects(pure)
{
  consume(ident(mk(@Float64.0)))
}
"""


def test_generic_formal_reads_its_instantiated_target() -> None:
    """A ``TypeVar`` formal fixed to ``Option<PosInt>`` at this call site is
    recovered from the checker's instantiated-target side-table, exactly as
    every other binding-obligation target is — so the generic spelling raises
    the obligation the concrete one does.

    Both calls raise one.  ``ident``'s argument is the disclosed ``mk`` and
    discloses; ``consume``'s argument is ``ident(...)``, whose declared result
    type carries the payload refinement and whose own function is not in the
    disclosed set, so it proves — the wrapper-laundering shape #1406/#1407 own.
    The emission is what this rule owns and it happens at BOTH; which of them
    the taint reaches is the other rule's answer.
    """
    binds = _refine_binds(_GENERIC_FORMAL, "f")
    assert len(binds) == 2, _statuses(binds)
    assert ("tier3_unguarded", "E506") in _statuses(binds), _statuses(binds)


_NONE_ONLY_PRODUCER = _PRELUDE + """
private fn mk(@Float64 -> @Option<Int>)
  requires(true)
  ensures(@Option<Int>.result == None)
  effects(pure)
{
  None
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

public fn f(@Float64 -> @Int)
  requires(true)
  ensures(@Int.result > 0)
  effects(pure)
{
  consume(mk(@Float64.0))
}
"""


def test_payload_obligation_is_per_constructor() -> None:
    """The goal is ``is_Some(t) => P(payload)``, not ``P(payload)``.

    ``mk`` declares an UNREFINED payload, so nothing is established — but its
    contract pins the result to ``None``, under which the payload obligation is
    vacuous.  Stated without the recognizer the goal would talk about the
    payload of a value that has none, and Z3 would refute a program that cannot
    violate anything: a false E505 on the empty case of every optional.
    """
    binds = _refine_binds(_NONE_ONLY_PRODUCER, "f")
    assert _statuses(binds) == [("verified", "")], _statuses(binds)


_TUPLE_DISCLOSED = _PRELUDE + """
private fn mk(@Float64 -> @Tuple<PosInt, Int>)
  requires(true)
  ensures(true)
  effects(pure)
{
  Tuple(float_to_int(@Float64.0), 5)
}

private fn consume(@Tuple<PosInt, Int> -> @Int)
  requires(true)
  ensures(@Int.result > 0)
  effects(pure)
{
  match @Tuple<PosInt, Int>.0 {
    Tuple(@PosInt, @Int) -> @PosInt.0
  }
}

public fn f(@Float64 -> @Int)
  requires(true)
  ensures(@Int.result > 0)
  effects(pure)
{
  consume(mk(@Float64.0))
}
"""


def test_disclosed_tuple_component_records_the_guarded_tier3() -> None:
    """The same disclosure as #1410's repro, one shape over: a TUPLE component
    IS guarded at the callee's entry, so it records `tier3` — counted in the
    totals, an informational E506 — rather than the unguarded bucket.  Status
    and guard must agree (#1362), and here the guard exists."""
    binds = _refine_binds(_TUPLE_DISCLOSED, "f")
    assert ("tier3", "E506") in _statuses(binds), _statuses(binds)
    assert ("tier3_unguarded", "E506") not in _statuses(binds), _statuses(binds)


_PARTIALLY_STATABLE = _PRELUDE + """
private data Chain<T> {
  Link(T, Chain<T>),
  End
}

private fn mk(@Int -> @Chain<Int>)
  requires(true)
  ensures(@Chain<Int>.result == End)
  effects(pure)
{
  End
}

private fn consume(@Chain<PosInt> -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match @Chain<PosInt>.0 {
    Link(@PosInt, @Chain<PosInt>) -> @PosInt.0,
    End -> 1
  }
}

public fn f(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  consume(mk(@Int.0))
}
"""


def test_partially_statable_goal_never_reports_tier_one() -> None:
    """A goal missing one of its positions is not a discharge of the whole.

    ``Chain<PosInt>`` refines the head of every ``Link`` — including the links
    inside links, which the walk has to stop at (a recursive type cannot be
    unrolled into a finite conjunction).  The part it CAN state proves here,
    from ``mk``'s contract pinning the result to ``End``.  Recording
    ``verified`` on the strength of that half would claim the tail's links were
    established too: the exact overstatement this issue is about.
    """
    binds = _refine_binds(_PARTIALLY_STATABLE, "f")
    assert _statuses(binds) == [("tier3_unguarded", "E506")], _statuses(binds)


_LET_BOUND_CONSTRUCTION = _PRELUDE + """
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

public fn f(@Float64 -> @Int)
  requires(true)
  ensures(@Int.result > 0)
  effects(pure)
{
  let @Option<PosInt> = Some(0 - 7);
  consume(@Option<PosInt>.0)
}
"""


def test_let_bound_construction_is_excluded_on_the_value() -> None:
    """A construction reaches the argument as a SLOT REFERENCE here, and it is
    still excluded — the exclusion is decided on the Z3 term, which is still
    ``Some(...)``, not on the spelling.

    Deciding it syntactically would record a second obligation for a fact the
    `let`'s own construction site already refutes, and record it ``verified``:
    the argument's declared type carries the refinement, so the modular rule
    would prove exactly what the construction disproves — two contradictory
    claims about one value in one stream.
    """
    binds = _refine_binds(_LET_BOUND_CONSTRUCTION, "f")
    assert _statuses(binds) == [("violated", "E505")], _statuses(binds)


# =====================================================================
# The rule crosses a module boundary
# =====================================================================

_XMOD_LIB = """\
module lib.box;

type PosInt = { @Int | @Int.0 > 0 };

public fn consume(@Option<PosInt> -> @Int)
  requires(true)
  ensures(@Int.result > 0)
  effects(pure)
{
  match @Option<PosInt>.0 {
    Some(@PosInt) -> @PosInt.0,
    None -> 41
  }
}
"""

_XMOD_MAIN = """\
import lib.box(consume);

type PosInt = { @Int | @Int.0 > 0 };

private fn mk(@Float64 -> @Option<PosInt>)
  requires(true)
  ensures(true)
  effects(pure)
{
  Some(float_to_int(@Float64.0))
}

public fn f(@Float64 -> @Int)
  requires(true)
  ensures(@Int.result > 0)
  effects(pure)
{
  consume(mk(@Float64.0))
}
"""


def test_imported_callee_argument_carries_the_obligation(
    tmp_path: Path,
) -> None:
    """The callee whose single proof assumes the payload may live in another
    module, and the caller is no better placed to establish it there.

    Run through the CLI so the import is resolved exactly as `vera verify`
    resolves it — the constructor and alias registries the walk reads are
    per-module, and a lookup that missed the imported side would silently
    raise no obligation rather than fail.
    """
    (tmp_path / "lib").mkdir()
    (tmp_path / "lib" / "box.vera").write_text(_XMOD_LIB, encoding="utf-8")
    main = tmp_path / "main.vera"
    main.write_text(_XMOD_MAIN, encoding="utf-8")

    proc = _cli("verify", "--json", str(main))
    env = json.loads(proc.stdout)
    at_call = [
        o for o in env["obligations"]
        if o["kind"] == "refine_bind" and o["location"]["line"] == 18
    ]
    assert at_call, [
        (o["kind"], o["status"], o["location"]["line"])
        for o in env["obligations"]
    ]
    assert all(o["status"] != "verified" for o in at_call), at_call

    run = _cli("run", str(main), "--fn", "f", "--", "-7.0")
    assert run.returncode != 0
    assert "Postcondition violation in consume" in (run.stdout + run.stderr)


_XMOD_DISCLOSED_LIB = """\
module lib.mk;

type PosInt = { @Int | @Int.0 > 0 };

public fn mk(@Float64 -> @Option<PosInt>)
  requires(true)
  ensures(true)
  effects(pure)
{
  Some(float_to_int(@Float64.0))
}
"""

_XMOD_DISCLOSED_MAIN = """\
import lib.mk(mk);

type PosInt = { @Int | @Int.0 > 0 };

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

public fn f(@Float64 -> @Int)
  requires(true)
  ensures(@Int.result > 0)
  effects(pure)
{
  consume(mk(@Float64.0))
}
"""


def test_imported_disclosed_producer_demotes_through_the_manifest(
    tmp_path: Path,
) -> None:
    """The PRODUCER is the imported half, and its disclosure travels.

    #1399/#1402 carry a module's disclosed set across the import it is read
    through, so `_scrutinee_is_disclosed_call` answers for an imported callee
    off the defining module's manifest.  That machinery alone did not close
    this shape — measured on `release/v0.2.0` at `f23db8f7`, the program still
    reported `ok: true` with `consume`'s `ensures` verified and no obligation
    anywhere on the argument, while `vera run --fn f -- -7.0` refuted it: the
    disclosure had arrived and nothing was asking.  The obligation is what
    consults it, and the two compose exactly here.
    """
    (tmp_path / "lib").mkdir()
    (tmp_path / "lib" / "mk.vera").write_text(
        _XMOD_DISCLOSED_LIB, encoding="utf-8")
    main = tmp_path / "main.vera"
    main.write_text(_XMOD_DISCLOSED_MAIN, encoding="utf-8")

    env = json.loads(_cli("verify", "--json", str(main)).stdout)
    binds = [o for o in env["obligations"] if o["kind"] == "refine_bind"]
    assert [(o["status"], o["error_code"]) for o in binds] == [
        ("tier3_unguarded", "E506")
    ], binds

    run = _cli("run", str(main), "--fn", "f", "--", "-7.0")
    assert run.returncode != 0
    assert "Postcondition violation in consume" in (run.stdout + run.stderr)
