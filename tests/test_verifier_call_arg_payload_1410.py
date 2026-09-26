"""Stream V3 — a call ARGUMENT establishes its parameter's nested refinements.

#1410.  A refinement written INSIDE a parameter's type — an ADT payload
(``Option<PosInt>``), a tuple component (``Tuple<PosInt, Int>``) — is *assumed*
by the callee: it is verified once, modularly, on the standing rule that some
producer discharged it (a construction site's ``refine_bind``, a refined
return's guard, R1's param-assume).  At an argument position nothing asked, so
a value no producer established satisfied the parameter silently and the
callee's postcondition proved at Tier 1 from a fact established nowhere.  Two
shapes reach it, and they are separate holes rather than one:

* a DISCLOSED producer — ``mk`` declares ``-> Option<PosInt>`` and one of its
  own obligations resolved ``tier3_unguarded``/E506, so the declared type is a
  claim this run admitted it could not establish (the parameter-side twin of
  #1363); and
* an UNREFINED producer — ``mkint`` declares ``-> Option<Int>``, which the
  checker accepts for an ``Option<PosInt>`` parameter (refinements are erased
  for compatibility), so the payload predicate is not even claimed.

The disclosing obligation used to be the producer's own ``Some(…)``
CONSTRUCTION site.  #1426 guards the four construction-position component
stores, so that store now traps on the value the refinement forbids and the
producer genuinely establishes its declared type — a caller may prove from it,
and rightly.  Every cell that measures what a caller does with a fact its
producer withheld therefore moved to a producer that is still disclosed, which
``_TINY`` below spells out and justifies; none of them changed what it claims.

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

# A refinement whose BASE is itself a refinement — the shape that is still
# DISCLOSED, and disclosed by DESIGN rather than by an omission.
#
# What a producer discloses is decided by `disclosed_fn_names`: a function
# joins the set when one of its own obligations resolved `tier3_unguarded`
# (or the E534 demotion), because a `tier3` that IS guarded makes the declared
# type true at run time and a consumer may lean on it.  Until #1426 the
# construction-position component stores were that unguarded set, so the
# obvious producer — `mk(@Float64 -> @Option<PosInt>) { Some(float_to_int(x)) }`
# — disclosed at its `Some(…)` store and every cell below could ask what a
# caller does with a fact its producer admitted it had not established.  That
# store is guarded now: it traps on the value the refinement forbids, so the
# producer genuinely establishes `Option<PosInt>` and callers may prove from
# it.  The cells that measure withholding therefore moved their producer, not
# their claim.
#
# Composing two membership predicates is unsupported, and a guard that kept
# only the outer one would silently drop the inner — so codegen emits nothing
# for this base ANYWHERE: at a function boundary it refuses the program
# outright (E618) rather than plant a partial guard, and at an internal bind
# it emits no guard and no diagnostic.  `_refined_boundary_codegen_guardable`
# mirrors exactly that, so the obligation records `tier3_unguarded`/E506
# because no guard is emittable, not because one is missing.  Nothing is going
# to close it the way #1426 closed the construction stores.
#
# The E618 half is why the nested refinement is written INSIDE a container and
# bound by a `let`: `-> @Tiny` (or `-> @Tuple<Tiny, Int>`, whose components a
# boundary DOES decompose) is refused at compile, while `@Option<Tiny>` at a
# boundary compiles — the decomposition reaches a parameter's own refinement
# and its tuple components and no further — and a `let` is not a boundary at
# all.  Each producer below therefore binds the payload at the nested
# refinement, where no store guard can be emitted, and forwards that slot into
# a declared return type spelled at `PosInt`, which is what keeps the
# consumers' parameter types — and their Tier-1 postcondition proofs — exactly
# as they were.  `Tiny` is a SUBTYPE of `PosInt`, so the forwarding is not a
# false relabelling: the producer's declared type is true of every value that
# is really a `Tiny`, and what it cannot do is establish that this one is.
#
# For an ADT payload the producer then discloses TWICE, and the two are worth
# telling apart because only one of them is durable:
#
# * the `Some(…)` store into an `Option<Tiny>` component — no guard is
#   emittable for that base at any site, ever; and
# * the producer's own RETURN slot — a refinement written on an ADT payload is
#   decomposed at no boundary, so a return that publishes one it did not
#   discharge is unguarded too.
#
# The second is inherent rather than chosen: a producer that fails to establish
# its payload cannot discharge the return goal either, so it always discloses
# there.  Measured, by mutating `Tiny`'s base to a plain `@Int`: the store
# becomes `tier3` and the Option cells stay green off the return slot alone,
# while all three TUPLE cells go red — a tuple return IS decomposed at the exit,
# so there the nested base is the only thing left that can disclose.  The
# nested base is what this constant is for; keep it nested.
_TINY = "\ntype Tiny = { @PosInt | @PosInt.0 < 10 };\n"

_DISCLOSING_PRELUDE = _PRELUDE + _TINY

# The issue's reproducer, with the producer moved to the still-disclosed shape.
_1410_REPRO = _DISCLOSING_PRELUDE + """
private fn mk(@Float64 -> @Option<PosInt>)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Option<Tiny> = Some(float_to_int(@Float64.0));
  @Option<Tiny>.0
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
_WRAPPER = _DISCLOSING_PRELUDE + """
private fn mk(@Float64 -> @Option<PosInt>)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Option<Tiny> = Some(float_to_int(@Float64.0));
  @Option<Tiny>.0
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
# `consume(mk(x))`, so it must carry the identical obligation.  Its producer
# tracks `_1410_REPRO`'s exactly — a spelling comparison only says something
# when the two programs differ in the spelling and nothing else, so when the
# reproducer's `mk` moved to the still-disclosed `let @Option<Tiny>` this one
# moved with it in the same edit.
_PIPED = _DISCLOSING_PRELUDE + """
private fn mk(@Float64 -> @Option<PosInt>)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Option<Tiny> = Some(float_to_int(@Float64.0));
  @Option<Tiny>.0
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

    `mk` is the `let @Option<Tiny>` producer rather than the bare
    `Some(float_to_int(x))` the issue reported: that store is guarded since
    #1426 and now establishes `Option<PosInt>`, so a caller proving from it is
    correct rather than a hole.  `_TINY` says which of the replacement's two
    positions discloses why.  `consume` keeps its parameter at `PosInt` and
    its postcondition at Tier 1, which is what makes the pairing below a
    false-Tier-1 differential rather than a Tier-3 check doing its job.
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


def _assert_refuses_the_payload(proc: "subprocess.CompletedProcess[str]") -> None:
    """The compiled program REFUSES the value the refinement forbids.

    Which check catches it first is not the property under test.  Before
    #765 the payload travelled unguarded to `consume`, whose postcondition
    refuted it; since #765 the constructor sub-pattern bind guards the
    payload where it is unwrapped and traps first.  Both are the contract
    refusing at run time, which is what makes a Tier-1 claim about this
    program a soundness bug.  A clean exit still reds this, which is the
    force the original assertion had.
    """
    out = proc.stdout + proc.stderr
    assert proc.returncode != 0, proc.stdout
    assert ("Postcondition violation in consume" in out
            or "Refinement violation in constructor sub-pattern" in out), out


def test_1410_run_still_refutes_the_contract(tmp_path: Path) -> None:
    """The differential half: the compiled program disagrees with a Tier-1
    claim, which is what makes the obligation's absence a soundness bug."""
    proc = _run(tmp_path, _1410_REPRO, "-7.0")
    assert proc.returncode != 0, proc.stdout
    _assert_refuses_the_payload(proc)


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


def test_wrapper_chain_discloses_at_every_link(tmp_path: Path) -> None:
    """One forwarding wrapper must not launder a disclosed producer.

    `wrap` declares `-> Option<PosInt>` and returns a bare `mk(@Float64.0)`.
    Measured on this PR's own first head, with the ARGUMENT rule in and the
    RETURN rule not: `wrap` published the declared type with no obligation of
    its own, so it never joined the disclosed set, and `consume(wrap(...))`
    proved its argument at Tier 1 from `wrap`'s declared type while the run
    refuted `consume`'s postcondition — the #1410 hole restored by a single
    hop.  Obligating the return closes it TRANSITIVELY through the
    disclosed-set fixpoint rather than per-caller: `wrap` discloses, and every
    caller's argument obligation then withholds the same premise it withholds
    for `mk`.

    There has to BE something for the fixpoint to carry, and since #1426 the
    plain `Some(…)` store `mk` used to disclose at is guarded — it establishes
    the declared type, so nothing propagates and the chain is honestly clean.
    `mk` is the `let @Option<Tiny>` producer now (see `_TINY`), whose
    disclosures are both by design rather than by omission — so what this cell
    measures is the fixpoint carrying one along the chain, not a gap in the
    guard set that a later PR would quietly close underneath it.
    """
    at_wrap = _refine_binds(_WRAPPER, "wrap")
    at_f = _refine_binds(_WRAPPER, "f")
    assert at_wrap, "the wrapper's own return raised no obligation"
    assert at_f, "the wrapped argument raised no obligation"
    assert all(o.status != "verified" for o in at_wrap + at_f), (
        _statuses(at_wrap), _statuses(at_f))
    _assert_accounting(tmp_path, _WRAPPER)

    proc = _run(tmp_path, _WRAPPER, "-7.0", name="w1.vera")
    assert proc.returncode != 0, proc.stdout
    _assert_refuses_the_payload(proc)


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
    _assert_refuses_the_payload(proc)


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


@pytest.mark.parametrize(
    "source,expected",
    [(_ARRAY_ESTABLISHED, [("verified", "")]),
     (_ARRAY_UNESTABLISHED, [("violated", "E505")])],
    ids=["source-carries-it", "source-does-not"])
def test_array_element_refinement_is_discharged_not_disclosed(
    source: str, expected: list[tuple[str, str]],
) -> None:
    """An array ELEMENT predicate is now STATED and answered (#1430 stage 1).

    Both spellings disclosed `tier3_unguarded`/E506 when this cell was
    written, because the goal — "every element satisfies P" — needs a
    quantifier over indices and nothing stated one.  #1430 states it as
    `forall i. 0 <= i < length(a) => P(index(a, i))` over the same
    uninterpreted `index_` / `length_` observers array literals and `arr[i]`
    already use, so the two spellings now legitimately DIFFER:

    * the producer whose declared return carries the refinement discharges it
      from the element fact its own return position was obligated to
      establish, and reports `verified`;
    * the producer typed `Array<Int>` establishes nothing, so the goal is
      REFUTED — `violated`/E505 with a counterexample, not a shrug.

    PR #1420's F4 ruling is preserved rather than weakened, and that is the
    point of keeping this cell: the `verified` comes from a discharged
    obligation — a solver query over a stated goal — and never from comparing
    one declared type against another.  The difference between the two
    spellings is now EARNED, where the draft F4 rejected asserted it.
    """
    binds = _refine_binds(source, "f")
    assert _statuses(binds) == expected, _statuses(binds)


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


_GENERIC_FORMAL = _DISCLOSING_PRELUDE + """
private fn mk(@Float64 -> @Option<PosInt>)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Option<Tiny> = Some(float_to_int(@Float64.0));
  @Option<Tiny>.0
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

    Both calls raise one, and — measured on the E506 rationales — for two
    DIFFERENT reasons, which is why the columns and not a status set are what
    this pins.  ``ident``'s argument is ``mk(...)``, and its proof "leans on a
    declared-type fact this run disclosed": the disclosed-producer taint.
    ``consume``'s argument is ``ident(...)``, whose value "is outside the SMT
    layer's decidable fragment": a generic call's result carries no term to
    state the payload obligation against, so it discloses whatever ``mk``
    does — it did so while ``mk`` was still clean.  The emission is what this
    rule owns and it happens at BOTH.

    ``mk`` is the `let @Option<Tiny>` producer (see `_TINY`).  Its old
    `Some(float_to_int(x))` store is guarded since #1426 and establishes
    `Option<PosInt>`, which left the inner position `verified` — the outer one
    would have stayed disclosed on its own, so the pair would have gone on
    looking measured while only one half was still testing the taint.
    """
    binds = _refine_binds(_GENERIC_FORMAL, "f")
    # BOTH positions, each named by its own column, rather than a status set
    # (PR review): a set accepts the inverted assignment, which would be a
    # different program's behaviour.  The outer argument is `ident(mk(...))`
    # at `consume`'s call and the inner is `mk(...)` at `ident`'s, so the
    # inner starts to the RIGHT — the columns are what pin the attribution.
    assert sorted((o.status, o.column) for o in binds) == [
        ("tier3_unguarded", 11), ("tier3_unguarded", 17),
    ], [(o.status, o.line, o.column) for o in binds]


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


_TUPLE_DISCLOSED = _DISCLOSING_PRELUDE + """
private fn mk(@Float64 -> @Tuple<PosInt, Int>)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Tuple<Tiny, Int> = Tuple(float_to_int(@Float64.0), 5);
  @Tuple<Tiny, Int>.0
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
    and guard must agree (#1362), and here the guard exists.

    The component `consume` receives has to stay spelled `PosInt` for that to
    be a real claim: `Tuple<Tiny, Int>` at a boundary is refused outright
    (E618), and a fixture the compiler will not accept cannot witness a guard
    that fires.  So the disclosure lives one step back, in `mk`'s
    `let @Tuple<Tiny, Int>` — a `let` is not a boundary, so the nested base is
    silently unguarded there instead of refused, which is the `tier3_unguarded`
    that puts `mk` in the disclosed set.  `mk`'s old `Tuple(float_to_int(x), 5)`
    store establishes the declared type since #1426, so the withholding this
    cell classifies would not have happened at all.
    """
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


_OPAQUE_BAD_LINK = _PARTIALLY_STATABLE.replace(
    "  ensures(@Chain<Int>.result == End)\n", "  ensures(true)\n").replace(
    "{\n  End\n}", "{\n  Link(0 - 9, End)\n}")


def test_a_recursive_tail_is_stated_and_still_refuses_an_unestablished_one(
) -> None:
    """The tail position is STATED now, and that is not an overstatement.

    When this cell was written the walk had to stop at the cycle — a recursive
    type has no finite unrolling — so the tail could not be stated at all, and
    recording `verified` on the strength of the half that proved would have
    claimed the tail's links were established too.  #1430 stage 2 states it as
    an opaque `refines_K(tail)` carried identically on both sides, so the
    question becomes whether the source can DISCHARGE it, and the two halves
    of this cell are the answer.

    With `mk` pinned to `End` the goal is genuinely true — `End` has no links,
    so "every link's head is positive" holds vacuously — and `verified` is
    correct rather than generous.  Change `mk` to return `Link(0 - 9, End)`
    with no refinement on its declared type and the same goal is REFUTED with
    E505: nothing licenses the fact, so nothing discharges it.  The
    overstatement this cell was written to catch is still caught; what changed
    is that the vacuous case is now recognised as vacuous.
    """
    binds = _refine_binds(_PARTIALLY_STATABLE, "f")
    assert _statuses(binds) == [("verified", "")], _statuses(binds)

    bad = _refine_binds(_OPAQUE_BAD_LINK, "f")
    assert _statuses(bad) == [("violated", "E505")], _statuses(bad)


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

type Tiny = { @PosInt | @PosInt.0 < 10 };

private fn mk(@Float64 -> @Option<PosInt>)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Option<Tiny> = Some(float_to_int(@Float64.0));
  @Option<Tiny>.0
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

    The producer here is the still-disclosed one (see `_TINY`): `mk` binds the
    payload at a refinement whose base is a refinement, which no guard can be
    emitted for, so it discloses by design where the plain `Some(…)` store it
    used to use is guarded since #1426 and establishes its declared type.  The
    line the obligation must land on is READ OFF the fixture rather than
    written as a constant — the constant said 18, the producer grew two lines,
    and a filter that matches nothing passes its own `all(...)` check while
    the presence assertion below is the only thing standing between that and a
    green cell measuring an empty list.
    """
    (tmp_path / "lib").mkdir()
    (tmp_path / "lib" / "box.vera").write_text(_XMOD_LIB, encoding="utf-8")
    main = tmp_path / "main.vera"
    main.write_text(_XMOD_MAIN, encoding="utf-8")

    call_line = 1 + _XMOD_MAIN.splitlines().index("  consume(mk(@Float64.0))")
    proc = _cli("verify", "--json", str(main))
    env = json.loads(proc.stdout)
    at_call = [
        o for o in env["obligations"]
        if o["kind"] == "refine_bind" and o["location"]["line"] == call_line
    ]
    assert at_call, [
        (o["kind"], o["status"], o["location"]["line"])
        for o in env["obligations"]
    ]
    assert all(o["status"] != "verified" for o in at_call), at_call

    run = _cli("run", str(main), "--fn", "f", "--", "-7.0")
    assert run.returncode != 0
    _assert_refuses_the_payload(run)


_XMOD_DISCLOSED_LIB = """\
module lib.mk;

type PosInt = { @Int | @Int.0 > 0 };

type Tiny = { @PosInt | @PosInt.0 < 10 };

public fn mk(@Float64 -> @Option<PosInt>)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Option<Tiny> = Some(float_to_int(@Float64.0));
  @Option<Tiny>.0
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

    `lib.mk`'s producer is the `let @Option<Tiny>` one (see `_TINY`), because
    the `Some(float_to_int(x))` store it used to disclose at is guarded since
    #1426 and publishes an `Option<PosInt>` the importer may lean on.  With
    nothing in the defining module's manifest there is no disclosure for the
    import to carry, so the cell would have gone green measuring the empty
    case.  The exact single-entry list is still the point: the importer's
    stream holds ONE `refine_bind`, the argument's, and the library's own two
    stay in the library's.
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
    _assert_refuses_the_payload(run)


# =====================================================================
# The return slot — the position that makes the argument rule transitive
# =====================================================================

_ARRAY_LITERAL_RETURN = _PRELUDE + """
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


def test_array_literal_return_is_a_construction_not_a_disclosure() -> None:
    """An `ArrayLit` builds its value HERE, so the return slot excludes it.

    The term test cannot see this one — an array term is not a datatype
    constructor application — so the syntactic half has to name it.  Without
    that, a `fn mk(@Int -> @Array<PosInt>) { [1, 2, 3] }` disclosed its own
    return (the element predicate is not statable) and, being disclosed,
    poisoned every caller: two E506 warnings about elements that are
    manifestly positive.  Whether an array literal's ELEMENTS are obligated is
    a separate question, closed by #1426's construction descent: each element
    is now obligated where it is built, and `1`, `2`, `3` PROVE.  The property
    here is unchanged by that — the boundary discloses nothing — so the cell
    reads for the absence of a DISCLOSURE rather than the absence of every
    record, which would have made it a restatement of what the other rule
    does.
    """
    binds = _refine_binds(_ARRAY_LITERAL_RETURN, "mk")
    statuses = _statuses(binds)
    assert all(status == "verified" for status, _ in statuses), statuses


def test_clean_forwarding_return_still_verifies() -> None:
    """The return rule must not fire on a wrapper whose producer is clean:
    `mk` builds `Some(7)`, so its declared type IS established and forwarding
    it proves at Tier 1."""
    src = _CLEAN_PRODUCER.replace(
        "public fn f(@Float64 -> @Int)",
        """private fn wrap(@Float64 -> @Option<PosInt>)
  requires(true)
  ensures(true)
  effects(pure)
{
  mk(@Float64.0)
}

public fn f(@Float64 -> @Int)""",
    ).replace("consume(mk(@Float64.0))", "consume(wrap(@Float64.0))")
    binds = _refine_binds(src, "wrap") + _refine_binds(src, "f")
    assert binds, "the forwarding return and argument raised no obligation"
    assert all(o.status == "verified" for o in binds), _statuses(binds)


def test_nullary_constructor_is_no_payload_not_an_unreadable_one() -> None:
    """`_payload_field_types` splits what `_instantiated_field_types` folds.

    Both walks that read constructor fields FAIL CLOSED when they cannot read
    them — an unreadable instantiation hides positions, and neither
    "established" nor "guarded" is something a walk can claim over hidden
    positions.  `_instantiated_field_types` answers `None` for a nullary
    constructor too, and `Option`'s `None` is the everyday case, so closing on
    that answer would close on every optional there is.

    Asserted directly on the helper rather than through a program: the two
    answers are indistinguishable end-to-end TODAY (only tuples are guarded,
    and a tuple has one constructor with no nullary sibling), so a
    program-level cell would pass whichever way the helper behaved.  This is
    the distinction the next position added to the guarded set would trip over.
    """
    from vera.checker import typecheck_with_artifacts
    from vera.parser import parse_to_ast
    from vera.verifier import ContractVerifier
    from vera.types import AdtType, PrimitiveType

    src = _PRELUDE + """
public fn f(@Option<PosInt> -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match @Option<PosInt>.0 { Some(@PosInt) -> @PosInt.0, None -> 1 }
}
"""
    program = parse_to_ast(src)
    diags, arts = typecheck_with_artifacts(program, src)
    assert not [d for d in diags if d.severity == "error"], diags
    v = ContractVerifier(src)
    v.register_program(program)
    opt_int = AdtType(name="Option", type_args=(PrimitiveType(name="Int"),))

    assert v._payload_field_types("None", opt_int) == (), (
        "a nullary constructor has no payload; answering None would fail every "
        "walk closed on every optional"
    )
    assert v._payload_field_types("Some", opt_int) == (
        PrimitiveType(name="Int"),)
    assert v._payload_field_types("NoSuchCtor", opt_int) is None, (
        "an unreadable constructor must stay None so the walks fail closed"
    )


_TUPLE_WRAPPER = _DISCLOSING_PRELUDE + """
private fn mk(@Float64 -> @Tuple<PosInt, Int>)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Tuple<Tiny, Int> = Tuple(float_to_int(@Float64.0), 5);
  @Tuple<Tiny, Int>.0
}

private fn wrap(@Float64 -> @Tuple<PosInt, Int>)
  requires(true)
  ensures(true)
  effects(pure)
{
  mk(@Float64.0)
}

public fn f(@Float64 -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match wrap(@Float64.0) {
    Tuple(@PosInt, @Int) -> @PosInt.0
  }
}
"""


def test_return_slot_guardedness_matches_the_return_epilogue(
    tmp_path: Path,
) -> None:
    """The return slot reads the same guard derivation the argument does, and
    it has to be true of a DIFFERENT codegen site.

    A tuple parameter's components are guarded at the callee's ENTRY; a tuple
    return's are guarded at the producer's EXIT.  Both are
    `_emit_component_refinement_guards`, so one derivation answers for both —
    but a rule that only ever checked the entry side would be claiming the
    exit side without measuring it.  Here the forwarding wrapper's return
    records the guarded `tier3`, and the run traps on `mk`'s return-value
    component guard, which is the site being claimed.

    The return epilogue is only the site that fires if nothing upstream of it
    does, and #1426 put a guard on the `Tuple(float_to_int(x), 5)` store `mk`
    used to build directly: the run trapped inside the construction and never
    reached an epilogue at all, so the cell stopped measuring the site named
    in its own assertion.  `mk` now builds through a `let @Tuple<Tiny, Int>`,
    whose component is a refinement over a refinement — no store guard is
    emittable for that base, so the value travels to the exit, where the
    declared `Tuple<PosInt, Int>` IS decomposed and does trap.  The same bind
    is `mk`'s disclosure, which is what stops `wrap`'s forwarding return
    proving at Tier 1 and leaves the `tier3` this cell classifies.
    """
    binds = _refine_binds(_TUPLE_WRAPPER, "wrap")
    assert _statuses(binds) == [("tier3", "E506")], _statuses(binds)

    proc = _run(tmp_path, _TUPLE_WRAPPER, "-7.0", name="tw.vera")
    assert proc.returncode != 0, proc.stdout
    out = proc.stdout + proc.stderr
    assert "Refinement violation in mk" in out and "return value" in out, out


_LET_BOUND_DISCLOSED = _DISCLOSING_PRELUDE + """
private fn mk(@Float64 -> @Option<PosInt>)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Option<Tiny> = Some(float_to_int(@Float64.0));
  @Option<Tiny>.0
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
  let @Option<PosInt> = mk(@Float64.0);
  consume(@Option<PosInt>.0)
}
"""


def test_let_bound_disclosed_value_still_raises_the_obligation() -> None:
    """The one spelling this rule cannot answer for, pinned as PRESENCE only.

    A `let`-bound disclosed value passed on within the SAME function reaches
    the argument as a slot reference.  No leaf descent attributes that to its
    producer — the wrapper spelling is closed here because a wrapper is a
    FUNCTION and the return slot obligates it, but a `let` is not, and
    disclosure is a fact about functions.  Following the taint to the VALUE is
    #1406/#1407's rule, and this checkpoint is what will consult it.

    Asserted as presence, deliberately: pinning today's status would go red the
    moment that rule lands, which is the direction we want it to move.

    A presence assertion holds whatever the producer does, so this cell did not
    go red when #1426 guarded `mk`'s `Some(…)` store — it simply stopped having
    a disclosed value in it, which is the whole subject of its name and its
    docstring.  `mk` moved to the still-disclosed `let @Option<Tiny>` with the
    cells that did go red, so the spelling under test is once again the one
    described.
    """
    binds = _refine_binds(_LET_BOUND_DISCLOSED, "f")
    assert binds, (
        "the let-bound argument raised no obligation at all; emission must not "
        "depend on how the producer was spelled, whatever the taint can reach"
    )


_VIOLATED_PRECONDITION = _PRELUDE + """
private fn mk(@Int -> @Option<PosInt>)
  requires(@Int.0 > 0)
  ensures(true)
  effects(pure)
{
  Some(@Int.0)
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
"""


def test_an_opaque_call_result_discloses_rather_than_certifying() -> None:
    """A payload the solver cannot see is disclosed, even when the producer
    did in fact establish it.

    `mk`'s own precondition is unmet at this call — a real E501 — and that
    makes the result OPAQUE, so there is no term to state the payload
    obligation against.  `mk`'s construction discharges at Tier 1, so the
    payload IS established; an earlier draft read that off the declared type
    and answered `verified`, which PR #1420's review (F4) rejected: a
    `verified` may only come from a discharged obligation, and nothing was
    discharged here.  The honest answer is the disclosure, and its cost is a
    second warning at a call that already has an error.  Its construction site
    keeps its own Tier-1 proof, which is what says the payload is fine.
    """
    at_mk = _refine_binds(_VIOLATED_PRECONDITION, "mk")
    assert _statuses(at_mk) == [("verified", "")], _statuses(at_mk)
    binds = _refine_binds(_VIOLATED_PRECONDITION, "f")
    assert _statuses(binds) == [("tier3_unguarded", "E506")], _statuses(binds)


# =====================================================================
# PR #1420 adversarial review — the shapes the first head missed
# =====================================================================

_UNREFINED_OPT = """
private fn mkint(@Float64 -> @Option<Int>)
  requires(true)
  ensures(true)
  effects(pure)
{
  Some(float_to_int(@Float64.0))
}
"""

_CONSUME_OPT = """
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
"""

# F1 — same-name NESTING, which a name-keyed cycle guard pruned as recursion.
_NESTED_SAME_NAME = _PRELUDE + """
private fn mk2(@Float64 -> @Option<Option<Int>>)
  requires(true)
  ensures(true)
  effects(pure)
{
  Some(Some(float_to_int(@Float64.0)))
}

private fn consume2(@Option<Option<PosInt>> -> @Int)
  requires(true)
  ensures(@Int.result > 0)
  effects(pure)
{
  match @Option<Option<PosInt>>.0 {
    Some(@Option<PosInt>) -> match @Option<PosInt>.0 {
      Some(@PosInt) -> @PosInt.0,
      None -> 41
    },
    None -> 42
  }
}

public fn f(@Float64 -> @Int)
  requires(true)
  ensures(@Int.result > 0)
  effects(pure)
{
  consume2(mk2(@Float64.0))
}
"""

# F7 — the same prune, at a position codegen DOES guard.
_NESTED_SAME_NAME_TUPLE = _PRELUDE + """
private fn mkt(@Float64 -> @Tuple<Tuple<Int, Int>, Int>)
  requires(true)
  ensures(true)
  effects(pure)
{
  Tuple(Tuple(float_to_int(@Float64.0), 2), 3)
}

private fn consume_t(@Tuple<Tuple<PosInt, Int>, Int> -> @Int)
  requires(true)
  ensures(@Int.result > 0)
  effects(pure)
{
  match @Tuple<Tuple<PosInt, Int>, Int>.0 {
    Tuple(@Tuple<PosInt, Int>, @Int) -> match @Tuple<PosInt, Int>.0 {
      Tuple(@PosInt, @Int) -> @PosInt.0
    }
  }
}

public fn f(@Float64 -> @Int)
  requires(true)
  ensures(@Int.result > 0)
  effects(pure)
{
  consume_t(mkt(@Float64.0))
}
"""

# A genuine cycle, which the guard must still stop at.
_RECURSIVE_ADT = _PRELUDE + """
private data Chain {
  Link(PosInt, Chain),
  End
}

private fn consume_c(@Chain -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match @Chain.0 {
    Link(@PosInt, @Chain) -> @PosInt.0,
    End -> 1
  }
}

public fn f(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  consume_c(Link(7, End))
}
"""


@pytest.mark.parametrize(
    ("source", "consumer"),
    [(_NESTED_SAME_NAME, "consume2"), (_NESTED_SAME_NAME_TUPLE, "consume_t")],
    ids=["option-in-option", "tuple-in-tuple"])
def test_same_name_nesting_is_not_a_cycle(source: str, consumer: str) -> None:
    """`Option<Option<PosInt>>` is nesting, not recursion.

    The cycle guard keyed on the ADT's NAME and added it on the way down, so
    the inner `Option` was pruned as though the walk had come back round to
    itself: the emission gate answered False, no obligation was raised at all,
    and the program was Tier-1 clean while the run refuted the consumer
    (PR #1420 review F1).  `Tuple<Tuple<PosInt, Int>, Int>` is the same prune
    at a position codegen DOES guard, so it was also a lockstep gap (F7).
    Keying on the instantiated type tells the two apart.
    """
    binds = _refine_binds(source, "f")
    assert binds, "the nested-instantiation argument raised no obligation"
    assert ("violated", "E505") in _statuses(binds), _statuses(binds)


def test_a_real_cycle_still_stops_the_walk() -> None:
    """The other side of the same key: a genuinely recursive `data` must not
    send the walk round for ever.  `Chain`'s field is `Chain` at the identical
    instantiation, so the key repeats and the walk stops — the construction
    here is excluded, and the program verifies rather than hanging."""
    result = _verify_source(_RECURSIVE_ADT)
    assert [d for d in result.diagnostics if d.severity == "error"] == []


# F2 — a branch join with one constructed arm.
def _join_fixture(spelling: str) -> str:
    body = {
        "if": "consume(if @Float64.0 > 0.0 then { Some(7) } "
              "else { mkint(@Float64.0) })",
        "match": "consume(match @Float64.0 > 0.0 { "
                 "true -> Some(7), false -> mkint(@Float64.0) })",
    }[spelling]
    return _PRELUDE + _UNREFINED_OPT + _CONSUME_OPT + f"""
public fn f(@Float64 -> @Int)
  requires(true)
  ensures(@Int.result > 0)
  effects(pure)
{{
  {body}
}}
"""


@pytest.mark.parametrize("spelling", ["if", "match"], ids=["if", "match"])
def test_a_join_with_one_constructed_arm_still_obligates(spelling: str) -> None:
    """One constructed arm must not excuse the other.

    The construction exclusion took `any` over the arms, so a join with a
    literal `Some(7)` on one side was skipped entirely — the constructed arm
    kept its own field obligation and the other arm was asked nothing, leaving
    the consumer's postcondition `verified` while the run took that arm and
    refuted it (PR #1420 review F2).  The exclusion now holds only when EVERY
    value-producing leaf constructs.
    """
    binds = _refine_binds(_join_fixture(spelling), "f")
    assert ("violated", "E505") in _statuses(binds), _statuses(binds)


# F3 — a construction whose FIELD type carries a nested refinement.
_NESTED_FIELD_CONSTRUCTION = _PRELUDE + """
private data Box {
  MkBox(Option<PosInt>)
}
""" + _UNREFINED_OPT + """
private fn consume(@Box -> @Int)
  requires(true)
  ensures(@Int.result > 0)
  effects(pure)
{
  match @Box.0 {
    MkBox(@Option<PosInt>) -> match @Option<PosInt>.0 {
      Some(@PosInt) -> @PosInt.0,
      None -> 41
    }
  }
}

public fn f(@Float64 -> @Int)
  requires(true)
  ensures(@Int.result > 0)
  effects(pure)
{
  consume(MkBox(mkint(@Float64.0)))
}
"""


def test_a_constructor_field_claims_its_nested_refinement(
    tmp_path: Path,
) -> None:
    """The exclusion's justification has to be true of the site it excuses.

    `MkBox(mkint(x))` was skipped as a construction, and the constructor-field
    rule claims a field's HEAD refinement only — `Option<PosInt>` is not one —
    so the payload was obligated nowhere and the program was Tier-1 clean while
    the run refuted the consumer (PR #1420 review F3).  The field now carries
    the nested obligation too, which is what makes "its own site already
    carries it" a true statement.
    """
    binds = _refine_binds(_NESTED_FIELD_CONSTRUCTION, "f")
    assert ("violated", "E505") in _statuses(binds), _statuses(binds)

    proc = _run(tmp_path, _NESTED_FIELD_CONSTRUCTION, "-7.0", name="b.vera")
    assert proc.returncode != 0, proc.stdout
    _assert_refuses_the_payload(proc)


# F6 — an effect operation's argument.
_THROW_PAYLOAD = _PRELUDE + _UNREFINED_OPT + _CONSUME_OPT + """
private fn thrower(@Float64 -> @Int)
  requires(true)
  ensures(true)
  effects(<Exn<Option<PosInt>>>)
{
  throw(mkint(@Float64.0))
}

public fn f(@Float64 -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[Exn<Option<PosInt>>] {
    throw(@Option<PosInt>) -> { consume(@Option<PosInt>.0) }
  } in { thrower(@Float64.0) }
}
"""


def test_an_effect_operation_argument_is_obligated() -> None:
    """Spec §2.6.4 lists effect-operation arguments, and the call-argument loop
    never reaches them — a bare operation has no `param_types`, so it takes the
    other branch entirely.

    `throw(mkint(x))` under `Exn<Option<PosInt>>` raised nothing: with the
    handler clause forwarding its binder on, the program was `tier1_verified:
    9`, exit 0, every contract `verified`, and the run refuted the consumer's
    postcondition (PR #1420 review F6).  The shared binding triple now carries
    the nested obligation, so every site it serves — the `throw` payload, a
    `State` write, a handler's state init, a `resume` value, a user effect's
    operation — is covered by one arm.  None of them is a function boundary,
    so the nested positions are unguarded whatever the head's guard does.
    """
    binds = _refine_binds(_THROW_PAYLOAD, "thrower")
    assert ("violated", "E505") in _statuses(binds), _statuses(binds)


# F5 — all three spellings of one disclosed producer, pinned together.
_DISCLOSED_PRODUCER = _DISCLOSING_PRELUDE + """
private fn mk(@Float64 -> @Option<PosInt>)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Option<Tiny> = Some(float_to_int(@Float64.0));
  @Option<Tiny>.0
}
""" + _CONSUME_OPT

_SPELLINGS = {
    "direct": _DISCLOSED_PRODUCER + """
public fn f(@Float64 -> @Int)
  requires(true)
  ensures(@Int.result > 0)
  effects(pure)
{
  consume(mk(@Float64.0))
}
""",
    "let-bound": _DISCLOSED_PRODUCER + """
public fn f(@Float64 -> @Int)
  requires(true)
  ensures(@Int.result > 0)
  effects(pure)
{
  let @Option<PosInt> = mk(@Float64.0);
  consume(@Option<PosInt>.0)
}
""",
    "wrapper": _DISCLOSED_PRODUCER + """
private fn wrap(@Float64 -> @Option<PosInt>)
  requires(true)
  ensures(true)
  effects(pure)
{
  mk(@Float64.0)
}

public fn f(@Float64 -> @Int)
  requires(true)
  ensures(@Int.result > 0)
  effects(pure)
{
  consume(wrap(@Float64.0))
}
""",
}


@pytest.mark.parametrize("spelling", sorted(_SPELLINGS))
def test_every_spelling_of_a_disclosed_producer_is_disclosed_somewhere(
    spelling: str, tmp_path: Path,
) -> None:
    """No spelling of one disclosed producer leaves the program Tier-1 clean.

    The review (F5) measured the discharge as spelling-DEPENDENT: direct
    disclosed, `let`-bound and wrapper-forwarded both proved, and all three
    refuted at run time.  Two of the three are closed by obligating the
    positions where a value acquires a nested-refined declared type — the
    wrapper at its RETURN slot, the `let` at its binder — so each carries its
    own disclosure and the fixpoint carries the wrapper's on to its callers.

    The `let`-bound ARGUMENT itself still reads `verified`: the value reaches
    it as a slot reference, and attributing that to its producer is
    value-level taint, which is #1406/#1407's rule.  What this asserts is the
    property that matters — the program discloses SOMEWHERE, so no reader is
    left with an unqualified Tier-1 claim — which is true of all three now and
    stays true when that rule lands.

    The disclosure this quantifies over has to be the producer's, and #1426
    guards the `Some(float_to_int(x))` store the old `mk` disclosed at.  What
    went red was the RUN half rather than the stream half: the store's own
    guard traps first, and `_assert_refuses_the_payload` reds a program that
    never reaches the consumer, because a trap at construction says nothing
    about what a caller was allowed to assume downstream of it.  `mk` moved to
    the `let @Option<Tiny>` producer (see `_TINY`), where the store carries no
    emittable guard, so the value travels to `consume` and is refused where the
    assumption was made.
    """
    src = _SPELLINGS[spelling]
    result = _verify_source(src)
    binds = [o for o in result.obligations if o.kind == "refine_bind"]
    assert any(o.status in ("tier3_unguarded", "tier3", "violated")
               for o in binds), (
        f"{spelling}: every obligation on a disclosed producer's chain "
        f"claimed Tier 1 — {[(o.fn_name, o.status) for o in binds]}"
    )

    proc = _run(tmp_path, src, "-7.0", name=f"{spelling}.vera")
    assert proc.returncode != 0, proc.stdout
    _assert_refuses_the_payload(proc)


# F4b — a `let` binder publishing a nested-refined type.
_LET_PUBLISHES_REFINED = _PRELUDE + _UNREFINED_OPT + _CONSUME_OPT + """
public fn f(@Float64 -> @Int)
  requires(true)
  ensures(@Int.result > 0)
  effects(pure)
{
  let @Option<PosInt> = mkint(@Float64.0);
  consume(@Option<PosInt>.0)
}
"""


def test_a_let_binder_publishing_a_refined_component_is_obligated(
    tmp_path: Path,
) -> None:
    """A `let` gives its slot a declared type, and every later reader leans on
    it — so the binder is one of the positions that must establish it.

    `let @Option<PosInt> = mkint(x)` was Tier-1 clean, exit 0, and refuted at
    run time (PR #1420 review F4b).  An interim form answered `verified` here
    by comparing the declared types, which certifies exactly the claim the
    `let` is making; the binder is obligated instead, and an unrefined RHS is
    a definite refutation.
    """
    binds = _refine_binds(_LET_PUBLISHES_REFINED, "f")
    assert ("violated", "E505") in _statuses(binds), _statuses(binds)

    proc = _run(tmp_path, _LET_PUBLISHES_REFINED, "-7.0", name="lp.vera")
    assert proc.returncode != 0, proc.stdout
    _assert_refuses_the_payload(proc)


_LAUNDERING_RETURN = _PRELUDE + _UNREFINED_OPT + _CONSUME_OPT + """
private fn launder(@Option<Int> -> @Option<PosInt>)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Option<Int>.0
}

public fn f(@Float64 -> @Int)
  requires(true)
  ensures(@Int.result > 0)
  effects(pure)
{
  consume(launder(mkint(@Float64.0)))
}
"""


def test_a_return_that_relabels_an_unrefined_payload_is_refuted(
    tmp_path: Path,
) -> None:
    """A declared return type is a claim, not a fact.

    `launder(@Option<Int> -> @Option<PosInt>) { @Option<Int>.0 }` type-checks
    — a refinement is erased for compatibility — and publishes a payload
    invariant it never establishes.  With the type-comparison shortcut in
    place this was `verified` at the caller (PR #1420 review F4a); the return
    slot obligates it and the relabelling is refuted where it happens.
    """
    binds = _refine_binds(_LAUNDERING_RETURN, "launder")
    assert ("violated", "E505") in _statuses(binds), _statuses(binds)

    proc = _run(tmp_path, _LAUNDERING_RETURN, "-7.0", name="ld.vera")
    assert proc.returncode != 0, proc.stdout
    # WHICH non-zero exit: a compile refusal is also non-zero, so the bare
    # code cannot tell a refuted contract from a program that never ran.
    _assert_refuses_the_payload(proc)


_REFINEMENT_OVER_REFINEMENT = """
type Pos = { @Int | @Int.0 > 0 };

type Tiny = { @Pos | @Pos.0 < 10 };

private fn boom(@Float64 -> @Int)
  requires(true)
  ensures(true)
  effects(<Exn<Tiny>>)
{
  throw(float_to_int(@Float64.0))
}

public fn main(@Float64 -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[Exn<Tiny>] {
    throw(@Tiny) -> { @Tiny.0 }
  } in {
    boom(@Float64.0)
  }
}
"""


def test_a_refinement_over_a_refinement_is_not_a_component() -> None:
    """`{ @Pos | @Pos.0 < 10 }` is a HEAD refinement twice over.

    Both predicates belong to the refined-first arms, and codegen refuses the
    shape outright (E618), so the nested rule must see no component here at
    all.  Unwrapping one level of refinement left `Pos` looking like something
    *inside* `Tiny` and raised a second obligation for a position that is not
    a component — caught by `test_exn_throw_payload_1268.py`'s nested-payload
    cell, whose point is that this shape promises one thing and records one
    thing.  The chain is stripped whole instead.
    """
    binds = _refine_binds(_REFINEMENT_OVER_REFINEMENT, "boom")
    assert _statuses(binds) == [("tier3_unguarded", "E506")], _statuses(binds)


_CLOSURE_ARGUMENT = _PRELUDE + """
type Taker = fn(Option<PosInt> -> Int) effects(pure);
""" + _UNREFINED_OPT + _CONSUME_OPT + """
public fn f(@Float64 -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Taker = fn(@Option<PosInt> -> @Int) effects(pure) { consume(@Option<PosInt>.0) };
  apply_fn(@Taker.0, mkint(@Float64.0))
}
"""

_CLOSURE_RETURN = _PRELUDE + """
type Maker = fn(Float64 -> Option<PosInt>) effects(pure);
""" + _UNREFINED_OPT + _CONSUME_OPT + """
public fn f(@Float64 -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Maker = fn(@Float64 -> @Option<PosInt>) effects(pure) { mkint(@Float64.0) };
  consume(apply_fn(@Maker.0, @Float64.0))
}
"""


def test_a_closure_argument_is_obligated(tmp_path: Path) -> None:
    """`apply_fn` is the other site the generic loop cannot reach.

    It is a checker special form with no `param_types`, so it takes its own
    inline chain — structurally the same gap the review found for a bare
    effect operation (F6), and found by asking the same question of the
    remaining sites.  Measured before this arm: `apply_fn(clo, mkint(x))` into
    an `Option<PosInt>` closure formal raised nothing for the argument, the
    lifted body's `consume` proved its postcondition at Tier 1, and the run
    refuted it.  The guard question is the boundary one — codegen decomposes
    a closure's refined formal at the lifted prologue exactly as it does a
    function's — so the derivation is shared, not forced.
    """
    binds = _refine_binds(_CLOSURE_ARGUMENT, "f")
    assert ("violated", "E505") in _statuses(binds), _statuses(binds)

    proc = _run(tmp_path, _CLOSURE_ARGUMENT, "-7.0", name="ca.vera")
    assert proc.returncode != 0, proc.stdout
    _assert_refuses_the_payload(proc)


def test_a_closure_return_discloses_at_its_consumer() -> None:
    """The closure RETURN needs no arm of its own.

    A lifted body is opaque to the SMT layer — its parameters and captures are
    not in the outer slot environment — so obligating the closure's own return
    would either fail to translate or translate against the wrong scope.  It
    does not have to: whatever consumes the `apply_fn` result is itself a
    position that must establish the payload, and an opaque result cannot be
    discharged there, so the chain discloses at the consumer instead of
    claiming Tier 1 anywhere.
    """
    binds = _refine_binds(_CLOSURE_RETURN, "f")
    assert binds, "the consumer of an opaque closure result raised nothing"
    assert all(o.status != "verified" for o in binds), _statuses(binds)


# =====================================================================
# PR #1420 CodeRabbit round 2
# =====================================================================

_GENERIC_CONSTRUCTOR_FIELD = _PRELUDE + """
private data Box<T> {
  MkBox(T)
}
""" + _UNREFINED_OPT + """
private fn consume(@Box<Option<PosInt>> -> @Int)
  requires(true)
  ensures(@Int.result > 0)
  effects(pure)
{
  match @Box<Option<PosInt>>.0 {
    MkBox(@Option<PosInt>) -> match @Option<PosInt>.0 {
      Some(@PosInt) -> @PosInt.0,
      None -> 41
    }
  }
}

public fn f(@Float64 -> @Int)
  requires(true)
  ensures(@Int.result > 0)
  effects(pure)
{
  consume(MkBox(mkint(@Float64.0)))
}
"""


def test_a_generic_constructor_field_recovers_its_instantiation(
    tmp_path: Path,
) -> None:
    """A generic field is a `TypeVar` until the checker says what it became.

    `data Box<T> { MkBox(T) }` built at `Box<Option<PosInt>>` passed the
    registry's unsubstituted field type to the gate, which sees a `TypeVar`,
    finds no refinement in it and emits nothing — so the program was Tier-1
    clean while the run refuted the consumer, even though the CONCRETE
    `MkBox(Option<PosInt>)` spelling of the same program was refuted (PR #1420
    review).  The instantiated target is recovered the way every other
    binding-obligation target recovers one (#747).
    """
    binds = _refine_binds(_GENERIC_CONSTRUCTOR_FIELD, "f")
    assert ("violated", "E505") in _statuses(binds), _statuses(binds)

    proc = _run(tmp_path, _GENERIC_CONSTRUCTOR_FIELD, "-7.0", name="gb.vera")
    assert proc.returncode != 0, proc.stdout
    _assert_refuses_the_payload(proc)


_LET_TUPLE_FROM_DISCLOSED = _DISCLOSING_PRELUDE + """
private fn mkt(@Float64 -> @Tuple<PosInt, Int>)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Tuple<Tiny, Int> = Tuple(float_to_int(@Float64.0), 5);
  @Tuple<Tiny, Int>.0
}

public fn f(@Float64 -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Tuple<PosInt, Int> = mkt(@Float64.0);
  match @Tuple<PosInt, Int>.0 {
    Tuple(@PosInt, @Int) -> @PosInt.0
  }
}
"""


def test_a_let_binding_never_claims_a_boundary_guard() -> None:
    """A `let` is not a function boundary, so it guards nothing.

    Codegen's component decomposition runs at parameter entry and return exit.
    Deriving the flag from the TARGET TYPE made a `let @Tuple<PosInt, Int>`
    record the guarded `tier3` — a runtime check nothing at that site emits,
    which is the #1362 shape, and inconsistent with the refined arm three
    lines above it that has always passed `guarded=False` (PR #1420 review).

    A disclosed producer is what makes the flag observable: a refutable value
    lands on `violated`, where it is never read.  Since #1426 an established
    one lands on `verified`, where it is never read either — `mkt`'s old
    `Tuple(float_to_int(x), 5)` store is guarded now, so the `let` binder
    proved and the flag went unobserved a second way.  `mkt` discloses at a
    `let @Tuple<Tiny, Int>` instead, whose component base is itself a
    refinement and so carries no emittable guard at any site.

    The type under the `f` binder stays `Tuple<PosInt, Int>` on purpose: it is
    a type a boundary WOULD decompose and guard, so an unguarded answer here
    can only have come from the site.  Spelling the binder at the nested
    refinement would make the type half answer first and the cell would stop
    distinguishing the two derivations at all.
    """
    binds = _refine_binds(_LET_TUPLE_FROM_DISCLOSED, "f")
    assert ("tier3_unguarded", "E506") in _statuses(binds), _statuses(binds)
    assert ("tier3", "E506") not in _statuses(binds), _statuses(binds)
