"""The handler-clause binder is obligated and guarded (#1445, #1448).

A clause binder is a pattern-bind site: `throw(@Nat)` on an `Exn<Int>`
handler binds the thrown `@Int` at `@Nat`, and `put(@Pos)` on a
`State<Int>` handler binds the written `@Int` at a refinement.  It was the
last such site with neither a guard nor, in three of its four spellings, an
obligation.

The two issues are different defects at one site, and the cells below keep
them apart:

* **#1445** — the `@Nat` binder over `Exn<Int>` *was* on the record, as
  `tier3_unguarded` / E504, and nothing checked it: `run -- -7` returned
  `-7`.  An honest disclosure with no guard behind it.
* **#1448** — the REFINED binder recorded nothing at all.  `vera verify`
  reported a clean program and the clause body reasoned from `@Pos.0 > 0`
  for a value that was `-7`.  Silence, which is the worse half: an
  unguarded site at least says so.

The `@Nat` disclosure in #1445 was also narrower than it looked.  It came
from the `nat_to_int(@Nat.0)` CALL in that fixture's clause body — a call
argument, not the bind — so it vanished when the body made no such call,
which is why the `State` spelling of the same shape recorded nothing
either.  The obligation added here is at the BINDER, so it does not depend
on what the body happens to do.

The obligation is Tier 3 by nature, not by a failed proof: the bound value
is whatever reaches the operation, and no throw or put site pins it, so a
static discharge would have to hold for every value of the payload type.
That is the case a runtime guard exists for.
"""

from __future__ import annotations

import json
import os
import subprocess
import sys
from pathlib import Path

import pytest

import vera
from tests.codegen_helpers import wat_calls

_PKG_PARENT = str(Path(vera.__file__).resolve().parents[1])

_NAT_TRAP = "Negative value bound into a @Nat slot"
_REFINE_TRAP = "Refinement violation"


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


def _write(tmp_path: Path, source: str, name: str) -> Path:
    p = tmp_path / name
    p.write_text(source, encoding="utf-8")
    return p


def _run(tmp_path: Path, source: str, arg: str, name: str) -> str:
    proc = _cli("run", str(_write(tmp_path, source, name)),
                "--fn", "f", "--", arg)
    return proc.stdout + proc.stderr


def _binds(tmp_path: Path, source: str, name: str) -> tuple[list, dict]:
    proc = _cli("verify", "--json", str(_write(tmp_path, source, name)))
    envelope = json.loads(proc.stdout)
    return ([(o["kind"], o["status"], o.get("error_code"))
             for o in envelope["obligations"]
             if o["kind"] in ("refine_bind", "nat_bind")], envelope)


def _clause_binds(envelope: dict) -> list[tuple[str, str, str | None]]:
    """Only the records the CLAUSE BINDER raises.

    A handler program carries other narrowing records at the same effect —
    the `throw` op ARGUMENT against the declared payload, most of all — and a
    cell that counted every `refine_bind` would read one of those as the
    binder's.  The binder's node is the clause BODY, which has no renderable
    source text and so renders `<expr>`; every other record here names the
    expression it is about.  The same distinction
    `test_verifier_truth_consult_status.py` draws between the binder and the
    call in its clause body.
    """
    return sorted(
        (o["kind"], o["status"], o.get("error_code"))
        for o in envelope["obligations"]
        if o["kind"] in ("refine_bind", "nat_bind")
        and o["description"] == "<expr>"
    )


def _assert_partition(envelope: dict) -> None:
    obs = envelope["obligations"]
    summary = envelope["verification"]
    violated = sum(1 for o in obs if o["status"] == "violated")
    unguarded = sum(1 for o in obs if o["status"] == "tier3_unguarded")
    assert len(obs) == summary["total"] + violated + unguarded, (
        f"the documented accounting broke: {len(obs)} records vs "
        f"{summary['total']} + {violated} + {unguarded}"
    )


_POS = "type Pos = { @Int | @Int.0 > 0 };\n\n"

#: `@Nat` over `Exn<Int>` — #1445's own reproducer.
_EXN_NAT = """\
public fn f(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[Exn<Int>] {
    throw(@Nat) -> { nat_to_int(@Nat.0) }
  } in {
    throw(@Int.0)
  }
}
"""

#: Refined over `Exn<Int>` — #1448's own reproducer.
_EXN_REFINED = _POS + """\
public fn f(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[Exn<Int>] {
    throw(@Pos) -> { @Pos.0 }
  } in {
    throw(@Int.0)
  }
}
"""

#: Refined over `State<Int>` — the second spelling of #1448, in the other
#: effect family.
_STATE_REFINED = _POS + """\
public fn f(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Int>](@Int = 1) {
    get(@Unit) -> { resume(1) },
    put(@Pos) -> { resume(()) }
  } in {
    put(@Int.0);
    2
  }
}
"""

#: `@Nat` over `State<Int>` — the spelling that showed the #1445 disclosure
#: was coming from the clause BODY rather than the bind: same shape, and it
#: recorded nothing at all.
_STATE_NAT = """\
public fn f(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Int>](@Int = 1) {
    get(@Unit) -> { resume(1) },
    put(@Nat) -> { resume(()) }
  } in {
    put(@Int.0);
    2
  }
}
"""

_SHAPES = {
    "exn-nat": (_EXN_NAT, "nat_bind", _NAT_TRAP, "7"),
    "exn-refined": (_EXN_REFINED, "refine_bind", _REFINE_TRAP, "7"),
    "state-refined": (_STATE_REFINED, "refine_bind", _REFINE_TRAP, "2"),
    "state-nat": (_STATE_NAT, "nat_bind", _NAT_TRAP, "2"),
}


@pytest.mark.parametrize("shape", sorted(_SHAPES))
def test_the_binder_refuses_a_payload_its_declared_type_forbids(
    tmp_path: Path, shape: str,
) -> None:
    """The property, read from a RUN, in every spelling.

    `-7` violates both `@Nat`'s sign and `Pos`'s predicate, so no clamp,
    default or dropped guard reads the same as the trap.
    """
    source, _kind, trap, _safe = _SHAPES[shape]
    out = _run(tmp_path, source, "-7", f"{shape}_run.vera")
    assert trap in out, (
        f"the {shape} clause binder accepted `-7`, and the clause body then "
        f"reasoned from a type the value does not have:\n{out}"
    )


@pytest.mark.parametrize("shape", sorted(_SHAPES))
def test_a_payload_the_binder_admits_still_passes(
    tmp_path: Path, shape: str,
) -> None:
    """The over-reach control.

    A guard that refused everything would satisfy the cell above while
    breaking every valid program, so each shape is also run with a payload
    its binder does admit.
    """
    source, _kind, _trap, safe = _SHAPES[shape]
    out = _run(tmp_path, source, "7", f"{shape}_safe.vera")
    assert out.strip() == safe, out


@pytest.mark.parametrize("shape", sorted(_SHAPES))
def test_the_binder_is_on_the_record_as_guarded(
    tmp_path: Path, shape: str,
) -> None:
    """The classification, which must count the guard rather than disclose.

    `tier3` — a runtime check covers this — and never `tier3_unguarded`,
    which is what #1445's spelling reported while nothing checked it, nor
    silence, which is what the other three reported.
    """
    source, kind, _trap, _safe = _SHAPES[shape]
    binds, envelope = _binds(tmp_path, source, f"{shape}_obl.vera")
    assert any(k == kind and status == "tier3" for k, status, _ in binds), (
        f"the {shape} clause binder is not recorded as guarded: {binds}"
    )
    _assert_partition(envelope)


def test_the_refined_binder_records_an_obligation_at_all(
    tmp_path: Path,
) -> None:
    """#1448 as its own claim, separate from #1445's.

    The two issues are different defects and this is the one that
    distinguishes them: #1445's binder had a record and no guard, this one
    had no record.  A fix that only added the guard would leave this cell
    failing, and a fix that only added the obligation would leave the run
    cells failing — which is what the mutation battery checks.
    """
    binds, _ = _binds(tmp_path, _EXN_REFINED, "refined_present.vera")
    assert any(k == "refine_bind" for k, _s, _c in binds), (
        f"the refined clause binder raises no obligation at all, so there "
        f"is not even a disclosure to read: {binds}"
    )


def test_the_site_table_moves_both_halves_together(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """The coupling the shared table exists for, exercised in-process.

    The classification and the emitter both read
    `vera.narrowing.REFINED_BIND_GUARDED_SITES`, so a site cannot be
    reported as guarded without being guarded, or guarded without being
    counted.  That is a claim about the WIRING, and the only way to test it
    is to move the table and watch both answers move — a cell that asserts
    the current status and the current WAT separately would pass just as
    well if each side had its own hard-coded copy, which is the arrangement
    this table replaced.

    Run in-process rather than through the CLI: the other cells here shell
    out, and a monkeypatched frozenset cannot reach a subprocess.
    """
    from vera import narrowing
    from vera.checker import typecheck_with_artifacts
    from vera.codegen import compile as codegen_compile
    from vera.parser import parse_to_ast
    from vera.verifier import verify

    def status_and_wat() -> tuple[list[str], str]:
        program = parse_to_ast(_EXN_REFINED)
        diags, arts = typecheck_with_artifacts(program, _EXN_REFINED)
        assert not [d for d in diags if d.severity == "error"], diags
        result = verify(
            program, _EXN_REFINED,
            expr_types=arts.expr_semantic_types,
            expr_target_types=arts.expr_target_types,
        )
        statuses = [o.status for o in result.obligations
                    if o.kind == "refine_bind"]
        wat = codegen_compile(
            program, source=_EXN_REFINED,
            expr_semantic_types=arts.expr_semantic_types,
            expr_target_types=arts.expr_target_types,
        ).wat
        return statuses, wat

    on_statuses, on_wat = status_and_wat()
    assert "tier3" in on_statuses, on_statuses
    assert wat_calls(on_wat, "vera.contract_fail")

    monkeypatch.setattr(
        narrowing, "REFINED_BIND_GUARDED_SITES",
        narrowing.REFINED_BIND_GUARDED_SITES - {"handler clause binder"},
    )
    off_statuses, off_wat = status_and_wat()
    assert "tier3_unguarded" in off_statuses, (
        f"the classification still claims a guard after the site left the "
        f"table, so it is not reading the table: {off_statuses}"
    )
    assert not wat_calls(off_wat, "vera.contract_fail"), (
        "the emitter still plants the guard after the site left the table, "
        "so it is not reading the table either"
    )


# =====================================================================
# The PAYLOAD axis: what the binder is narrower THAN
# =====================================================================
#
# Every fixture above declares an UNREFINED payload (`Exn<Int>`,
# `State<Int>`), so none of them can reach the question the two components
# were answering differently: what happens when the payload is refined TOO.
# The reviewer of PR #1465 found both failure modes there, and this is the
# axis that holds them.

_TWO_FAMILIES = """type Pos = { @Int | @Int.0 > 0 };
type Neg = { @Int | @Int.0 < 0 };

public fn f(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[Exn<Pos>] {
    throw(@Neg) -> { @Neg.0 }
  } in {
    throw(@Int.0)
  }
}
"""

_STATE_TWO_FAMILIES = """type Pos = { @Int | @Int.0 > 0 };
type Neg = { @Int | @Int.0 < 0 };

public fn f(@Int -> @Int)
  requires(@Int.0 > 0)
  ensures(true)
  effects(pure)
{
  handle[State<Pos>](@Pos = 1) {
    get(@Unit) -> { resume(1) },
    put(@Neg) -> { resume(()) }
  } in {
    put(@Int.0);
    2
  }
}
"""

_CHAIN_OVER_REFINED = """type Pos = { @Int | @Int.0 > 0 };
type Big = { @Pos | @Pos.0 > 100 };

public fn f(@Int -> @Int)
  requires(@Int.0 > 0)
  ensures(true)
  effects(pure)
{
  handle[Exn<Pos>] {
    throw(@Big) -> { @Big.0 }
  } in {
    throw(@Int.0)
  }
}
"""

_SAME_FAMILY = """type Pos = { @Int | @Int.0 > 0 };

public fn f(@Int -> @Int)
  requires(@Int.0 > 0)
  ensures(true)
  effects(pure)
{
  handle[Exn<Pos>] {
    throw(@Pos) -> { @Pos.0 }
  } in {
    throw(@Int.0)
  }
}
"""


class TestThePayloadMayBeRefinedToo:
    """Four payload shapes, and what each must do.

    The two components asked the narrowing question two different ways —
    the verifier "is the declared type refined and the payload's not?", the
    emitter "do the refinement-preserving family names differ?" — and they
    disagree on every program where both are refined.  Both failure modes
    the class claim rules out were reachable through this axis:

    * `Exn<Pos>` bound at `@Neg`: the emitter guarded it (different family
      names) and the verifier recorded nothing (the payload IS refined).  A
      guard the stream does not count.
    * `Exn<Pos>` bound at `Big = { @Pos | … }`: the family names differ, so
      the emitter guarded — but the base is itself a refinement, so the
      §2.6.5 lowering declines and nothing was emitted after all, and the
      verifier still recorded nothing.  Silent AND unguarded: #1448 again,
      at the chain spelling, on the one pattern-bind position where `let`
      and `match` both obligate it.

    Both sides now call `narrowing.narrows_into_refinement` over the
    CONJOINED chains, so `Exn<Pos>` bound at `@Pos` — the same chain — is
    exempt at both, and everything else is obligated at both.
    """

    def test_a_disjoint_family_is_obligated(self, tmp_path: Path) -> None:
        _binds_all, envelope = _binds(tmp_path, _TWO_FAMILIES, "twofam.vera")
        binds = _clause_binds(envelope)
        assert any(k == "refine_bind" and s == "tier3" for k, s, _ in binds), (
            f"the binder narrows `Pos` to `Neg`, which shares no predicate "
            f"with it, and the emitter guards it: {binds}"
        )
        _assert_partition(envelope)

    def test_a_disjoint_family_refuses_a_payload_it_forbids(
        self, tmp_path: Path,
    ) -> None:
        """`5` satisfies `Pos` and violates `Neg`, so the guard must fire.

        At 8eca11c0 this program ran and returned `5`; at 26af842f it
        trapped with nothing on the record.  Both halves are pinned, so
        neither can come back alone.
        """
        out = _run(tmp_path, _TWO_FAMILIES, "5", "twofam_run.vera")
        assert _REFINE_TRAP in out, out

    def test_the_state_side_twin(self, tmp_path: Path) -> None:
        _binds_all, envelope = _binds(
            tmp_path, _STATE_TWO_FAMILIES, "st_twofam.vera")
        binds = _clause_binds(envelope)
        assert any(k == "refine_bind" and s == "tier3" for k, s, _ in binds), (
            f"the `put` clause binder narrows `Pos` to `Neg`: {binds}"
        )
        out = _run(tmp_path, _STATE_TWO_FAMILIES, "5", "st_twofam_run.vera")
        assert _REFINE_TRAP in out, out

    def test_a_chain_over_the_payload_is_at_least_on_the_record(
        self, tmp_path: Path,
    ) -> None:
        """`Big = { @Pos | … }` over an `Exn<Pos>` payload.

        Whether it can be GUARDED is the pre-existing E618 question — a
        refinement whose base is itself a refinement is one the §2.6.5
        lowering will not compose — so `tier3_unguarded` is the honest
        answer and the cell asks for a record, not for a guard.  What it may
        not be is silent, which is what it was.
        """
        _binds_all, envelope = _binds(
            tmp_path, _CHAIN_OVER_REFINED, "chain.vera")
        binds = _clause_binds(envelope)
        assert any(k == "refine_bind" for k, _s, _c in binds), (
            f"the chain adds `> 100` to the payload's `> 0` and nothing "
            f"records it: {binds}"
        )
        _assert_partition(envelope)

    def test_the_same_chain_is_exempt_at_both_sides(
        self, tmp_path: Path,
    ) -> None:
        """`Exn<Pos>` bound at `@Pos` narrows nothing.

        The over-reach control for the two cells above, and the one that
        keeps `ch07_exn_payload_guard.vera`'s emitted WAT where it was: no
        record, and a payload the handler admits still runs.
        """
        all_binds, envelope = _binds(tmp_path, _SAME_FAMILY, "same.vera")
        # The premise: this fixture DOES record a narrowing — the `throw`
        # argument against the declared payload — so the negative below is
        # about the clause binder rather than about a program that records
        # nothing at all (CodeRabbit on PR #1465).
        assert any(k == "refine_bind" for k, _s, _c in all_binds), (
            f"the fixture emitted no narrowing record at all, so the "
            f"exemption is untested: {all_binds}"
        )
        binds = _clause_binds(envelope)
        assert not [b for b in binds if b[0] == "refine_bind"], (
            f"a binder at the payload's own type is not a narrowing: {binds}"
        )
        out = _run(tmp_path, _SAME_FAMILY, "5", "same_run.vera")
        assert out.strip() == "5", out
