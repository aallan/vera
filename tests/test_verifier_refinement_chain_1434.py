"""A refinement over a refinement means the conjunction of its predicates (#1434).

`type Small = { @Pos | @Pos.0 < 10 }` over `type Pos = { @Int | @Int.0 > 0 }`
means `0 < x < 10`.  The verifier read one level: `_refined_parts` answered
`(Pos, @Pos.0 < 10)`, `_base_slot_name` declined `Pos` because it is not a
primitive, and `_translate_refined_predicate` returned `None` — so the type was
unmodelled and every obligation over it fell to Tier 3, *or worse* was refuted
outright because the value carried no constraint at all.

`_refined_chain` now walks to the primitive base collecting every predicate,
and each is translated in ITS OWN `SlotEnv` — the levels bind different names
(`{ @Int | @Int.0 > 0 }` binds `@Int`, `{ @Pos | @Pos.0 < 10 }` binds `@Pos`)
over the same value — with `@Nat`'s intrinsic `>= 0` contributed once for the
whole chain.  A level that will not translate still returns `None`: a
conjunction is only as strong as its weakest conjunct, and dropping one would
ASSERT a membership the run cannot establish.

The values below are chosen so that no single-predicate implementation can
pass: one satisfies the inner predicate alone, one the outer alone.  An
implementation reading either level in isolation verifies one of them, and
both are refutable.

SCOPE.  This conjoins predicates; it does not change the SORT rule.
`Option<chain>` still keys `?` (PR #1431's option C), because making the sort
succeed while an arm's facts do not reach a primitive operation reports a
false E526 — measured, and recorded in
`test_verifier_refined_sort_derivation.py`.  That combination belongs to
#1415, whose arm-fact flow is the missing precondition.
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


def _write(tmp_path: Path, source: str, name: str = "p.vera") -> Path:
    tmp_path.mkdir(parents=True, exist_ok=True)
    p = tmp_path / name
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
            f"{proc.stderr[-600:]}"
        ) from None
    internal = [
        d for d in result.get("diagnostics", [])
        if d.get("error_code") == "E699"
    ]
    assert not internal, f"{path.name}: internal error — {internal[0]}"
    return result


def _obl(result: dict, kind: str) -> list[tuple[str, str | None]]:
    return [
        (o["status"], o.get("error_code")) for o in result["obligations"]
        if o["kind"] == kind
    ]


_CHAIN = """\
type Pos = {{ @Int | @Int.0 > 0 }};
type Small = {{ @Pos | @Pos.0 < 10 }};

public fn f(@Unit -> @Small)
  requires(true)
  ensures(true)
  effects(pure)
{{
  {value}
}}
"""


# ---------------------------------------------------------------------------
# Values no single-predicate reading can get right
# ---------------------------------------------------------------------------

@pytest.mark.parametrize(
    "value,satisfies",
    [
        pytest.param("50", "the INNER predicate only (> 0, but not < 10)",
                     id="inner-only"),
        pytest.param("0 - 5", "the OUTER predicate only (< 10, but not > 0)",
                     id="outer-only"),
    ],
)
def test_1434_a_value_satisfying_one_level_is_refuted(
    tmp_path: Path, value: str, satisfies: str,
) -> None:
    """Membership is the CONJUNCTION, so one level is not enough.

    These two values are the discrimination.  `50` satisfies `> 0`, so an
    implementation that read only the inner predicate would verify it; `-5`
    satisfies `< 10`, so one reading only the outer would verify that.  Both
    are refutable against the chain, and no single-level reading refutes both.

    Before #1434 both were `tier3_unguarded`/E506 — the honest answer for a
    type nothing modelled, and the reason a wrong value could not be caught.
    """
    result = _verify(_write(tmp_path, _CHAIN.format(value=value)))
    assert _obl(result, "refine_bind") == [("violated", "E505")], (
        f"a value satisfying {satisfies} was not refuted against the chain: "
        f"{result['obligations']}"
    )


def test_1434_a_value_satisfying_both_levels_verifies(tmp_path: Path) -> None:
    """... and the conjunction is not vacuously false either.

    The over-rejection control: `5` satisfies both predicates and must reach
    Tier 1.  Without it, "refute everything" would pass the two cells above.
    """
    result = _verify(_write(tmp_path, _CHAIN.format(value="5")))
    assert result["ok"] is True, result["diagnostics"]
    assert _obl(result, "refine_bind") == [("verified", None)], (
        result["obligations"]
    )


# ---------------------------------------------------------------------------
# The program the guard-completeness cells used to pin, in its new truth
# ---------------------------------------------------------------------------

#: This is the program `test_guard_completeness.py`'s
#: `_Q1_REFINED_OVER_REFINED_LET` used to carry.  Before #1434 it was
#: `tier3_unguarded`/E506 — the chain was unmodelled — and those cells pinned
#: the WORDING of that warning.  #1434 decides it instead, so the fixture there
#: moved to a `@Byte` chain (a base `_base_slot_name` still declines, per spec
#: §2.6.4 cause 2) and the program itself is pinned here, in its new truth.
_LET_FROM_GUARD_COMPLETENESS = """\
type Pos = {{ @Int | @Int.0 > 0 }};
type Tiny = {{ @Pos | @Pos.0 < 10 }};

public fn mk(@Int -> @Pos)
  requires(@Int.0 > 0)
  ensures({mk_ensures})
  effects(pure)
{{
  @Int.0
}}

public fn f(@Int -> @Int)
  requires({req})
  ensures(true)
  effects(pure)
{{
  let @Tiny = mk(@Int.0);
  @Tiny.0
}}
"""


def test_1434_the_relocated_let_program_is_now_refuted(
    tmp_path: Path,
) -> None:
    """`mk` returns a `Pos`, which carries no upper bound — so `Tiny` fails.

    The refutation is the point: this program was always wrong and the old
    E506 was only the honest silence of an unmodelled type.  `requires(@Int.0
    > 0)` gives `> 0`; nothing gives `< 10`, so a counterexample exists.
    """
    result = _verify(_write(
        tmp_path,
        _LET_FROM_GUARD_COMPLETENESS.format(
            req="@Int.0 > 0", mk_ensures="true")))
    assert result["ok"] is False, result["obligations"]
    assert ("violated", "E505") in _obl(result, "refine_bind"), (
        result["obligations"]
    )


def test_1434_the_relocated_let_program_verifies_when_bounded(
    tmp_path: Path,
) -> None:
    """... and verifies once the caller's precondition supplies both bounds.

    Two things have to change together, which is itself the lesson: bounding
    the CALLER's argument is not enough, because `mk`'s `ensures(true)` says
    nothing linking its result to its input — so the returned `Pos` is still
    only `> 0`.  With `ensures(@Pos.result == @Int.0)` the bound travels, and
    the bind reaches Tier 1.  That makes the cell above a statement about the
    VALUE rather than about the shape.
    """
    result = _verify(_write(
        tmp_path,
        _LET_FROM_GUARD_COMPLETENESS.format(
            req="@Int.0 > 0 && @Int.0 < 10",
            mk_ensures="@Pos.result == @Int.0")))
    assert result["ok"] is True, result["diagnostics"]
    # EVERY bind, not "one of them": `mk`'s own return bind verifies on the
    # base too (a plain `@Int` into a single `@Pos`), so a membership test
    # would pass without the chain being decided at all.
    binds = _obl(result, "refine_bind")
    assert binds and all(b == ("verified", None) for b in binds), (
        result["obligations"]
    )


# ---------------------------------------------------------------------------
# A false REJECTION of valid code, fixed — and what backs the new Tier 1
# ---------------------------------------------------------------------------

_ENSURES_FROM_PARAMETER = """\
type Pos = { @Int | @Int.0 > 0 };
type Small = { @Pos | @Pos.0 < 10 };

public fn main(@Small -> @Int)
  requires(true)
  ensures(@Int.result > 0 && @Int.result < 10)
  effects(pure)
{
  @Small.0
}
"""


def test_1434_a_postcondition_the_chain_proves_is_no_longer_refuted(
    tmp_path: Path,
) -> None:
    """The chain is what makes this postcondition true, and it now says so.

    A `@Small` parameter is assumed to satisfy its predicate in the body
    (spec §2.6.4), sound because every call site discharges it.  Reading one
    level left the value unconstrained, so `@Int.result > 0 && < 10` was
    reported **`violated`** on `release/v0.2.0` — a false rejection of valid
    code, the #854/#884 class.  It is now `verified`.
    """
    result = _verify(_write(tmp_path, _ENSURES_FROM_PARAMETER))
    assert result["ok"] is True, result["diagnostics"]
    assert _obl(result, "ensures") == [("verified", None)], (
        result["obligations"]
    )


def test_1434_no_runtime_witness_is_reachable_for_that_tier_1(
    tmp_path: Path,
) -> None:
    """The `vera run` leg, and its honest result: the program will not run.

    A Tier-1 proof resting on a parameter's refinement is only as good as the
    boundary that enforces it.  Codegen declines to compose a nested
    refinement's membership guard — "Composing nested refinement membership
    predicates is unsupported" — and REFUSES the program rather than emitting
    a weaker guard.  That refusal predates this change (measured identical on
    `release/v0.2.0`), so no runtime witness of a false Tier 1 is
    constructible here: the failure mode is a loud compile-time refusal, not
    a bad value flowing past a missing check.

    Tracked as #1450, which is what this pin is waiting for: E618 is
    registered in `vera/errors.py` but sits in no limitation table, so the
    toolchain refuses a shape the verifier proves and nothing documents it.
    Closing #1450 by composing the boundary guard from the same conjunction
    `_refined_chain` builds turns this cell into a real `ensures` + `vera run`
    differential — `-5` and `50` trapping at the guard, `5` returning.

    Asserted rather than left as a note, so that if codegen ever starts
    compiling this shape, this cell fails and someone checks that the guard it
    emits actually enforces the whole chain.
    """
    path = _write(tmp_path, _ENSURES_FROM_PARAMETER)
    proc = _cli("run", str(path), "--fn", "main", "--", "5")
    assert proc.returncode != 0, (
        f"the program now compiles — verify the emitted boundary guard "
        f"enforces BOTH predicates:\n{proc.stdout[-400:]}"
    )
    combined = proc.stdout + proc.stderr
    assert "nested refinement" in combined, combined[-400:]


# ---------------------------------------------------------------------------
# The conservative leg: a chain the verifier still declines
# ---------------------------------------------------------------------------

_BYTE_CHAIN = """\
type SmallByte = { @Byte | @Byte.0 < 100 };
type TinyByte = { @SmallByte | @SmallByte.0 < 10 };

public fn f(@SmallByte -> @Byte)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @TinyByte = @SmallByte.0;
  @TinyByte.0
}
"""


def test_1434_a_chain_over_an_unmodelled_base_is_still_tier_3(
    tmp_path: Path,
) -> None:
    """Conjoining does not widen which BASES are modelled.

    `_base_slot_name` declines `@Byte` — its `0..255` is never asserted, so a
    symbolic value would translate without its base semantics (spec §2.6.4,
    cause 2).  A chain over it therefore still reaches no verdict, and must
    stay the honest Tier 3 rather than becoming a confident answer about a
    base nothing constrains.  This is the fixture
    `test_guard_completeness.py` now uses for exactly that reason.
    """
    result = _verify(_write(tmp_path, _BYTE_CHAIN))
    assert result["ok"] is True, result["diagnostics"]
    assert ("tier3_unguarded", "E506") in _obl(result, "refine_bind"), (
        result["obligations"]
    )


def test_1434_an_untranslatable_level_declines_the_whole_chain() -> None:
    """One level outside the fragment makes the whole membership undecided.

    A conjunction is only as strong as its weakest conjunct.  Keeping the
    levels that translate and skipping the rest would ASSERT a membership the
    run cannot establish — and with EVERY level skipped the conjunction of
    nothing is `True`, so the value would be waved through entirely.

    A PIN, not a mutation-killing cell, recorded as such.  I could not
    make it fail under the obvious mutation (keep the translatable levels
    and `continue` past the rest).  A predicate that genuinely fails to
    translate over a MODELLED base is hard to write — a `@Byte` chain
    declines earlier, at `_base_slot_name`, and never reaches this loop —
    and injecting a `None` into `translate_expr` lands on sub-expressions
    rather than whole levels, so it does not isolate the decision either.
    It earns its place by pinning the contract the conjunction leans on,
    not by discriminating.
    """
    from vera import ast
    from vera.smt import SmtContext
    from vera.types import INT, RefinedType
    from vera.verifier import ContractVerifier

    import z3

    inner = ast.BinaryExpr(
        op=ast.BinOp.GT,
        left=ast.SlotRef(type_name="Int", type_args=None, index=0),
        right=ast.IntLit(value=0),
    )
    outer = ast.BinaryExpr(
        op=ast.BinOp.LT,
        left=ast.SlotRef(type_name="Int", type_args=None, index=0),
        right=ast.IntLit(value=10),
    )
    chain = RefinedType(
        base=RefinedType(base=INT, predicate=inner), predicate=outer)

    smt = SmtContext()
    value = z3.Int("v")
    # Sanity: both levels translate, so the chain is decidable as written.
    assert ContractVerifier._translate_refined_predicate(
        smt, chain, value) is not None

    original = smt.translate_expr
    calls = {"n": 0}

    def one_level_fails(expr, env):  # type: ignore[no-untyped-def]
        calls["n"] += 1
        if calls["n"] == 2:      # the second level of the chain
            return None
        return original(expr, env)

    smt.translate_expr = one_level_fails  # type: ignore[method-assign]
    got = ContractVerifier._translate_refined_predicate(smt, chain, value)
    assert calls["n"] >= 2, (
        f"the walk stopped before the second level, so this cell measures "
        f"nothing ({calls['n']} translation(s))"
    )
    assert got is None, (
        f"an untranslatable level was dropped and the rest conjoined: {got}"
    )
