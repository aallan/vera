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


# ---------------------------------------------------------------------------
# The chain has to reach every consumer of the refinement, not just the
# binding-site translation (R-1431 review of PR #1453, F1-F3)
# ---------------------------------------------------------------------------

_F1_CALL_ARG = """\
type Pos = { @Int | @Int.0 > 0 };
type Small = { @Pos | @Pos.0 < 10 };

public fn mk(@Int -> @Small)
  requires(@Int.0 > 0 && @Int.0 < 10)
  ensures(true)
  effects(pure)
{
  @Int.0
}

public fn needpos(@Pos -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Pos.0
}

public fn caller(@Int -> @Int)
  requires(@Int.0 > 0 && @Int.0 < 10)
  ensures(true)
  effects(pure)
{
  needpos(mk(@Int.0))
}
"""

_F1_POSTCONDITION = """\
type Pos = { @Int | @Int.0 > 0 };
type Small = { @Pos | @Pos.0 < 10 };

public fn mk(@Int -> @Small)
  requires(@Int.0 > 0 && @Int.0 < 10)
  ensures(true)
  effects(pure)
{
  @Int.0
}

public fn caller(@Unit -> @Int)
  requires(true)
  ensures(@Int.result > 0 && @Int.result < 10)
  effects(pure)
{
  mk(5)
}
"""


@pytest.mark.parametrize(
    "source,discriminates",
    [
        pytest.param(
            _F1_CALL_ARG,
            "the INNER level (`> 0`), which an outermost-only reading misses",
            id="call-argument",
        ),
        pytest.param(
            _F1_POSTCONDITION,
            "BOTH levels, so neither level alone carries the postcondition",
            id="postcondition",
        ),
    ],
)
def test_1434_a_chain_return_type_is_assumed_by_its_caller(
    tmp_path: Path, source: str, discriminates: str,
) -> None:
    """A refined return type is an implicit postcondition — for a CHAIN too.

    `SmtContext` assumed the refinement of a call's result only when the type
    was one level over a modelled primitive.  A chain's base is another
    `RefinedType`, so the gate was false and the fact was dropped WHOLE: the
    caller got a fresh unconstrained variable and a program that holds was
    refuted (E505 on the argument, E500 on the postcondition), while the same
    program written flat verified.  Dropped, not weakened — the counterexample
    named the result as 0, which satisfies neither level.

    Each shape needs {discriminates}, so a fix that reads one level cannot
    pass both.
    """
    result = _verify(_write(tmp_path, source))
    assert result["ok"] is True, (
        "a valid program over a refinement CHAIN was refuted — the refined "
        f"return fact did not reach the caller: {result['diagnostics']}"
    )
    assert all(
        o["status"] in ("verified", "tier3") for o in result["obligations"]
    ), result["obligations"]


def test_1434_the_violation_message_names_every_level(tmp_path: Path) -> None:
    """The refutation has to say WHICH predicate it refuted.

    The renderer read one level, so `50` narrowed into `{ @NZ | @NZ.0 < 10 }`
    over `{ @Nat | @Nat.0 > 0 }` was reported against `@NZ.0 < 10` alone, and
    the `@Nat` base intrinsic was dropped as well because the `>= 0` prefix
    tests the OUTERMOST base — which for a chain is a `RefinedType`, never
    `NAT`.  A reader told only the outer predicate cannot see what membership
    actually requires, and for `{ @NZ | true }` the message would name `true`.
    """
    source = (
        "type NZ = { @Nat | @Nat.0 > 0 };\n"
        "type NSmall = { @NZ | @NZ.0 < 10 };\n"
        "\n"
        "public fn f(@Unit -> @NSmall)\n"
        "  requires(true)\n"
        "  ensures(true)\n"
        "  effects(pure)\n"
        "{\n"
        "  50\n"
        "}\n"
    )
    result = _verify(_write(tmp_path, source))
    assert _obl(result, "refine_bind") == [("violated", "E505")], (
        result["obligations"]
    )
    e505 = [d for d in result["diagnostics"] if d.get("error_code") == "E505"]
    text = "\n".join(d.get("description", "") for d in e505)
    for fragment in ("@Nat.0 >= 0", "@Nat.0 > 0", "@NZ.0 < 10"):
        assert fragment in text, (
            f"the E505 message does not name `{fragment}`, so it does not "
            f"state the membership it refuted:\n{text}"
        )
    # The `fix` field renders the same conjunction into the `requires(...)` it
    # suggests, so a partial render sends the reader to write a precondition
    # that does not discharge the obligation.  Asserted separately because it
    # is a separate string: the description could be right while the repair
    # advice stayed one-level (CodeRabbit review of PR #1453).
    fix_text = "\n".join(d.get("fix", "") for d in e505)
    for fragment in ("@Nat.0 >= 0", "@Nat.0 > 0", "@NZ.0 < 10"):
        assert fragment in fix_text, (
            f"the E505 `fix` does not name `{fragment}`, so the suggested "
            f"`requires(...)` would not discharge the obligation:\n{fix_text}"
        )


def test_1434_a_concrete_value_is_decided_over_a_chain(tmp_path: Path) -> None:
    """Spec 2.6.4: a CONCRETE narrowing is decided whatever the base.

    `_concrete_refined_verdict` exists because substituting a literal leaves a
    closed formula that folds — no base modelling required, which is why an
    unmodelled `@Byte` is still DECIDED there.  It read one level, so a chain
    fell straight back to the undecided disclosure the modelling gate
    produces, and the same literal decided flat went undecided nested.

    `200` is the discrimination: it satisfies the inner `> 0` and violates the
    outer `< 10`, so an innermost-only fold answers True and a correct one
    answers False.  The flat spelling below is the oracle — same literal, same
    predicate, and it is the verdict the chain must reproduce.
    """
    chain = (
        "type B1 = { @Byte | @Byte.0 > 0 };\n"
        "type BSmall = { @B1 | @B1.0 < 10 };\n"
        "\n"
        "public fn f(@Unit -> @Int)\n"
        "  requires(true)\n"
        "  ensures(true)\n"
        "  effects(pure)\n"
        "{\n"
        "  let @BSmall = 200;\n"
        "  0\n"
        "}\n"
    )
    flat = (
        "type BFlat = { @Byte | @Byte.0 < 10 };\n"
        "\n"
        "public fn f(@Unit -> @Int)\n"
        "  requires(true)\n"
        "  ensures(true)\n"
        "  effects(pure)\n"
        "{\n"
        "  let @BFlat = 200;\n"
        "  0\n"
        "}\n"
    )
    flat_result = _verify(_write(tmp_path / "flat", flat))
    assert _obl(flat_result, "refine_bind") == [("violated", "E505")], (
        "the ORACLE moved: a concrete violation over a flat unmodelled base "
        f"is no longer decided: {flat_result['obligations']}"
    )
    chain_result = _verify(_write(tmp_path / "chain", chain))
    assert _obl(chain_result, "refine_bind") == _obl(flat_result, "refine_bind"), (
        "a concrete value decided against a flat refinement went undecided "
        f"against the chain: {chain_result['obligations']}"
    )
    text = "\n".join(
        d.get("description", "") for d in chain_result["diagnostics"]
        if d.get("error_code") == "E505"
    )
    assert "the value is 200" in text, text


def test_1434_a_chain_result_is_declared_at_its_primitive_sort(
    tmp_path: Path,
) -> None:
    """The fresh call result needs the sort of the chain's PRIMITIVE base.

    Separate mechanism from the assumption above, and separately broken by the
    same one-level reading: the declaration stripped one refinement, found
    another `RefinedType` rather than `@Nat`, and fell through to
    `declare_int` — so the result variable never carried `@Nat`'s `>= 0`.

    The predicates here are `true`, which is the discrimination: no predicate
    can supply the missing fact, so this cell answers about the DECLARATION
    and nothing else.  Mutating the strip back to one level refutes it with
    the result witnessed as `-1` — a negative inhabitant of a `@Nat`-based
    type.
    """
    source = (
        "type A = { @Nat | true };\n"
        "type B = { @A | true };\n"
        "\n"
        "public fn mk(@Nat -> @B)\n"
        "  requires(true)\n"
        "  ensures(true)\n"
        "  effects(pure)\n"
        "{\n"
        "  @Nat.0\n"
        "}\n"
        "\n"
        "public fn caller(@Unit -> @Int)\n"
        "  requires(true)\n"
        "  ensures(@Int.result >= 0)\n"
        "  effects(pure)\n"
        "{\n"
        "  mk(7)\n"
        "}\n"
    )
    result = _verify(_write(tmp_path, source))
    assert result["ok"] is True, (
        "the result of a call returning a chain over @Nat was declared "
        f"without the base's `>= 0`: {result['diagnostics']}"
    )


def test_1434_the_tier3_reason_names_the_primitive_base(tmp_path: Path) -> None:
    """A Tier-3 chain is diagnosed by what it BOTTOMS OUT in.

    The E506 rationale distinguishes two causes that call for different
    repairs: an unmodelled base (nothing was ever asked) versus a predicate
    outside the fragment.  Reading one level named the intermediate alias as
    the unmodelled base — which is false twice: that alias is not what the
    modelling gate consults, and for a chain over a MODELLED base it would
    blame the base for a Tier 3 the fragment caused.

    The value here is symbolic, so the concrete fold declines and the
    obligation really is Tier 3; `@Byte` is genuinely unmodelled, so the
    sentence must name `Byte` and not the `B1` standing between them.
    """
    source = (
        "type B1 = { @Byte | @Byte.0 > 0 };\n"
        "type BSmall = { @B1 | @B1.0 < 10 };\n"
        "\n"
        "public fn f(@Byte -> @Int)\n"
        "  requires(true)\n"
        "  ensures(true)\n"
        "  effects(pure)\n"
        "{\n"
        "  let @BSmall = @Byte.0;\n"
        "  0\n"
        "}\n"
    )
    result = _verify(_write(tmp_path, source))
    rationales = "\n".join(
        d.get("rationale", "")
        for d in result["diagnostics"] + result.get("warnings", [])
        if d.get("error_code") == "E506"
    )
    assert "does not model `Byte`" in rationales, (
        f"the E506 rationale does not name the primitive base:\n{rationales}"
    )
    assert "`B1`" not in rationales, (
        "the E506 rationale blames the intermediate refinement rather than "
        f"the base the modelling gate consults:\n{rationales}"
    )
