"""Guard completeness — the sites the verifier OBLIGATES and codegen must
runtime-check (#765, #757, #1036, #754, #1222).

DESIGN.md's "contracts as truth" makes the obligation stream a claim about the
compiled artifact, not a report about the prover: a Tier-3 obligation says a
runtime check covers this, so the check has to exist.  Five sites were
obligated and unguarded, each for its own reason, and each closed here at the
place that already knows the obligation exists rather than at the symptom:

* #765 — a refinement narrowed by a PATTERN BIND (`let`, match bind, tuple
  destructure, constructor sub-pattern at any depth) had no guard at all.
  `@Nat` is a refinement whose predicate codegen writes by hand, so the sign
  guard covered one member of the family and the rest went unchecked.
* #757 — a `@Nat` field reached through a GENERIC instantiation
  (`Wrap(@Int.0)` building a `Box<Nat>`) carried no per-field metadata, so
  the construction guard was skipped.
* #1036 — a refined base with a NON-PLAIN type argument (`Array<{refined}>`)
  could not spell its binder slot, so no boundary guard fired.
* #754 — an effect operation's argument reached no per-formal type, so a
  narrowing into a concrete `@Nat` / refined formal was unguarded.
* #1222 — the `decreases` measure is evaluated in machine i64 while the
  prover reasons over unbounded integers.

Every cell here is the issue's own reproducer, run on a value chosen so that
no fallback can coincide with the right answer: a NEGATIVE `Int` into every
`@Nat` slot (a clamp to zero would read as success), and a refinement
violation a clamp cannot repair.  Each asserts the TRAP or the guard's own
diagnostic, never a length or an exit code.
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


def _write(tmp_path: Path, source: str, name: str = "p.vera") -> Path:
    p = tmp_path / name
    p.write_text(source, encoding="utf-8")
    return p


def _run(tmp_path: Path, source: str, *args: str, name: str = "p.vera") -> str:
    """`vera run` on *source*, returning stdout+stderr.

    Both streams, because the two outcomes a cell distinguishes live on
    different ones: a value on stdout, a trap message on stderr.
    """
    proc = _cli("run", str(_write(tmp_path, source, name)), *args)
    return proc.stdout + proc.stderr


def _obligations(tmp_path: Path, source: str,
                 name: str = "p.vera") -> tuple[list[dict], dict]:
    proc = _cli("verify", "--json", str(_write(tmp_path, source, name)))
    try:
        envelope = json.loads(proc.stdout)
    except json.JSONDecodeError:
        raise AssertionError(
            f"verify emitted no envelope (exit {proc.returncode})\n"
            f"{proc.stdout[:400]}\n{proc.stderr[-600:]}"
        ) from None
    return envelope["obligations"], envelope


def _assert_partition(envelope: dict) -> None:
    """`len(obligations) == total + violated + tier3_unguarded`.

    The documented accounting between the array and the summary.  Every cell
    that changes a status checks it, because a status flip that forgets which
    bucket it left silently breaks the partition and nothing else notices.
    """
    obs = envelope["obligations"]
    violated = sum(1 for o in obs if o["status"] == "violated")
    unguarded = sum(1 for o in obs if o["status"] == "tier3_unguarded")
    total = envelope["verification"]["total"]
    assert len(obs) == total + violated + unguarded, (
        f"partition broken: {len(obs)} obligations, total={total}, "
        f"violated={violated}, tier3_unguarded={unguarded} — "
        f"{[(o['kind'], o['status']) for o in obs]}"
    )


# ===========================================================================
# #765 — a refinement narrowed by a pattern bind
# ===========================================================================

# The issue's shape: `Some(Some(@PosInt))` on a doubly-wrapped payload, with
# the refinement at the INNER bind, which no direct-bind guard can reach.
_765_NESTED = """\
type Pos = { @Int | @Int.0 > 0 };

private data Box {
  MkBox(Int)
}

private data Wrap {
  MkWrap(Box)
}

public fn f(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match MkWrap(MkBox(@Int.0)) {
    MkWrap(MkBox(@Pos)) -> @Pos.0
  }
}
"""

_765_DIRECT = """\
type Pos = { @Int | @Int.0 > 0 };

private data Box {
  MkBox(Int)
}

public fn f(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match MkBox(@Int.0) {
    MkBox(@Pos) -> @Pos.0
  }
}
"""

_765_MATCH_BIND = """\
type Pos = { @Int | @Int.0 > 0 };

public fn f(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match @Int.0 {
    @Pos -> @Pos.0
  }
}
"""

_765_DESTRUCTURE = """\
type Pos = { @Int | @Int.0 > 0 };

public fn f(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let Tuple<@Pos, @Int> = Tuple(@Int.0, 1);
  @Pos.0
}
"""

_765_LET = """\
type Pos = { @Int | @Int.0 > 0 };

public fn f(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Pos = @Int.0;
  @Pos.0
}
"""

# Inside a lifted CLOSURE, whose context carried no guard emitter at all
# until #765 installed one.
_765_IN_CLOSURE = """\
type Pos = { @Int | @Int.0 > 0 };

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  array_length(array_map(array_range(0 - 2, 0),
    fn(@Int -> @Int) effects(pure) { let @Pos = @Int.0; @Pos.0 }))
}
"""

_765_SHAPES = {
    "nested_sub_pattern": _765_NESTED,
    "direct_sub_pattern": _765_DIRECT,
    "match_bind": _765_MATCH_BIND,
    "tuple_destructure": _765_DESTRUCTURE,
    "let_binding": _765_LET,
}

# A pair-typed (ptr, len) refinement, guarded over the pointer half — the
# representation the scalar cells above cannot reach.
_765_PAIR = """\
type NonEmptyArray = { @Array<Int> | array_length(@Array<Int>.0) > 0 };

private fn mk(@Unit -> @Array<Int>)
  requires(true)
  ensures(true)
  effects(pure)
{
  array_slice([1, 2], 0, 0)
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @NonEmptyArray = mk(());
  array_length(@NonEmptyArray.0)
}
"""


class TestRefinedPatternBindsAreGuarded765:
    """Every narrowing PATTERN BIND checks its refinement predicate.

    `-5` is the input at every shape, and it is chosen so no fallback can
    pass for the right answer: a clamp to zero, a default, or a dropped guard
    all produce a NUMBER, and only the guard produces the violation.  The
    assertion is on the guard's own diagnostic — `Refinement violation` plus
    the predicate text — rather than on a trap word, because an unrelated
    fault (a bad offset, an out-of-bounds read) also traps and would read as
    a guard that fired.
    """

    @pytest.mark.parametrize("shape", sorted(_765_SHAPES))
    def test_a_refinement_violating_bind_traps(
        self, shape: str, tmp_path: Path,
    ) -> None:
        out = _run(tmp_path, _765_SHAPES[shape], "--fn", "f", "--", "-5",
                   name=f"{shape}.vera")
        assert "Refinement violation" in out, (
            f"{shape}: -5 was bound into a `@Pos` slot with no guard — the "
            f"arm body then reasons from `> 0` about a negative:\n{out}"
        )
        assert "@Int.0 > 0" in out, (
            f"{shape}: the trap does not name the predicate that failed, so "
            f"it may be an unrelated fault:\n{out}"
        )

    @pytest.mark.parametrize("shape", sorted(_765_SHAPES))
    def test_a_satisfying_value_passes(self, shape: str, tmp_path: Path) -> None:
        """The over-rejection control.

        Without it, "the guard fires" is equally satisfied by a guard that
        fires on everything, which would break every valid program.
        """
        out = _run(tmp_path, _765_SHAPES[shape], "--fn", "f", "--", "7",
                   name=f"{shape}_ok.vera")
        assert out.strip() == "7", (
            f"{shape}: a value satisfying the predicate was rejected:\n{out}"
        )

    def test_the_guard_reaches_inside_a_lifted_closure(
        self, tmp_path: Path,
    ) -> None:
        """A closure body is a translation context of its own.

        It was built with no refinement-guard emitter (#1268 left it out
        deliberately, the only boundary then being a `throw` payload that
        cannot occur there), so a narrowing bind inside one had nothing to
        lower its predicate with.
        """
        out = _run(tmp_path, _765_IN_CLOSURE, name="closure.vera")
        assert "Refinement violation" in out and "@Int.0 > 0" in out, out

    def test_a_pair_typed_refinement_is_guarded_over_its_pointer(
        self, tmp_path: Path,
    ) -> None:
        """String / Array refinements live in two locals, not one."""
        out = _run(tmp_path, _765_PAIR, name="pair.vera")
        assert "Refinement violation" in out, out
        assert "array_length" in out, (
            f"the trap does not name the failing predicate:\n{out}"
        )

    def test_the_obligation_stream_says_guarded(self, tmp_path: Path) -> None:
        """The status is a claim about the artifact, so it must move with it.

        The nested bind recorded `tier3_unguarded` + E506 while nothing
        guarded it — honest then, and false now.  The opaque scrutinee is
        what keeps the obligation UNDECIDED, which is the only leg on which
        the guarded flag is consulted at all.
        """
        obs, envelope = _obligations(tmp_path, _765_NESTED, name="ob.vera")
        binds = [o for o in obs if o["kind"] == "refine_bind"]
        assert [o["status"] for o in binds] == ["tier3"], binds
        _assert_partition(envelope)


# ===========================================================================
# #757 — a @Nat field reached through a generic instantiation
# ===========================================================================

# The issue's shape: `Wrap(@Int.0)` building a `Box<Nat>`.  The reader binds
# the field back at `@Int`, so the extraction guard cannot stand in for the
# construction one — and the postcondition is exactly the fact the verifier
# proves from the field's declared `@Nat`.
_757_NARROW = """\
private data Box<T> {
  Wrap(T)
}

private fn peek(@Box<Nat> -> @Int)
  requires(true)
  ensures(@Int.result >= 0)
  effects(pure)
{
  match @Box<Nat>.0 {
    Wrap(@Int) -> @Int.0
  }
}

public fn f(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  peek(Wrap(@Int.0))
}
"""

# The widening dual (#821's audit of the same blocker): a `@Nat` stored into a
# generic field instantiated to `@Int`.
_757_WIDEN = """\
public fn gf(@Nat -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Option<Int> = Some(@Nat.0);
  match @Option<Int>.0 {
    Some(@Int) -> @Int.0,
    None -> 0
  }
}
"""

# The construction site ALONE: nothing ever reads the field back, so the
# store is the only place a negative can be caught.  `_757_NARROW` reads it,
# which is what makes that fixture show the soundness consequence — and what
# makes it useless for isolating the construction guard, since the read has a
# guard of its own.
_757_STORE_ONLY = """\
private data Box<T> {
  Wrap(T)
}

private fn size(@Box<Nat> -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  1
}

public fn f(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  size(Wrap(@Int.0))
}
"""

_U64_MAX = "18446744073709551615"

#: What a tripped `@Int` -> `@Nat` narrowing guard says since #754 gave it a
#: dedicated trap kind.  Asserted instead of the bare instruction name
#: because "unreachable" is equally what a non-exhaustive match and a
#: shadow-stack overflow produce.
_NAT_GUARD_TRAP = "Negative value bound into a @Nat slot"


class TestGenericInstantiatedFieldsAreGuarded757:
    """A constructor layout is per-ADT; the instantiation is per-SITE.

    `nat_fields` / `int_fields` describe the DECLARED field types, so for
    `data Box<T> { Wrap(T) }` every flag is False at every instantiation and
    the guard that fires for a concrete `Wrap(Nat)` field was skipped.  The
    guard now reads the argument's own recorded target — the same table, and
    the same question, the verifier's `_nat_binding_target` consults — so the
    obligation's `guarded` flag and the emitted guard cannot answer
    differently.
    """

    def test_a_negative_into_a_generic_nat_field_traps_at_construction(
        self, tmp_path: Path,
    ) -> None:
        """-5, and the trap must be in the CONSTRUCTOR's frame.

        A reader that binds the field back at `@Nat` has its own guard and
        would trap too, which is why the reader here binds at `@Int`: without
        the construction guard the negative reaches the postcondition and
        `ensures(@Int.result >= 0)` — proved from the field's declared
        `@Nat` — fails at run time on a program `vera verify` accepted.
        """
        out = _run(tmp_path, _757_NARROW, "--fn", "f", "--", "-5",
                   name="n757.vera")
        assert _NAT_GUARD_TRAP in out, (
            f"-5 was stored into a `Box<Nat>` field unguarded:\n{out}"
        )
        assert "Postcondition violation" not in out, (
            f"the negative reached the reader and broke a PROVED "
            f"postcondition — the guard is missing, not merely late:\n{out}"
        )
        assert "in f " in out, (
            f"the trap is not in the constructing frame, so it came from the "
            f"reader's own guard rather than from the construction:\n{out}"
        )

    def test_an_in_range_value_passes(self, tmp_path: Path) -> None:
        out = _run(tmp_path, _757_NARROW, "--fn", "f", "--", "7",
                   name="n757ok.vera")
        assert out.strip() == "7", out

    def test_a_nat_above_i64_max_into_a_generic_int_field_traps(
        self, tmp_path: Path,
    ) -> None:
        """The widening dual, at the only value that distinguishes it.

        u64.MAX is the input because every smaller `@Nat` widens exactly; a
        guard that never fires and a guard that fires correctly are
        indistinguishable at 42.  Unguarded, this returned -1.
        """
        out = _run(tmp_path, _757_WIDEN, "--fn", "gf", "--", _U64_MAX,
                   name="w757.vera")
        # The WIDEN guard, whose dedicated kind is still a follow-up, so its
        # trap is the bare instruction rather than `_NAT_GUARD_TRAP`.
        assert "unreachable" in out, (
            f"u64.MAX widened into a generic `@Int` field silently — the "
            f"reinterpreted -1 flowed on:\n{out}"
        )
        out_ok = _run(tmp_path, _757_WIDEN, "--fn", "gf", "--", "42",
                      name="w757ok.vera")
        assert out_ok.strip() == "42", out_ok

    def test_the_obligation_stream_says_guarded(self, tmp_path: Path) -> None:
        obs, envelope = _obligations(tmp_path, _757_WIDEN, name="ob757.vera")
        coerce = [o for o in obs if o["kind"] == "nat_to_int_coerce"]
        assert [o["status"] for o in coerce] == ["tier3"], coerce
        _assert_partition(envelope)


# ===========================================================================
# #1036 — a refined base with a non-plain type argument
# ===========================================================================

_1036_PRELUDE = (
    "type NEPosArr = { @Array<{ @Int | @Int.0 > 0 }> | "
    "array_length(@Array<{ @Int | @Int.0 > 0 }>.0) > 0 };\n"
)

_1036_NAMED_FORMAL = _1036_PRELUDE + """\
private fn take(@NEPosArr -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  array_length(@NEPosArr.0)
}

public fn main(@Unit -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  take([])
}
"""

_1036_FN_ARG_BASE = """\
type IntToInt = fn(Int -> Int) effects(pure);

type NonEmptyFns = { @Array<IntToInt> | array_length(@Array<IntToInt>.0) > 0 };

public fn count(@NonEmptyFns -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  array_length(@NonEmptyFns.0)
}
"""


class TestNonPlainTypeArgBasesAreGuarded1036:
    """`Array<{refined}>` and `Array<fn(…)>` bases carry their guard.

    The disclosure said otherwise, on the premise that the binder slot name
    could not be spelt.  It can: since #1208 the binder renders through
    `vera.naming.slot_name`, whose ARGUMENTS go through the checker's own
    renderer, so a refinement or a function type in argument position renders
    like any other type.  The stale bail left the mirror wrong in the
    direction opposite to the one PR #1034 fixed — under-counting a runtime
    check that fires, and telling a reader to add a bound they already had.

    What the guard checks is the base's OWN predicate (`array_length > 0`),
    not the element refinement inside the type argument; element-wise
    membership is a separate site with its own obligation, exactly as a tuple
    component's is.
    """

    def test_an_empty_array_traps_at_the_refined_boundary(
        self, tmp_path: Path,
    ) -> None:
        out = _run(tmp_path, _1036_NAMED_FORMAL, name="np1036.vera")
        assert "Refinement violation" in out, (
            f"an empty array crossed a NonEmpty-refined boundary whose type "
            f"argument is itself refined:\n{out}"
        )
        assert "array_length" in out, (
            f"the trap does not name the failing predicate:\n{out}"
        )

    def test_the_obligation_stream_says_guarded(self, tmp_path: Path) -> None:
        obs, envelope = _obligations(
            tmp_path, _1036_NAMED_FORMAL, name="np1036v.vera")
        binds = [o for o in obs if o["kind"] == "refine_bind"]
        assert binds, obs
        assert all(o["status"] != "tier3_unguarded" for o in binds), (
            f"disclosed unguarded, but the boundary traps: "
            f"{[(o['kind'], o['status']) for o in binds]}"
        )
        _assert_partition(envelope)

    def test_a_function_typed_argument_base_is_guarded_too(
        self, tmp_path: Path,
    ) -> None:
        """The other non-plain argument shape the bail named.

        Read from the emitted module rather than from a run: an array of
        closures has no literal form the backend compiles yet, so there is no
        way to hand this boundary an empty one.
        """
        proc = _cli(
            "compile", "--wat",
            str(_write(tmp_path, _1036_FN_ARG_BASE, "fnarg.vera")))
        assert proc.returncode == 0, proc.stderr[-500:]
        assert "call $vera.contract_fail" in proc.stdout, (
            "no boundary guard for a refined base whose type argument is a "
            "function type"
        )


# ===========================================================================
# #754 — an effect operation's argument, and the guard's own trap kind
# ===========================================================================

# The issue's site, at the one built-in operation that has a `@Nat` formal.
# A user-declared effect cannot serve as the reproducer: its enclosing
# function is an E603 codegen skip, so there is no run to guard.
_754_OP_ARG = """\
public fn f(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(<IO>)
{
  IO.sleep(@Int.0);
  0
}
"""

# The same site with an argument the solver cannot settle, so the obligation
# lands UNDECIDED — the only leg on which the `guarded` flag is consulted.
_754_OP_ARG_OPAQUE = """\
public fn f(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(<IO>)
{
  IO.sleep(array_length(string_lines("a")) - 5);
  0
}
"""

# A USER-declared effect: obligated, and honestly UNGUARDED, because the
# enclosing function does not compile at all.
_754_USER_EFFECT = """\
effect E {
  op wait(Nat -> Unit);
}

public fn f(@Unit -> @Unit)
  requires(true)
  ensures(true)
  effects(<E>)
{
  E.wait(array_length(string_lines("a")) - 5)
}
"""


class TestEffectOperationArgumentsAreGuarded754:
    """An operation's argument is guarded from its FORMAL, like any call's.

    `_effect_ops` carries a dispatch target and nothing about types, so an
    operation argument was the one narrowing site with no formal to guard
    against.  The registry is built from the same table the checker typed the
    call against — `TypeEnv.effects` for the built-ins, the program's own
    `effect` / `ability` declarations for the rest — so a formal cannot be
    obligated by the verifier without being visible to codegen.
    """

    def test_a_negative_into_a_nat_op_formal_traps(self, tmp_path: Path) -> None:
        out = _run(tmp_path, _754_OP_ARG, "--fn", "f", "--", "-5",
                   name="op754.vera")
        assert _NAT_GUARD_TRAP in out, (
            f"-5 reached the host through `IO.sleep`'s `@Nat` formal:\n{out}"
        )

    def test_a_valid_argument_passes(self, tmp_path: Path) -> None:
        out = _run(tmp_path, _754_OP_ARG, "--fn", "f", "--", "0",
                   name="op754ok.vera")
        assert out.strip() == "0", out

    def test_the_classification_equals_what_the_module_does(
        self, tmp_path: Path,
    ) -> None:
        """PARITY on the undecided leg, where the flag is actually read."""
        obs, envelope = _obligations(
            tmp_path, _754_OP_ARG_OPAQUE, name="op754v.vera")
        binds = [o for o in obs if o["kind"] == "nat_bind"]
        assert binds, obs
        undecided = [o for o in binds
                     if o["status"] in ("tier3", "tier3_unguarded", "timeout")]
        assert undecided, (
            f"every nat_bind settled statically ({[o['status'] for o in binds]}"
            f"), so the guarded flag was never consulted"
        )
        verifier_says_guarded = any(
            o["status"] != "tier3_unguarded" for o in undecided)
        out = _run(tmp_path, _754_OP_ARG_OPAQUE, "--fn", "f", "--", "1",
                   name="op754r.vera")
        codegen_guards = _NAT_GUARD_TRAP in out
        assert codegen_guards == verifier_says_guarded, (
            f"module {'traps' if codegen_guards else 'does NOT trap'}, "
            f"verifier says "
            f"{'guarded' if verifier_says_guarded else 'unguarded'} "
            f"({[o['status'] for o in undecided]})"
        )
        _assert_partition(envelope)

    def test_a_user_effect_stays_honestly_unguarded(
        self, tmp_path: Path,
    ) -> None:
        """The over-claiming control, and the reason the roster is consulted.

        A user-declared effect makes its whole enclosing function an E603
        codegen skip, so there is no run for a guard to protect.  Recording
        `guarded` there would be #1268's mistake one boundary over — a
        Tier-3 promise about a runtime that is never reached — so the
        classification intersects the formal's base with
        `narrowing.COMPILABLE_EFFECTS`, the roster codegen itself decides
        compilability from.
        """
        obs, envelope = _obligations(
            tmp_path, _754_USER_EFFECT, name="user754.vera")
        binds = [o for o in obs if o["kind"] == "nat_bind"]
        assert [o["status"] for o in binds] == ["tier3_unguarded"], binds
        assert [o.get("error_code") for o in binds] == ["E504"], binds
        _assert_partition(envelope)

        proc = _cli("compile", "--wat",
                    str(_write(tmp_path, _754_USER_EFFECT, "user754c.vera")))
        assert "E603" in (proc.stdout + proc.stderr), (
            "the fixture compiles after all, so the disclosure is about a "
            "run that CAN happen and the reasoning above no longer applies"
        )

    def test_only_get_put_and_throw_have_a_bare_route(
        self, tmp_path: Path,
    ) -> None:
        """The claim the unqualified dispatch loop rests on.

        Codegen guards a bare operation argument from the CELL, not from the
        declaration, and that is correct only while the bare-routable set is
        exactly the three cell-carrying ops.  A fourth joining it would be
        dispatched with no formal to guard against, silently — so the set is
        asserted rather than remembered.
        """
        from vera.environment import TypeEnv

        env = TypeEnv()
        # Keyed by (effect, op), never by op name alone: `State.get` is
        # routable and `Http.get` is not, so a name-keyed set lets the
        # routable one whitelist `get` and hides the other losing its E217
        # (PR review).
        bare_ok: set[tuple[str, str]] = set()
        for eff_name, info in sorted(env.effects.items()):
            for op_name in sorted(info.operations):
                src = (
                    f"public fn f(@Unit -> @Unit)\n"
                    f"  requires(true)\n  ensures(true)\n"
                    f"  effects(<{eff_name}>)\n"
                    f"{{\n  {op_name}(())\n}}\n"
                )
                proc = _cli(
                    "check",
                    str(_write(tmp_path, src, f"bare_{eff_name}_{op_name}.vera")))
                out = proc.stdout + proc.stderr
                # E217 is emitted BEFORE the op-call check, so a non-routable
                # op that loses it typically fails on ARITY (E204) instead —
                # which "no E217" would read as acceptance.  Only a check that
                # raises neither counts as routable.
                if "E217" not in out and "E204" not in out:
                    bare_ok.add((eff_name, op_name))
        unexpected = {
            pair for pair in bare_ok
            if pair not in {("State", "get"), ("State", "put"),
                            ("Exn", "throw")}
        }
        assert not unexpected, (
            f"these ops accept a BARE call and are not cell-carrying, so "
            f"their arguments reach the unqualified dispatch loop with no "
            f"formal to guard against: {sorted(unexpected)}"
        )


class TestTheNarrowingGuardNamesItself754:
    """The trap says which boundary failed, not which instruction ran.

    A tripped narrowing guard reported `kind="unreachable"`, whose Fix
    paragraph lists three causes — a non-exhaustive `match`, a compiler
    assertion, a shadow-stack overflow — and a narrowing is none of them, so
    the one piece of advice that would have helped (`requires(... >= 0)`)
    was the one it did not give.  The guard now signals
    `vera.nat_guard_trap` before its `unreachable`, the same channel #808
    built for arithmetic overflow.
    """

    def test_the_trap_carries_the_narrowing_kind_and_its_fix(
        self, tmp_path: Path,
    ) -> None:
        out = _run(tmp_path, _765_LET.replace("@Pos", "@Nat"),
                   "--fn", "f", "--", "-5", name="kind754.vera")
        assert _NAT_GUARD_TRAP in out, out
        assert "requires(... >= 0)" in out, (
            f"the Fix does not name the precondition that would discharge "
            f"this:\n{out}"
        )
        assert "non-exhaustive" not in out, (
            f"the generic `unreachable` paragraph is still being used:\n{out}"
        )

    def test_the_signal_declares_its_own_import(self, tmp_path: Path) -> None:
        """A guard that calls an undeclared import fails WAT compilation.

        The flag that emits the declaration is set beside the call, and has
        to survive every per-scope merge — the body's, the postcondition's,
        and a lifted closure's.  This drives the closure one, which is the
        merge a guard emitted only inside a lifted body depends on.
        """
        source = """\
public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  array_length(array_map(array_range(0 - 2, 0),
    fn(@Int -> @Int) effects(pure) { let @Nat = @Int.0; nat_to_int(@Nat.0) }))
}
"""
        proc = _cli("compile", "--wat",
                    str(_write(tmp_path, source, "sig754.vera")))
        assert proc.returncode == 0, proc.stderr[-600:]
        assert 'import "vera" "nat_guard_trap"' in proc.stdout, (
            "the guard inside the lifted closure calls the signal, but the "
            "module does not declare the import"
        )
        assert proc.stdout.count("call $vera.nat_guard_trap") >= 1


# ===========================================================================
# #1222 — the decreases measure and the range its guard compares in
# ===========================================================================

# The measure halves each hop, so u64.MAX reaches the base case in 64 steps —
# a `- 1` measure would need 2^64 of them and the observation would be a
# timeout rather than a verdict.
_1222_UNBOUNDED = """\
public fn halve(@Nat -> @Nat)
  requires(true)
  ensures(true)
  decreases(@Nat.0)
  effects(pure)
{
  if @Nat.0 == 0 then {
    0
  } else {
    halve(@Nat.0 / 2)
  }
}
"""

_1222_BOUNDED = _1222_UNBOUNDED.replace(
    "requires(true)", "requires(@Nat.0 < 1000)")

_1222_PROVABLY_OUT = _1222_UNBOUNDED.replace(
    "requires(true)", "requires(@Nat.0 > 9223372036854775807)")

_I64_MAX = "9223372036854775807"
_I64_MAX_PLUS_1 = "9223372036854775808"


class TestDecreasesMeasureFitsTheGuardsRange1222:
    """The termination proof and the termination check must agree on the
    value they are talking about.

    The proof reasons over unbounded integers; the runtime guard compares
    with `i64.lt_s` / `i64.ge_s`.  A `@Nat` is a u64 in that i64, so above
    `i64.MAX` it reads NEGATIVE, the guard's non-negativity clause fails, and
    a program whose termination the verifier PROVED at Tier 1 aborts with
    "failed to decrease" — a true statement about the machine value and a
    false one about the program.

    The remedy is disclosure, not a wider comparison: this compiler treats a
    `@Nat` above `i64.MAX` as an edge it discloses (E530 and E531 exist for
    exactly that), so widening this one comparison would support a range the
    rest of the language does not.  The shared fact is obligated instead —
    Tier 1 where the measure is bounded, Tier 3 with a runtime backstop where
    it is not, and a loud E536 where it provably does not hold.
    """

    def test_the_boundary_is_where_the_two_readings_part(
        self, tmp_path: Path,
    ) -> None:
        """i64.MAX runs; i64.MAX + 1 does not.

        The pair, not either alone: a guard that rejected both would be
        indistinguishable from one that rejects everything, and one that
        accepted both would not be measuring the boundary at all.
        """
        ok = _run(tmp_path, _1222_UNBOUNDED, "--fn", "halve", "--", _I64_MAX,
                  name="d1222a.vera")
        assert ok.strip() == "0", (
            f"a measure AT i64.MAX must still run:\n{ok}"
        )
        over = _run(tmp_path, _1222_UNBOUNDED, "--fn", "halve", "--",
                    _I64_MAX_PLUS_1, name="d1222b.vera")
        assert "i64 range" in over, (
            f"a measure past i64.MAX ran, or failed for another reason:\n"
            f"{over}"
        )

    def test_the_failure_names_the_range_not_the_termination_rule(
        self, tmp_path: Path,
    ) -> None:
        """It reported "failed to decrease", which is the wrong advice.

        The measure decreases perfectly well; what it does not do is fit the
        i64 the check compares in.  A reader told the metric fails to
        decrease goes looking for a bug in a recursion that has none.
        """
        out = _run(tmp_path, _1222_UNBOUNDED, "--fn", "halve", "--",
                   _I64_MAX_PLUS_1, name="d1222c.vera")
        assert "failed to decrease" not in out, (
            f"the trap still blames the termination rule for a range "
            f"problem:\n{out}"
        )
        assert "@Nat above i64.MAX" in out, out

    def test_an_unbounded_measure_is_a_guarded_tier3(
        self, tmp_path: Path,
    ) -> None:
        obs, envelope = _obligations(
            tmp_path, _1222_UNBOUNDED, name="d1222v.vera")
        bounds = [o for o in obs if o["kind"] == "decreases_bound"]
        assert [o["status"] for o in bounds] == ["tier3"], obs
        # The termination proof itself is unaffected — it was never wrong.
        assert [o["status"] for o in obs if o["kind"] == "decreases"] == [
            "verified"], obs
        _assert_partition(envelope)

    def test_a_bounded_measure_proves_at_tier_1(self, tmp_path: Path) -> None:
        """The over-disclosure control.

        Without it, "the obligation exists" is equally satisfied by one that
        never discharges, which would put every terminating program on Tier 3
        for a fact most of them establish.
        """
        obs, envelope = _obligations(
            tmp_path, _1222_BOUNDED, name="d1222w.vera")
        bounds = [o for o in obs if o["kind"] == "decreases_bound"]
        assert [o["status"] for o in bounds] == ["verified"], obs
        _assert_partition(envelope)

    def test_a_provably_out_of_range_measure_is_a_loud_error(
        self, tmp_path: Path,
    ) -> None:
        obs, envelope = _obligations(
            tmp_path, _1222_PROVABLY_OUT, name="d1222x.vera")
        bounds = [o for o in obs if o["kind"] == "decreases_bound"]
        assert [(o["status"], o.get("error_code")) for o in bounds] == [
            ("violated", "E536")], obs
        assert envelope["ok"] is False
        assert "E536" in [d.get("error_code") for d in envelope["diagnostics"]]
        _assert_partition(envelope)

    def test_an_int_measure_records_nothing(self, tmp_path: Path) -> None:
        """The scope control: only `@Nat` has two readings.

        An `@Int` measure IS the i64 the guard compares in, so there is no
        fact to obligate and no guard to emit; recording one would put every
        `@Int`-measured recursion on Tier 3 for nothing, and the guard would
        false-trip a legitimately negative first activation.
        """
        source = """\
public fn down(@Int -> @Int)
  requires(@Int.0 >= 0)
  ensures(true)
  decreases(@Int.0)
  effects(pure)
{
  if @Int.0 <= 0 then { 0 } else { down(@Int.0 - 1) }
}
"""
        obs, envelope = _obligations(tmp_path, source, name="d1222i.vera")
        assert not [o for o in obs if o["kind"] == "decreases_bound"], obs
        _assert_partition(envelope)


# ===========================================================================
# Mutation validation — every guard above is load-bearing
# ===========================================================================

def _observe_in_process(source: str, fn: str, args: list[object]) -> str:
    """What running *source* DOES, as a short string.

    ``"ran"`` when it completes, otherwise the trap's own text.  A boolean
    is not enough for these mutations: neutering a guard does not always let
    the value through — sometimes a second, later guard catches it, and
    sometimes (as with the measure-range check) the pre-fix behaviour was a
    trap with the WRONG message rather than no trap.  Both are real changes
    and neither is visible to "did it run".

    In-process because the mutations are monkeypatches on the emitters,
    which a subprocess would not see.  The compile step is deliberately
    outside the try: a program that stopped COMPILING is a measurement
    failure, not evidence that a guard was load-bearing.

    Compiled through the CHECKER's artifacts, not a bare
    ``transform -> compile``: several of these guards read the checker's
    recorded target types, which that shorter path does not thread, so a
    bare compile silently emits no guard and every mutation below would
    read as already-neutered.  Measured: the #757 store-only probe RAN
    under the bare path and traps under this one.
    """
    import tempfile

    from vera.checker import typecheck_with_artifacts
    from vera.codegen import compile as codegen_compile
    from vera.codegen import execute
    from vera.parser import parse_to_ast

    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".vera", delete=False, encoding="utf-8",
    ) as handle:
        handle.write(source)
        path = handle.name
    try:
        program = parse_to_ast(source)
        diags, arts = typecheck_with_artifacts(program, source, file=path)
        errors = [d for d in diags if d.severity == "error"]
        assert not errors, f"the probe does not type-check: {errors}"
        compiled = codegen_compile(
            program, source=source, file=path,
            expr_semantic_types=arts.expr_semantic_types,
            expr_target_types=arts.expr_target_types,
        )
        cg_errors = [d for d in compiled.diagnostics if d.severity == "error"]
        assert not cg_errors, f"the probe does not compile: {cg_errors}"
    finally:
        Path(path).unlink(missing_ok=True)
    try:
        execute(compiled, fn_name=fn, args=args)
    except Exception as exc:  # noqa: BLE001 — the trap IS the observation
        return str(exc)
    return "ran"


def _guard_mutations() -> list[tuple]:
    """(label, owner, method, neutered, probe, with_guard, without_guard).

    Each probe is a program the guard exists to stop, run on the value it
    exists to catch; the last two are substrings the observation must
    contain WITH the guard and WITHOUT it.  They differ for every entry,
    which is the whole content of the check.
    """
    from vera.codegen.contracts import ContractsMixin
    from vera.wasm.calls import CallsMixin
    from vera.wasm.data import DataMixin

    return [
        (
            "765 refined pattern bind",
            DataMixin, "_emit_bind_refine_guard",
            lambda self, te, local, where, node, env: [],
            (_765_DIRECT, "f", [-5]),
            "Refinement violation", "ran",
        ),
        (
            # The probe never reads the field back, so the store is the
            # only place a negative can be caught.  `_757_NARROW` — which
            # does read it — cannot isolate this guard: its read has a
            # guard of its own and catches the same value one frame later.
            "757 generic instantiated field",
            DataMixin, "_ctor_field_mono_base",
            lambda self, arg: None,
            (_757_STORE_ONLY, "f", [-5]),
            "Negative value bound into a @Nat slot", "ran",
        ),
        (
            "754 effect-operation argument",
            CallsMixin, "_guard_effect_op_arg",
            lambda self, arg, instrs, formals, index: instrs,
            (_754_OP_ARG, "f", [-5]),
            "Negative value bound into a @Nat slot", "ran",
        ),
        (
            # The pre-fix behaviour was not "runs": it was a trap blaming the
            # termination rule for a measure that decreases perfectly well.
            "1222 decreases measure range",
            ContractsMixin, "_dec_measure_bound_check",
            lambda self, ctx, contract, measured, name, indent="": [],
            (_1222_UNBOUNDED, "halve", [2 ** 63]),
            "i64 range", "failed to decrease",
        ),
    ]


class TestEveryGuardIsLoadBearing:
    """Neuter one guard; the probe's behaviour must change.

    A green suite is necessary and not sufficient: a probe can refuse a
    value for a reason that has nothing to do with the guard under test — an
    unrelated fault, a second guard covering the same value, a fixture that
    fails to run at all — and every cell above would stay green with the
    guard removed.  So each guard's emitter is replaced with a pass-through
    and the probe re-run, and BOTH observations are asserted: what the guard
    produces, and what its absence produces.  Asserting only the first would
    not separate "this guard acts" from "something acts".
    """

    @pytest.mark.parametrize(
        ("label", "owner", "method", "neutered", "probe", "with_guard",
         "without_guard"),
        _guard_mutations(),
        ids=[m[0] for m in _guard_mutations()],
    )
    def test_removing_the_guard_changes_what_the_program_does(
        self,
        label: str,
        owner: object,
        method: str,
        neutered: object,
        probe: tuple,
        with_guard: str,
        without_guard: str,
        monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        source, fn, args = probe
        assert with_guard != without_guard, f"{label}: nothing to tell apart"
        before = _observe_in_process(source, fn, args)
        assert with_guard in before, (
            f"{label}: with the guard in place the program does not do what "
            f"this cell says it does — {before!r} lacks {with_guard!r}"
        )
        monkeypatch.setattr(owner, method, neutered)
        after = _observe_in_process(source, fn, args)
        assert without_guard in after, (
            f"{label}: neutering the guard did not change the outcome — "
            f"{after!r} lacks {without_guard!r}, so something else is "
            f"producing the behaviour the cells above attribute to it"
        )


# ---------------------------------------------------------------------------
# #1222, self-review: the range check does not ride on the CHAIN guard
# ---------------------------------------------------------------------------

# The chain guard is declined for a function that declares `Exn` (a throw
# unwinds past the exit restores and would leave stale chain state)...
_1222_EXN = _1222_UNBOUNDED.replace("effects(pure)", "effects(<Exn<Int>>)", 1)

# ...and for a measure with a component the backend cannot rank, which here is
# the SIBLING of a `@Nat` component that translates perfectly well (#1177's
# parameterized-ADT limitation).
_1222_UNRANKABLE_SIBLING = """\
private data List<T> {
  Nil,
  Cons(T, List<T>)
}

public fn walk(@Nat, @List<Int> -> @Nat)
  requires(true)
  ensures(true)
  decreases(@Nat.0, @List<Int>.0)
  effects(pure)
{
  if @Nat.0 == 0 then {
    0
  } else {
    walk(@Nat.0 / 2, @List<Int>.0)
  }
}
"""


class TestTheRangeCheckSurvivesADeclinedChainGuard1222:
    """A declined CHAIN guard must not take the RANGE check with it.

    Found reviewing this PR's own first cut, which folded the range check
    into `_compile_decreases_entry`'s success path.  Three shapes decline the
    chain guard — an `Exn`-declaring function, an untranslatable component,
    an ADT component with no structural-rank helper — and every one of them
    is a statement about state carried ACROSS activations.  A `@Nat`
    component's range check reads one locally-evaluated value and compares it
    against a constant; it carries nothing.  So the obligation recorded a
    guarded Tier 3 for a module with no guard in it at all, which is the
    exact class of false claim this PR exists to close, introduced by the
    fix for it.
    """

    @pytest.mark.parametrize(
        ("label", "source", "fn"),
        [
            ("exn_declared", _1222_EXN, "halve"),
            ("unrankable_sibling", _1222_UNRANKABLE_SIBLING, "walk"),
        ],
        ids=["exn_declared", "unrankable_sibling"],
    )
    def test_the_measure_range_is_still_checked(
        self, label: str, source: str, fn: str, tmp_path: Path,
    ) -> None:
        # The premise: this shape really does decline the chain guard, so the
        # cell is about the range check surviving alone rather than about a
        # chain guard that happens to cover it.
        proc = _cli("compile", "--wat",
                    str(_write(tmp_path, source, f"{label}_c.vera")))
        assert proc.returncode == 0, proc.stderr[-500:]
        assert "dec_prev" not in proc.stdout, (
            f"{label}: the chain guard IS emitted here, so this cell no "
            f"longer isolates the range check"
        )
        assert "i64 range" in proc.stdout, (
            f"{label}: the chain guard is declined and took the range check "
            f"with it — the obligation claims a runtime check the module "
            f"does not contain"
        )

    def test_the_exn_shape_traps_past_the_boundary_and_runs_below_it(
        self, tmp_path: Path,
    ) -> None:
        """The artifact, not the WAT: the pair that settles it."""
        over = _run(tmp_path, _1222_EXN, "--fn", "halve", "--",
                    _I64_MAX_PLUS_1, name="exn1222a.vera")
        assert "i64 range" in over, over
        ok = _run(tmp_path, _1222_EXN, "--fn", "halve", "--", "10",
                  name="exn1222b.vera")
        assert ok.strip() == "0", ok

    def test_the_obligation_was_already_claiming_this(
        self, tmp_path: Path,
    ) -> None:
        """Both shapes recorded a guarded `tier3` before the guard existed.

        Kept as the statement of what made the gap a defect rather than a
        missing feature: the claim came first.
        """
        for label, source in (("exn", _1222_EXN),
                              ("sibling", _1222_UNRANKABLE_SIBLING)):
            obs, envelope = _obligations(
                tmp_path, source, name=f"{label}_ob.vera")
            bounds = [o for o in obs if o["kind"] == "decreases_bound"]
            assert [o["status"] for o in bounds] == ["tier3"], (label, obs)
            _assert_partition(envelope)


# ===========================================================================
# #1416 — the two Tuple-component sites, from this PR's own review round
# ===========================================================================

# The narrowing at CONSTRUCTION.  Its widening twin at the same site has read
# the checker's target-type table since #820; this arm never did, so one
# field could be guarded and its neighbour not, at one construction.
_1416_CONSTRUCT = """\
private fn snd(@Tuple<Nat, Int> -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  1
}

public fn tc(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  snd(Tuple(@Int.0, 2))
}
"""

# The widening at a DESTRUCTURE whose source is not a literal.  An inline
# `if` over tuple literals keeps the value off any function boundary, whose
# own component check would otherwise trap for an unrelated reason.
# ASYMMETRIC on purpose: the widened `@Nat` sits in component 0 and a
# constant `@Int` in component 1, and component 0 is the one read back.  With
# the same expression in both slots a guard or obligation keyed to the wrong
# component produces an identical verdict and an identical value, so the cell
# could not separate "component 0 is guarded" from "component 1 is" (PR
# review; the repo's own slot-order rule for non-commutative shapes).
_1416_DESTRUCTURE = """\
public fn td(@Nat -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let Tuple<@Int, @Int> =
    if @Nat.0 > 0 then { Tuple(@Nat.0, 1) }
    else { Tuple(@Nat.0, 2) };
  @Int.1
}
"""


_P1_NAT_ELEMENT_STORE_ONLY = """\
public fn f(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Array<Nat> = [@Int.0];
  1
}
"""

_P1_NESTED_ARRAY = """\
type Pos = { @Int | @Int.0 > 0 };

public fn f(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Array<Array<Pos>> = [[@Int.0]];
  @Array<Array<Pos>>.0[0][0]
}
"""

_P1_MAP_REFINED_VALUE = """\
type Pos = { @Int | @Int.0 > 0 };

public fn f(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Map<String, Pos> = map_insert(map_new(), "k", @Int.0);
  match map_get(@Map<String, Pos>.0, "k") {
    Some(@Pos) -> @Pos.0,
    None -> 0
  }
}
"""

_P1_MAP_NAT_VALUE = """\
public fn f(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Map<String, Nat> = map_insert(map_new(), "k", @Int.0);
  1
}
"""

_P1_ARRAY_OF_REFINED_TUPLES = """\
type Pos = { @Int | @Int.0 > 0 };

public fn f(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Array<Tuple<Pos, Int>> = [Tuple(@Int.0, 1)];
  let Tuple<@Pos, @Int> = @Array<Tuple<Pos, Int>>.0[0];
  @Pos.0
}
"""

_P1_FLAT_ARRAY_CONTROL = """\
type Pos = { @Int | @Int.0 > 0 };

public fn f(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Array<Pos> = [@Int.0];
  1
}
"""


class TestConstructionPositionReachesNestedContainers:
    """The silent-absence class, one nesting level deeper and one container
    over (#1426, third-pass P1).

    Fixing the FLAT array element left four shapes still unobligated: a
    nested array literal's inner element, a `Map` value in each direction,
    and an array of refined tuples.  All four verified clean — `ok: true`,
    no `refine_bind`, no `nat_bind` — on base and on the flat fix.

    The mechanism is the same in each: the checker records a target type for
    the OUTER literal and none for the inner node, and for a `map_insert`
    the value argument's recorded target is the ERASED base (`Int` for a
    `Map<String, Pos>`), because generic unification resolves `V` against
    the `map_new()` receiver.  A walk that reads a target per expression
    therefore sees nothing to obligate.  The remedy is to thread the
    expected type DOWN from the one place that still has it — the outer
    literal's target, or the enclosing `let`'s DECLARED type, which is a
    declaration rather than an inference and keeps its refinement.

    What each shape does at runtime differs, and the cells say which: two
    are caught by the read-side pattern-bind guard (#765) and two are not
    guarded anywhere.  Neither had an obligation, which is the defect —
    silence cannot be read in either direction.
    """

    def test_a_nested_inner_element_is_obligated(
        self, tmp_path: Path,
    ) -> None:
        obs, envelope = _obligations(
            tmp_path, _P1_NESTED_ARRAY, name="p1a.vera")
        binds = [(o["status"], o.get("error_code"))
                 for o in obs if o["kind"] == "refine_bind"]
        assert binds == [("violated", "E505")], obs
        assert envelope["ok"] is False
        _assert_partition(envelope)

    def test_and_the_nested_element_value_flows_out_unguarded(
        self, tmp_path: Path,
    ) -> None:
        """The run differential: nothing catches this one at all.

        Unlike the two tuple/`Option` shapes below, the inner element is
        read back as a plain projection, so no pattern bind guards it and
        `-4` is returned from a function whose element type forbids it.
        """
        out = _run(tmp_path, _P1_NESTED_ARRAY, "--fn", "f", "--", "-4",
                   name="p1b.vera")
        assert out.strip() == "-4", out

    def test_a_refined_map_value_is_obligated(self, tmp_path: Path) -> None:
        """The insert's own record, which was absent entirely.

        Read by membership, not by equality: the `let` whose declared type
        writes a refinement on a component publishes that claim to later
        readers of the slot and raises its own #1410 records beside this one.
        Those are about the slot, this one is about the value going in.
        """
        obs, envelope = _obligations(
            tmp_path, _P1_MAP_REFINED_VALUE, name="p1c.vera")
        binds = [(o["status"], o.get("error_code"))
                 for o in obs if o["kind"] == "refine_bind"]
        assert ("violated", "E505") in binds, obs
        assert envelope["ok"] is False
        _assert_partition(envelope)

    def test_the_refined_map_value_is_caught_only_on_the_way_out(
        self, tmp_path: Path,
    ) -> None:
        """The differential that names WHERE the check lives.

        The insert plants nothing; the trap arrives at the `Some(@Pos)`
        sub-pattern when the value is read back (#765).  A program that
        inserts and never reads keeps the forbidden value, which is why the
        obligation has to exist at the insert.
        """
        out = _run(tmp_path, _P1_MAP_REFINED_VALUE, "--fn", "f", "--", "-4",
                   name="p1d.vera")
        assert "Refinement violation in constructor sub-pattern" in out, out

    def test_a_nat_map_value_is_obligated_and_disclosed_unguarded(
        self, tmp_path: Path,
    ) -> None:
        """`Map<String, Nat>`: nothing guards the insert, so E503/E504.

        The run differential is the store-only one — `-4` is inserted and
        `f` returns `1` — so this obligation must NOT claim `guarded`.
        """
        obs, envelope = _obligations(
            tmp_path, _P1_MAP_NAT_VALUE, name="p1e.vera")
        binds = [(o["status"], o.get("error_code"))
                 for o in obs if o["kind"] == "nat_bind"]
        assert binds == [("violated", "E503")], obs
        _assert_partition(envelope)

        out = _run(tmp_path, _P1_MAP_NAT_VALUE, "--fn", "f", "--", "-4",
                   name="p1f.vera")
        assert out.strip() == "1", (
            f"expected the insert to plant no guard, which is what the "
            f"unguarded flag on this obligation states:\n{out}"
        )

    def test_a_refined_tuple_inside_an_array_is_obligated(
        self, tmp_path: Path,
    ) -> None:
        """One container over: the element type is neither refined nor
        `@Nat`, so both scalar arms decline and the components were never
        reached until the descent decomposed the `Tuple`."""
        obs, envelope = _obligations(
            tmp_path, _P1_ARRAY_OF_REFINED_TUPLES, name="p1i.vera")
        binds = [(o["status"], o.get("error_code"))
                 for o in obs if o["kind"] == "refine_bind"]
        assert binds == [("violated", "E505")], obs
        assert envelope["ok"] is False
        _assert_partition(envelope)

        out = _run(tmp_path, _P1_ARRAY_OF_REFINED_TUPLES, "--fn", "f", "--",
                   "-4", name="p1j.vera")
        assert "Refinement violation in let Tuple" in out, out

    def test_one_obligation_per_component_not_one_per_route(
        self, tmp_path: Path,
    ) -> None:
        """The over-recording control, and why the descent is memoised.

        Three routes can reach the same component — the array literal's own
        recorded target, the enclosing `let`'s declared type, and the
        tuple-construction path — and each recording it would inflate
        `len(obligations)` and the Tier-3 count derived from it.  The flat
        `let @Array<Pos> = [...]` already worked before this change, so its
        count is the fixed point the descent must not move.
        """
        obs, envelope = _obligations(
            tmp_path, _P1_FLAT_ARRAY_CONTROL, name="p1k.vera")
        binds = [(o["status"], o.get("error_code"))
                 for o in obs if o["kind"] == "refine_bind"]
        assert binds == [("violated", "E505")], obs
        _assert_partition(envelope)


class TestTupleComponentSitesAreGuarded1416:
    """The last two members of the coercion-guard family.

    Filed while working this PR's review round and closed in it, because both
    have the root #757 already fixed one site over: read the component's type
    from the CHECKER's table rather than from a per-ADT bitmap that describes
    only declared types.  The construction arm gains the narrowing twin of
    the reader its widening arm has used since #820; the destructure arm
    gains the same reader for a non-literal source, where only a literal one
    was covered.

    The destructure half was observable — it returned a reinterpreted `-1`.
    The construction half was not: every consumer path is itself guarded (a
    callee's parameter component check, a return component check, the
    destructure), so the negative could not escape. What it was, was an
    obligation claiming `tier3_unguarded` at a site the composition covered
    — a disclosure pointing at the wrong place. Guarding the store makes the
    site's own claim true rather than borrowing its neighbours'.
    """

    def test_the_destructure_widening_traps_at_u64_max(
        self, tmp_path: Path,
    ) -> None:
        out = _run(tmp_path, _1416_DESTRUCTURE, "--fn", "td", "--", _U64_MAX,
                   name="d1416.vera")
        assert "unreachable" in out, (
            f"u64.MAX read out of a `@Nat` tuple component into an `@Int` "
            f"binding returned a reinterpreted value:\n{out}"
        )
        ok = _run(tmp_path, _1416_DESTRUCTURE, "--fn", "td", "--", "42",
                  name="d1416ok.vera")
        assert ok.strip() == "42", ok

    def test_the_construction_narrowing_is_guarded_at_the_store(
        self, tmp_path: Path,
    ) -> None:
        """Read from the module, because the value cannot escape to be run.

        Every consumer of the tuple guards it again, so a run cannot separate
        "the store is guarded" from "the read is". The store's own guard is
        what the obligation claims, so the store is what is measured.
        """
        proc = _cli("compile", "--wat",
                    str(_write(tmp_path, _1416_CONSTRUCT, "c1416.vera")))
        assert proc.returncode == 0, proc.stderr[-500:]
        assert "call $vera.nat_guard_trap" in proc.stdout, (
            "the `@Int` component stored into a `Tuple<Nat, Int>` carries no "
            "narrowing guard, while its `@Int` neighbour's widening twin at "
            "the same site does"
        )

    @pytest.mark.parametrize(
        ("label", "source", "kind"),
        [
            ("construct", _1416_CONSTRUCT, "nat_bind"),
            ("destructure", _1416_DESTRUCTURE, "nat_to_int_coerce"),
        ],
        ids=["construct", "destructure"],
    )
    def test_the_obligation_no_longer_discloses_unguarded(
        self, label: str, source: str, kind: str, tmp_path: Path,
    ) -> None:
        obs, envelope = _obligations(tmp_path, source, name=f"{label}_ob.vera")
        rows = [o for o in obs if o["kind"] == kind]
        assert rows, obs
        assert all(o["status"] != "tier3_unguarded" for o in rows), (
            f"{label}: still disclosed unguarded while the site now guards: "
            f"{[(o['kind'], o['status']) for o in rows]}"
        )
        _assert_partition(envelope)


_1222_EFFECTFUL_MEASURE = """\
private fn risky(@Nat -> @Nat)
  requires(true)
  ensures(true)
  effects(<Exn<Int>>)
{
  if @Nat.0 == 0 then { throw(1) } else { @Nat.0 }
}

public fn walk(@Nat -> @Nat)
  requires(true)
  ensures(true)
  decreases(risky(@Nat.0))
  effects(<Exn<Int>>)
{
  if @Nat.0 == 0 then { 0 } else { walk(@Nat.0 / 2) }
}
"""


class TestTheRangeCheckDoesNotRunTheMeasureAgain1222:
    """The decline path may not make an extra evaluation observable.

    Found by CodeRabbit on this PR.  Where the CHAIN guard is emitted the
    measure is evaluated once and the range check reads its locals, so
    nothing new runs.  Where the chain is declined the check evaluates the
    component itself — and for an effectful component that is a new action
    at function entry, before the body.

    Measured: `decreases(risky(@Nat.0))` on a function declaring `Exn<Int>`,
    where `risky` throws on zero.  The chain guard is declined for the `Exn`
    row, and evaluating the measure there turned a program that returned 0
    into one that threw.  The check is now emitted only for a component an
    extra evaluation cannot make observable, and the obligation discloses
    E537 where it is not.
    """

    def test_the_program_still_returns_rather_than_throwing(
        self, tmp_path: Path,
    ) -> None:
        out = _run(tmp_path, _1222_EFFECTFUL_MEASURE, "--fn", "walk", "--",
                   "4", name="eff1222.vera")
        assert out.strip() == "0", (
            f"the range check evaluated an effectful measure at entry, so a "
            f"program that returned 0 now throws:\n{out}"
        )

    def test_and_says_so_instead_of_claiming_a_check(
        self, tmp_path: Path,
    ) -> None:
        obs, envelope = _obligations(
            tmp_path, _1222_EFFECTFUL_MEASURE, name="eff1222v.vera")
        bounds = [o for o in obs if o["kind"] == "decreases_bound"]
        assert [(o["status"], o.get("error_code")) for o in bounds] == [
            ("tier3_unguarded", "E537")], obs
        _assert_partition(envelope)

    def test_a_pure_measure_on_the_same_decline_path_is_still_checked(
        self, tmp_path: Path,
    ) -> None:
        """The over-restriction control.

        Without it, "do not evaluate" is equally satisfied by never emitting
        the check on the decline path at all — which would undo the fix this
        cell's neighbours cover, since an `Exn`-declaring function is one of
        the shapes that has no chain guard to fall back on.
        """
        proc = _cli("compile", "--wat",
                    str(_write(tmp_path, _1222_EXN, "eff1222c.vera")))
        assert proc.returncode == 0, proc.stderr[-400:]
        assert "i64 range" in proc.stdout, (
            "a PURE measure on the same declined-chain path lost its range "
            "check too"
        )


_1222_MIXED_PURITY = """\
private fn size(@Nat -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Nat.0
}

public fn walk(@Nat -> @Nat)
  requires(true)
  ensures(true)
  decreases(@Nat.0, size(@Nat.0))
  effects(<Exn<Int>>)
{
  if @Nat.0 == 0 then { 0 } else { walk(@Nat.0 / 2) }
}
"""

_1222_RANKABLE_ADT_SIBLING = """\
private data Tree {
  Leaf,
  Node(Tree, Tree)
}

private fn size(@Nat -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Nat.0
}

public fn walk(@Nat, @Tree -> @Nat)
  requires(true)
  ensures(true)
  decreases(size(@Nat.0), @Tree.0)
  effects(pure)
{
  if @Nat.0 == 0 then { 0 } else { walk(@Nat.0 / 2, @Tree.0) }
}
"""


class TestTheBoundFlagIsPerComponent1222:
    """The obligation's guarded flag is computed the way codegen filters.

    Found by the re-verification.  Codegen decides per COMPONENT — the
    declined-chain path emits a range check for each component whose extra
    evaluation cannot be observed — while the flag was computed once per
    CONTRACT and a second test, "is any component non-scalar", stood in for
    "is the chain declined".  Both over-answered, so two shapes carried an
    E537 for a component the emitted module does check: exactly the
    obligation-versus-guard drift this release exists to remove, in the
    machinery added to remove it.
    """

    def test_a_mixed_measure_splits_rather_than_condemning_both(
        self, tmp_path: Path,
    ) -> None:
        """`decreases(@Nat.0, size(@Nat.0))` on an `Exn` function.

        The chain guard is declined for the `Exn` row, so the range check
        evaluates the components itself: it does for the slot reference and
        does not for the call.  One `tier3`, one `tier3_unguarded` — and the
        module carries exactly the one check that pairs with them.
        """
        obs, envelope = _obligations(
            tmp_path, _1222_MIXED_PURITY, name="mix1222.vera")
        bounds = [(o["status"], o.get("error_code"))
                  for o in obs if o["kind"] == "decreases_bound"]
        assert bounds == [("tier3", None), ("tier3_unguarded", "E537")], bounds
        _assert_partition(envelope)

        proc = _cli("compile", "--wat",
                    str(_write(tmp_path, _1222_MIXED_PURITY, "mix1222c.vera")))
        assert proc.returncode == 0, proc.stderr[-400:]
        assert proc.stdout.count("i64 range") == 1, (
            f"expected exactly one range check to pair with the one guarded "
            f"obligation, got {proc.stdout.count('i64 range')}"
        )

    def test_a_rankable_adt_sibling_does_not_decline_the_chain(
        self, tmp_path: Path,
    ) -> None:
        """`decreases(size(@Nat.0), @Tree.0)` with a CONCRETE `Tree`.

        A non-scalar component declines the chain only when the backend
        cannot structurally rank it — the #1177 parameterized-ADT case.  A
        concrete ADT ranks, so the chain is emitted, the measure is evaluated
        once by it, and the call component's purity never arises.  Reading
        "non-scalar" as "declined" put an E537 on a measure the module does
        check.
        """
        obs, envelope = _obligations(
            tmp_path, _1222_RANKABLE_ADT_SIBLING, name="rank1222.vera")
        bounds = [(o["status"], o.get("error_code"))
                  for o in obs if o["kind"] == "decreases_bound"]
        assert bounds == [("tier3", None)], bounds
        _assert_partition(envelope)

        proc = _cli("compile", "--wat",
                    str(_write(tmp_path, _1222_RANKABLE_ADT_SIBLING,
                               "rank1222c.vera")))
        assert proc.returncode == 0, proc.stderr[-400:]
        # BOTH halves: "i64 range" is the standalone measure-range
        # check, which a declined chain would also emit, so on its own
        # it cannot tell this cell's not-declined path from the declined
        # one.  `dec_prev` is the chain guard itself (CR PR-review).
        assert "dec_prev" in proc.stdout, (
            "the chain guard is NOT emitted for a concrete ADT sibling, "
            "so this cell no longer measures the not-declined path"
        )
        assert "i64 range" in proc.stdout

    def test_the_disclosure_names_the_cause_it_actually_had(
        self, tmp_path: Path,
    ) -> None:
        """Two causes, two sentences.

        The unguarded leg told the author of a `pure` function that it had
        been "dropped with an E603", which is the OTHER cause — an effect row
        the backend cannot lower.  A reader following that goes looking for a
        diagnostic that was never emitted.
        """
        proc = _cli("verify", str(_write(
            tmp_path, _1222_MIXED_PURITY, "why1222.vera")))
        out = proc.stdout + proc.stderr
        assert "termination CHAIN guard is declined" in out, out
        assert "dropped with an E603" not in out, (
            f"a `pure`-bodied measure was told its function is E603-dropped:"
            f"\n{out}"
        )


_N4_REFINED_ELEMENT = """\
type Pos = { @Int | @Int.0 > 0 };

public fn f(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Array<Pos> = [@Int.0];
  @Array<Pos>.0[0]
}
"""

_N4_REFINED_ELEMENT_OPAQUE = """\
type Pos = { @Int | @Int.0 > 0 };

public fn f(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Array<Pos> = [handle[Exn<Int>] { throw(@Int) -> { @Int.0 } } in \
{ throw(@Int.0) }];
  @Array<Pos>.0[0]
}
"""

_N4_NAT_ELEMENT = """\
public fn f(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Array<Nat> = [@Int.0];
  nat_to_int(@Array<Nat>.0[0])
}
"""

_N4_WIDEN_CONTROL = """\
public fn ae(@Nat -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Array<Int> = [@Nat.0];
  @Array<Int>.0[0]
}
"""


class TestArrayElementNarrowingIsObligated:
    """An array element narrowed at CONSTRUCTION is on the record.

    Found by the re-verification, and worse than the unguarded sites #1426
    describes: neither narrowing direction was obligated AT ALL.  `vera
    verify` reported a clean program — `ok: true`, no `refine_bind`, no
    `nat_bind` — while `[-4]` was stored into an `@Array<Pos>` and read back
    out.  An unguarded site at least says so; silence cannot be read in
    either direction, and the `-4` differential below is what separates the
    two.

    The cause was refined-first (R9) being absent here: a refinement OVER
    `@Int` answers `_is_int_type`, so the `@Nat` -> `@Int` widening arm — the
    only arm this branch had — swallowed a refined element type and the
    predicate was never asked about.  The `@Nat` narrowing arm was simply
    missing, which left a site whose runtime guard FIRES with no obligation
    to count it: a Tier-3 undercount in the other direction.
    """

    def test_a_refined_element_is_refuted_not_silently_accepted(
        self, tmp_path: Path,
    ) -> None:
        obs, envelope = _obligations(
            tmp_path, _N4_REFINED_ELEMENT, name="n4a.vera")
        binds = [(o["status"], o.get("error_code"))
                 for o in obs if o["kind"] == "refine_bind"]
        assert binds == [("violated", "E505")], obs
        assert envelope["ok"] is False
        _assert_partition(envelope)

    def test_and_the_value_it_refutes_does_flow_out(
        self, tmp_path: Path,
    ) -> None:
        """The run differential that makes the silence a defect.

        Without this the cell above is a claim about a status; with it, the
        status is measured against what the program does.  Nothing guards
        this site — it is one of #1426's — so `-4` is returned, which is
        exactly why the obligation has to exist.
        """
        out = _run(tmp_path, _N4_REFINED_ELEMENT, "--fn", "f", "--", "-4",
                   name="n4b.vera")
        assert out.strip() == "-4", (
            f"expected the unguarded element to flow out, so that the "
            f"obligation is what protects the program:\n{out}"
        )

    def test_an_opaque_refined_element_discloses_rather_than_refutes(
        self, tmp_path: Path,
    ) -> None:
        """The undecided leg, where the guarded flag is actually consulted.

        `tier3_unguarded` + E506, consistent with the other
        construction-position component sites (#1426) — never a `tier3` that
        would claim a runtime check this site does not emit.
        """
        obs, envelope = _obligations(
            tmp_path, _N4_REFINED_ELEMENT_OPAQUE, name="n4c.vera")
        binds = [(o["status"], o.get("error_code"))
                 for o in obs if o["kind"] == "refine_bind"]
        assert binds == [("tier3_unguarded", "E506")], obs
        _assert_partition(envelope)

    def test_a_nat_element_is_obligated_and_its_guard_counted(
        self, tmp_path: Path,
    ) -> None:
        """The other direction, where a guard exists and had no obligation.

        The trap below is real, but it belongs to the READ, not to the
        store: the fixture ends in `nat_to_int(...[0])`, and the #765
        pattern-bind guard fires there.  The construction site itself plants
        nothing — see the store-only cell in
        :py:class:`TestConstructionPositionReachesNestedContainers`, where
        `-4` is stored into an `@Array<Nat>` and the program returns
        normally — so this obligation is recorded UNguarded.  The earlier
        reading of this cell took the trap as evidence about the store and
        claimed `guarded`, which asserted a runtime check the site does not
        emit.
        """
        obs, envelope = _obligations(
            tmp_path, _N4_NAT_ELEMENT, name="n4d.vera")
        binds = [(o["status"], o.get("error_code"))
                 for o in obs if o["kind"] == "nat_bind"]
        assert binds == [("violated", "E503")], obs
        _assert_partition(envelope)

        out = _run(tmp_path, _N4_NAT_ELEMENT, "--fn", "f", "--", "-4",
                   name="n4e.vera")
        assert _NAT_GUARD_TRAP in out, (
            f"the `@Nat` element store does not trap, so the obligation's "
            f"guarded flag is wrong:\n{out}"
        )

    def test_the_element_store_itself_plants_no_guard(
        self, tmp_path: Path,
    ) -> None:
        """Store-only: the differential that separates store from read.

        A fixture that reads the element back cannot answer where the guard
        lives, because the read-side bind guard (#765) answers first.  This
        one never reads: `-4` goes into an `@Array<Nat>` and `f` returns
        `1`.  That is why the construction obligation is recorded UNguarded
        — claiming otherwise would assert a check that is not in the WAT.
        """
        out = _run(tmp_path, _P1_NAT_ELEMENT_STORE_ONLY, "--fn", "f", "--",
                   "-4", name="p1g.vera")
        assert out.strip() == "1", (
            f"expected the store-only program to complete, showing the "
            f"element store plants no guard:\n{out}"
        )
        obs, envelope = _obligations(
            tmp_path, _P1_NAT_ELEMENT_STORE_ONLY, name="p1h.vera")
        binds = [(o["status"], o.get("error_code"))
                 for o in obs if o["kind"] == "nat_bind"]
        assert binds == [("violated", "E503")], obs
        _assert_partition(envelope)

    def test_the_widening_arm_still_fires(self, tmp_path: Path) -> None:
        """The over-reach control.

        Routing refined-first must not take the `@Nat` -> `@Int` widening
        element off the record — #820 guards that store and its obligation
        counts the guard.
        """
        obs, _ = _obligations(tmp_path, _N4_WIDEN_CONTROL, name="n4f.vera")
        coerce = [(o["status"], o.get("error_code"))
                  for o in obs if o["kind"] == "nat_to_int_coerce"]
        assert coerce == [("tier3", None)], obs


# The two closure-argument fixtures differ in EXACTLY one token — the payload
# carrier the `Taker` formal writes `PosInt` inside — so the pair isolates the
# type half of the derivation from the site half.  Both make the argument
# opaque the same way, by producing it from another closure: a lifted body is
# outside the outer slot environment, so the payload predicate can be neither
# discharged nor refuted and the obligation lands at Tier 3, which is the only
# place the `guarded` flag is read at all.  A `violated` never consults it.
_A1_CLOSURE_OPTION = """\
type PosInt = { @Int | @Int.0 > 0 };
type Maker = fn(Int -> Option<Int>) effects(pure);
type Taker = fn(Option<PosInt> -> Int) effects(pure);

public fn f(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Maker = fn(@Int -> @Option<Int>) effects(pure) { Some(@Int.0) };
  let @Taker = fn(@Option<PosInt> -> @Int) effects(pure) { 1 };
  apply_fn(@Taker.0, apply_fn(@Maker.0, @Int.0))
}
"""

_A1_CLOSURE_TUPLE = """\
type PosInt = { @Int | @Int.0 > 0 };
type Maker = fn(Int -> Tuple<Int, Int>) effects(pure);
type Taker = fn(Tuple<PosInt, Int> -> Int) effects(pure);

public fn f(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Maker = fn(@Int -> @Tuple<Int, Int>) effects(pure) { Tuple(@Int.0, 5) };
  let @Taker = fn(@Tuple<PosInt, Int> -> @Int) effects(pure) { 1 };
  apply_fn(@Taker.0, apply_fn(@Maker.0, @Int.0))
}
"""

#: The closure prologue's own component guard, measured from the trap.  It
#: names the CLOSURE's rendered signature rather than a caller's, which is
#: what pins the check to the boundary the obligation points at.
_A1_TUPLE_TRAP_SITE = "Refinement violation in fn(@Tuple<@PosInt, @Int> -> @Int)"
_A1_TUPLE_TRAP_WHAT = "parameter (tuple component): @Int.0 > 0 failed"


class TestClosureArgumentNestedGuardednessIsTypeDerived:
    """A closure argument's guardedness is the SITE half AND the TYPE half.

    "closure argument" is in `_REFINED_BIND_GUARDED_SITES`, so the site half
    answers True for both cells below.  That alone is not the answer: codegen
    decomposes a refined formal at a boundary through TUPLES and nothing else
    (`_emit_component_refinement_guards`), so where the refinement sits INSIDE
    the formal's type decides whether any check is emitted for it.  The verifier
    intersects the two — `_refined_bind_site_guarded(site) and
    _nested_refinements_guarded(formal_ty)` — and these cells pin that second
    conjunct at the one position where it is actually read.

    The pair is a differential, not two independent claims.  The fixtures are
    identical apart from the carrier the `Taker` formal writes `PosInt` inside,
    `Option<PosInt>` against `Tuple<PosInt, Int>`, so a derivation that dropped
    the type half and answered from the roster alone would call BOTH guarded —
    and the `Option` cell's run is the evidence that would be a false promise:
    `-4` crosses the boundary and `f` returns normally, with no check anywhere
    to fulfil a `tier3`.  That is #1362's misclassification exactly, which is
    why the status is measured against what the program does rather than on its
    own.

    Both obligations carry E506.  The code is not the discriminator here — a
    `tier3` carries the informational "will be checked at run time" wording
    under the same code the unguarded warning uses — so the STATUS is what
    separates them, and both are asserted as a pair so neither can drift alone.
    """

    def test_an_option_payload_formal_records_the_unguarded_tier3(
        self, tmp_path: Path,
    ) -> None:
        """`Option<PosInt>`: the type half says no, so the status must too.

        Codegen's boundary decomposition never opens an `Option`, so the
        refinement on its payload reaches no guard.  `tier3_unguarded` + E506
        is the honest record; a plain `tier3` would claim a runtime check that
        the companion run below shows does not exist.
        """
        obs, envelope = _obligations(
            tmp_path, _A1_CLOSURE_OPTION, name="a1a.vera")
        binds = [(o["status"], o.get("error_code"))
                 for o in obs if o["kind"] == "refine_bind"]
        assert binds == [("tier3_unguarded", "E506")], obs
        _assert_partition(envelope)

    def test_and_the_option_payload_crosses_the_boundary_unchecked(
        self, tmp_path: Path,
    ) -> None:
        """The run that makes the status above a measurement.

        `-4` is chosen because no fallback can coincide with it: a clamp to
        zero would still violate `> 0`, so a trap here could only come from a
        real guard.  None fires — `f` returns the closure's `1` and exits 0 —
        which is precisely what `tier3_unguarded` reports.
        """
        out = _run(tmp_path, _A1_CLOSURE_OPTION, "--fn", "f", "--", "-4",
                   name="a1b.vera")
        assert out.strip() == "1", (
            f"expected the unguarded `Option` payload to cross the closure "
            f"boundary and the program to run on:\n{out}"
        )
        assert "Refinement violation" not in out, (
            f"a guard fired at a boundary the obligation records as "
            f"unguarded, so the status is wrong in the other direction:\n{out}"
        )

    def test_a_tuple_component_formal_records_the_guarded_tier3(
        self, tmp_path: Path,
    ) -> None:
        """`Tuple<PosInt, Int>`: the one carrier the decomposition reaches.

        Same site, same opaque producer, same predicate — only the carrier
        differs, and with it the type half.  `tier3` (counted in the totals)
        rather than `tier3_unguarded`, because here the promised check is
        real; the next cell runs it.
        """
        obs, envelope = _obligations(
            tmp_path, _A1_CLOSURE_TUPLE, name="a1c.vera")
        binds = [(o["status"], o.get("error_code"))
                 for o in obs if o["kind"] == "refine_bind"]
        assert binds == [("tier3", "E506")], obs
        assert envelope["verification"]["tier3_runtime"] == 1, envelope
        _assert_partition(envelope)

    def test_and_the_tuple_component_traps_at_the_closure_prologue(
        self, tmp_path: Path,
    ) -> None:
        """The guard the `tier3` promises, run.

        The trap text is asserted rather than the exit code, because an exit
        code cannot say WHICH check fired.  It names the closure's own
        signature and the tuple-component parameter position, so the check is
        the one at the boundary the obligation points at — not a producer's
        return guard standing in for it, which is the confound a refined-return
        producer would have introduced here.
        """
        out = _run(tmp_path, _A1_CLOSURE_TUPLE, "--fn", "f", "--", "-4",
                   name="a1d.vera")
        assert _A1_TUPLE_TRAP_SITE in out, (
            f"the `tier3` promises a runtime check at the closure boundary "
            f"and none fired there:\n{out}"
        )
        assert _A1_TUPLE_TRAP_WHAT in out, out

        ok = _run(tmp_path, _A1_CLOSURE_TUPLE, "--fn", "f", "--", "7",
                  name="a1e.vera")
        assert ok.strip() == "1", (
            f"the guard rejects a satisfying component, so the trap above "
            f"witnesses nothing about the predicate:\n{ok}"
        )


_A2_CALL_RESULT_OPERAND = """\
type PosInt = { @Int | @Int.0 > 0 };
type Taker = fn(Option<PosInt> -> Int) effects(pure);

public fn mkint(@Int -> @Option<Int>)
  requires(true)
  ensures(true)
  effects(pure)
{
  Some(@Int.0)
}

public fn taker(@Unit -> @Taker)
  requires(true)
  ensures(true)
  effects(pure)
{
  fn(@Option<PosInt> -> @Int) effects(pure) { 1 }
}

public fn f(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  apply_fn(taker(()), mkint(@Int.0))
}
"""


class TestCallResultClosureOperandIsPinnedNotClaimed:
    """A closure OPERAND that is a call result does not reach the
    closure-argument arm — pinned with the reason it is harmless (A2).

    `apply_fn(taker(()), mkint(x))` names its closure through a CALL rather
    than a slot, and the arm that raises the closure-argument obligation
    reads the operand's declared function type from the slot.  So no
    `refine_bind` is recorded, and `verify` reports `ok: true` for a program
    whose payload the formal's `Option<PosInt>` forbids.

    That is a real gap in the obligation, and it is unreachable at run time
    today for a reason that has nothing to do with the guard: code
    generation cannot compile this shape and drops the enclosing function
    with `E602`, so the module contains no `f` to run.  The pin is the
    CONJUNCTION — the obligation is absent AND the function is dropped.  If
    codegen later learns this shape, the second half fails and the gap stops
    being harmless, which is exactly when someone needs to be told.  A cell
    asserting only the absence would go on passing.
    """

    def test_the_arm_is_not_reached_for_a_call_result_operand(
        self, tmp_path: Path,
    ) -> None:
        obs, envelope = _obligations(
            tmp_path, _A2_CALL_RESULT_OPERAND, name="a2a.vera")
        binds = [(o["status"], o.get("error_code"))
                 for o in obs if o["kind"] == "refine_bind"]
        assert binds == [], (
            f"the closure-argument arm now reaches a call-result operand — "
            f"good, but this cell pinned its ABSENCE, so re-derive the pin "
            f"from what it does now: {binds}"
        )
        assert envelope["ok"] is True, envelope
        _assert_partition(envelope)

    def test_and_the_enclosing_function_is_dropped_so_nothing_runs(
        self, tmp_path: Path,
    ) -> None:
        """The half that makes the gap above harmless, asserted separately.

        Read from the ARTIFACT: `f` must be absent from the emitted module.
        A message-text check would pass on a build that printed the E602
        note and emitted the function anyway.
        """
        proc = _cli("compile", "--wat",
                    str(_write(tmp_path, _A2_CALL_RESULT_OPERAND,
                               "a2b.vera")))
        assert proc.returncode == 0, proc.stderr
        assert '(export "f"' not in proc.stdout, (
            "codegen now emits `f` for a call-result closure operand, so the "
            "missing closure-argument obligation is no longer unreachable: "
            "the arm has to reach this operand shape"
        )
        assert '(export "taker"' in proc.stdout, (
            "the module lost more than `f`, so its absence is not evidence "
            "about this shape"
        )


_CR_REFINED_INT_ELEMENT = """\
type NonNeg = { @Int | @Int.0 >= 0 };

public fn f(@Nat -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Array<NonNeg> = [@Nat.0];
  @Array<NonNeg>.0[0]
}
"""

_CR_PLAIN_INT_ELEMENT = """\
public fn f(@Nat -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Array<Int> = [@Nat.0];
  @Array<Int>.0[0]
}
"""


class TestARefinedIntElementCountsItsWideningGuardToo:
    """A refined `@Int` element records the RANGE obligation beside the
    predicate one (CR PR-review).

    Routing refined-FIRST fixed the swallowed predicate and introduced the
    opposite error at the same site: the refined arm returned, so an
    `@Array<{ @Int | ... }>` element fed a `@Nat` recorded only
    `refine_bind`.  Code generation does not distinguish the two — it
    resolves the refined element target to `@Int` and emits the same
    widening guard it emits for a plain one — so the site had a guard that
    fires with nothing counting it.  That is a Tier-3 UNDERcount, the same
    defect as the overcount in the other direction and just as much a
    verifier/codegen desync.

    The two obligations are about different things and neither implies the
    other: the predicate is about the VALUE, the widening check about the
    REPRESENTATION a `@Nat` above `i64.MAX` takes when it is reinterpreted
    as a signed `i64`.  A `@Nat` narrowing twin is deliberately absent — a
    refinement over `@Nat` discharges its full predicate on the refined arm,
    which already implies `>= 0`.
    """

    def test_the_refined_element_records_both_obligations(
        self, tmp_path: Path,
    ) -> None:
        obs, envelope = _obligations(
            tmp_path, _CR_REFINED_INT_ELEMENT, name="cr4a.vera")
        kinds = [(o["kind"], o["status"]) for o in obs
                 if o["kind"] in ("refine_bind", "nat_to_int_coerce")]
        assert ("nat_to_int_coerce", "tier3") in kinds, (
            f"the widening guard the module emits here is counted by no "
            f"obligation: {kinds}"
        )
        assert ("refine_bind", "verified") in kinds, kinds
        _assert_partition(envelope)

    def test_and_the_module_really_does_guard_it(
        self, tmp_path: Path,
    ) -> None:
        """The differential that makes the missing record a defect.

        The plain `@Array<Int>` element is the control: #820 guards its
        store and `nat_to_int_coerce` counts that guard.  The refined
        element compiles to the SAME number of traps in `f`, which is what
        says the guard is there — so an obligation stream that mentioned it
        only in the plain case was describing two different programs.
        """
        def traps(source: str, name: str) -> int:
            proc = _cli("compile", "--wat",
                        str(_write(tmp_path, source, name)))
            assert proc.returncode == 0, proc.stderr[-400:]
            body, _, rest = proc.stdout.partition("(func $f ")
            assert rest, "no `f` in the emitted module"
            return rest.split("\n  )")[0].count("unreachable")

        plain = traps(_CR_PLAIN_INT_ELEMENT, "cr4b.vera")
        refined = traps(_CR_REFINED_INT_ELEMENT, "cr4c.vera")
        assert plain > 0, "the control emits no guard, so it controls nothing"
        assert refined == plain, (
            f"the refined element emits {refined} traps and the plain one "
            f"{plain}; this cell's premise is that codegen treats them alike"
        )


_Q1_REFINED_OVER_REFINED_LET = """\
type Pos = { @Int | @Int.0 > 0 };
type Tiny = { @Pos | @Pos.0 < 10 };

public fn mk(@Int -> @Pos)
  requires(@Int.0 > 0)
  ensures(true)
  effects(pure)
{
  @Int.0
}

public fn f(@Int -> @Int)
  requires(@Int.0 > 0)
  ensures(true)
  effects(pure)
{
  let @Tiny = mk(@Int.0);
  @Tiny.0
}
"""


class TestTheUnguardedRationaleNamesTheCauseThatApplies:
    """The E506 closing sentence must not blame a site #765 guards.

    A `let @Tiny = mk(...)` whose base is itself a refinement lands here for
    a TYPE reason: `_emit_bind_refine_guard` will not lower a guard for a
    refinement-over-refinement base.  The site is fine — `"let binding"` is
    in `_REFINED_BIND_GUARDED_SITES`.  The sentence that used to close this
    warning said the guard lives only at a function boundary "not at this
    internal narrowing site", which was true before #765 and false after,
    and it sent a reader to move a binding that has no reason to move.

    This cell exists because that text was fixed once and LOST to a rebase:
    #1420 parameterised the closing sentence, the merge kept the new
    parameter with its pre-#765 default, and the corrected wording went with
    it.  A reviewed text fix that nothing asserts is one merge away from
    being un-fixed, so the assertion is the pin — it fails on the regression
    rather than waiting for the next reviewer to re-read the paragraph.
    """

    def test_the_rationale_offers_both_causes(self, tmp_path: Path) -> None:
        proc = _cli("verify", "--json",
                    str(_write(tmp_path, _Q1_REFINED_OVER_REFINED_LET,
                               "q1a.vera")))
        envelope = json.loads(proc.stdout)
        e506 = [w for w in envelope["warnings"]
                if w.get("error_code") == "E506"]
        assert len(e506) == 1, envelope["warnings"]
        rationale = e506[0]["rationale"]
        assert "SITE is" in rationale and "BASE is" in rationale, (
            f"the closing sentence names one cause where two apply, so a "
            f"reader cannot tell which half to change:\n{rationale}"
        )

    def test_and_does_not_blame_a_site_that_is_guarded(
        self, tmp_path: Path,
    ) -> None:
        """The half that actually regressed, asserted on its own.

        Kept separate from the cell above so the failure names the defect:
        a rationale could name both causes and still carry the stale
        internal-site clause beside them.
        """
        proc = _cli("verify", "--json",
                    str(_write(tmp_path, _Q1_REFINED_OVER_REFINED_LET,
                               "q1b.vera")))
        envelope = json.loads(proc.stdout)
        rationale = next(w["rationale"] for w in envelope["warnings"]
                         if w.get("error_code") == "E506")
        assert "internal narrowing site" not in rationale, (
            f"a `let` bind is runtime-guarded since #765, so calling it an "
            f"unguarded internal site is false:\n{rationale}"
        )

    def test_the_bind_is_recorded_unguarded_for_the_type_not_the_site(
        self, tmp_path: Path,
    ) -> None:
        """The status behind the sentence, so the pin is not text-only.

        `tier3_unguarded` is correct here — no guard is emitted — and the
        cause is the base, which is what the wording has to convey.
        """
        obs, envelope = _obligations(
            tmp_path, _Q1_REFINED_OVER_REFINED_LET, name="q1c.vera")
        binds = [(o["status"], o.get("error_code"))
                 for o in obs if o["kind"] == "refine_bind"]
        assert ("tier3_unguarded", "E506") in binds, obs
        _assert_partition(envelope)

