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

_U64_MAX = "18446744073709551615"


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
        assert "unreachable" in out, (
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
