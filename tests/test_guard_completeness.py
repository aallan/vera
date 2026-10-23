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
  prover reasons over unbounded integers.  A `@Nat` holds `0 .. i64.MAX`
  (v0.2.3), so the two readings agree on every `@Nat` measure, and the
  range check this site had on the u64 `Nat` is gone.

Every cell here is the issue's own reproducer, run on a value chosen so that
no fallback can coincide with the right answer: a NEGATIVE `Int` into every
`@Nat` slot (a clamp to zero would read as success), and a refinement
violation a clamp cannot repair.  Each asserts the TRAP or the guard's own
diagnostic, never a length or an exit code.
"""

from __future__ import annotations

from pathlib import Path

import pytest

from tests import pipeline

#: The bound each call below that this file makes to the pipeline had as a
#: `vera` process; in process it is the call's budget (tests/pipeline.py).
_BUDGET_S = 300


def _write(tmp_path: Path, source: str, name: str = "p.vera") -> Path:
    p = tmp_path / name
    p.write_text(source, encoding="utf-8")
    return p


def _compiled(tmp_path: Path, source: str, name: str) -> pipeline.Compiled:
    """*source*, written to a file, compiled as ``vera compile`` compiles it."""
    compiled = pipeline.compile(_write(tmp_path, source, name), budget_s=_BUDGET_S)
    assert compiled.ok, [d.description[:200] for d in compiled.errors]
    return compiled


def _run(tmp_path: Path, source: str, *args: str, name: str = "p.vera") -> str:
    """`vera run` on *source*, returning stdout+stderr.

    Both streams, because the two outcomes a cell distinguishes live on
    different ones: a value on stdout, a trap message on stderr.
    """
    proc = pipeline.cli("run", str(_write(tmp_path, source, name)), *args, budget_s=_BUDGET_S)
    return proc.stdout + proc.stderr


def _obligations(tmp_path: Path, source: str,
                 name: str = "p.vera") -> tuple[list[dict], dict]:
    """What ``vera verify --json`` prints for *source*, and its obligations:
    the verify stage's envelope."""
    envelope = pipeline.verify(_write(tmp_path, source, name),
                               budget_s=_BUDGET_S).envelope()
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
_I64_MAX = "9223372036854775807"
_I64_MAX_PLUS_1 = "9223372036854775808"

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

    def test_a_nat_at_the_top_of_its_range_into_a_generic_int_field(
        self, tmp_path: Path,
    ) -> None:
        """The widening dual, at the value that distinguishes it.

        i64.MAX is the largest `@Nat`, and it comes back as itself; a value
        above it is no `@Nat` and is refused before the call.  On the u64
        `Nat`, u64.MAX was the input that distinguished a guard, and
        unguarded it returned -1.
        """
        out = _run(tmp_path, _757_WIDEN, "--fn", "gf", "--", _I64_MAX,
                   name="w757.vera")
        assert out.strip() == _I64_MAX, out
        over = _run(tmp_path, _757_WIDEN, "--fn", "gf", "--", _U64_MAX,
                    name="w757u.vera")
        assert "out of range for parameter type @Nat" in over, over
        out_ok = _run(tmp_path, _757_WIDEN, "--fn", "gf", "--", "42",
                      name="w757ok.vera")
        assert out_ok.strip() == "42", out_ok

    def test_the_widening_has_nothing_to_check(self, tmp_path: Path) -> None:
        """A `@Nat` is an `@Int` at the value level: the stream records
        nothing at the widening, and the module checks nothing there."""
        obs, envelope = _obligations(tmp_path, _757_WIDEN, name="ob757.vera")
        assert [(o["kind"], o["status"]) for o in obs] == [
            ("requires", "verified"), ("ensures", "verified")], obs
        _assert_partition(envelope)
        assert _compiled(tmp_path, _757_WIDEN, "c757.vera").checks() == ()


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
        compiled = _compiled(tmp_path, _1036_FN_ARG_BASE, "fnarg.vera")
        assert compiled.checks(kind="contract_violation"), (
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

        A row naming a user-declared effect is refused at check (E340,
        #1681), so there is no run for a guard to protect.  The verifier's
        classification intersects the formal's base with
        `narrowing.COMPILABLE_EFFECTS`, the roster codegen itself decides
        compilability from, so that recording `guarded` cannot repeat
        #1268's mistake one boundary over; every built-in effect is in the
        roster, so only a refused program could reach the other branch, and
        no stage after the check runs on a program it refuses.
        """
        checked = pipeline.check(_754_USER_EFFECT)
        assert [d.error_code for d in checked.errors] == ["E340"], [
            (d.error_code, d.description) for d in checked.errors]

        proc = pipeline.cli("compile", "--wat",
                            str(_write(tmp_path, _754_USER_EFFECT, "user754c.vera")), budget_s=_BUDGET_S)
        assert "E340" in (proc.stdout + proc.stderr), (
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
                proc = pipeline.cli(
                    "check",
                    str(_write(tmp_path, src, f"bare_{eff_name}_{op_name}.vera")), budget_s=_BUDGET_S)
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
    was the one it did not give.  The guard now signals `nat_guard` before
    its `unreachable`, through the channel #808 built for arithmetic
    overflow — one `vera.trap` import for every kind since #1479.
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
        and a lifted closure's.  This drives a guard emitted only inside a
        lifted body.  Since #1479 a closure's module also declares the
        signal for its allocator, so this cell no longer isolates the
        closure merge; `tests/test_named_traps_1479.py`'s fan-in cells do,
        with a check whose import no allocation declares.
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
        compiled = _compiled(tmp_path, source, "sig754.vera")
        assert 'import "vera" "trap"' in compiled.wat, (
            "the guard inside the lifted closure calls the signal, but the "
            "module does not declare the import"
        )
        assert compiled.checks(kind="nat_guard")


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


class TestANatMeasureIsAnI64_1222:
    """The termination proof and the termination check agree on the value.

    The proof reasons over unbounded integers; the runtime guard compares
    with `i64.lt_s` / `i64.ge_s`.  A `@Nat` holds `0 .. i64.MAX`, so the two
    readings agree on every value a `@Nat` measure can take.  On the u64
    `Nat` a measure above `i64.MAX` read negative in the guard, and a range
    check of its own (`decreases_bound`, E536, E537) held it to the guard's
    range.
    """

    def test_the_top_of_the_range_runs_and_past_it_is_refused(
        self, tmp_path: Path,
    ) -> None:
        """i64.MAX runs; i64.MAX + 1 is no `@Nat`, refused before the call."""
        ok = _run(tmp_path, _1222_UNBOUNDED, "--fn", "halve", "--", _I64_MAX,
                  name="d1222a.vera")
        assert ok.strip() == "0", (
            f"a measure AT i64.MAX must still run:\n{ok}"
        )
        over = _run(tmp_path, _1222_UNBOUNDED, "--fn", "halve", "--",
                    _I64_MAX_PLUS_1, name="d1222b.vera")
        assert "out of range for parameter type @Nat" in over, over

    def test_the_termination_proof_stands_alone(self, tmp_path: Path) -> None:
        obs, envelope = _obligations(
            tmp_path, _1222_UNBOUNDED, name="d1222v.vera")
        assert [(o["kind"], o["status"]) for o in obs] == [
            ("requires", "verified"), ("ensures", "verified"),
            ("decreases", "verified")], obs
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
    probe = pipeline.compile(source, file="fixture.vera")
    _ = probe.parsed.program  # raises the parse or transform error
    assert probe.checked is not None
    errors = list(probe.checked.errors)
    assert not errors, f"the probe does not type-check: {errors}"
    compiled = probe.result
    cg_errors = [d for d in compiled.diagnostics if d.severity == "error"]
    assert not cg_errors, f"the probe does not compile: {cg_errors}"
    try:
        ran = pipeline.run(compiled, fn, args, capture_stderr=False)
    except Exception as exc:  # noqa: BLE001 — the trap IS the observation
        return str(exc)
    if ran.trap is not None:
        return str(ran.trap)
    return "ran"


def _guard_mutations() -> list[tuple]:
    """(label, owner, method, neutered, probe, with_guard, without_guard).

    Each probe is a program the guard exists to stop, run on the value it
    exists to catch; the last two are substrings the observation must
    contain WITH the guard and WITHOUT it.  They differ for every entry,
    which is the whole content of the check.
    """
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


# ===========================================================================
# #1416 — the two Tuple-component sites, from this PR's own review round
# ===========================================================================

# The narrowing at CONSTRUCTION.  On the u64 `Nat` its widening twin at the
# same site read the checker's target-type table since #820; this arm never
# did, so one field could be guarded and its neighbour not, at one
# construction.
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

    Each shape is now guarded at its own store as well as obligated there,
    and the run cells say which guard traps: the flat stores by #1426 and
    #1440, the nested ones because a nested literal takes its type from the
    position it stands in (R-1412 F3).  Before, none had an obligation,
    which was the defect — silence cannot be read in either direction.
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

    def test_and_the_nested_element_is_caught_at_its_store(
        self, tmp_path: Path,
    ) -> None:
        """The run differential that names WHERE the check lives.

        Unlike the two tuple/`Option` shapes below, the inner element is
        read back as a plain projection, so no pattern bind guards it: when
        this cell was written `-4` was returned from a function whose element
        type forbids it.  #1426 guarded the flat element store, and the
        nested literal now receives its element type from the position it
        stands in (R-1412 F3), so its own store traps.
        """
        out = _run(tmp_path, _P1_NESTED_ARRAY, "--fn", "f", "--", "-4",
                   name="p1b.vera")
        assert "Refinement violation in array element store" in out, out

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

    def test_the_refined_map_value_is_caught_at_the_insert(
        self, tmp_path: Path,
    ) -> None:
        """The differential that names WHERE the check lives.

        When this cell was written the insert planted nothing and the trap
        arrived at the `Some(@Pos)` sub-pattern on the way back out (#765),
        which is why the obligation had to exist at the insert: a program
        that inserted and never read kept the forbidden value.  #1426 gives
        the insert its own guard, so the trap now names THAT site — earlier,
        and on the store-only programs the read-side guard never saw.
        """
        out = _run(tmp_path, _P1_MAP_REFINED_VALUE, "--fn", "f", "--", "-4",
                   name="p1d.vera")
        assert "Refinement violation in map value insert" in out, out

    def test_a_nat_map_value_is_obligated_and_guarded(
        self, tmp_path: Path,
    ) -> None:
        """`Map<String, Nat>`: the insert is obligated AND checked.

        When this cell was written nothing guarded the insert, so the
        record disclosed E504 and the store-only differential — `-4`
        inserted, `f` returning `1` — was what proved the disclosure
        honest.  #1440 gave the insert its guard, so the same differential
        now shows the trap.
        """
        obs, envelope = _obligations(
            tmp_path, _P1_MAP_NAT_VALUE, name="p1e.vera")
        binds = [(o["status"], o.get("error_code"))
                 for o in obs if o["kind"] == "nat_bind"]
        assert binds == [("violated", "E503")], obs
        _assert_partition(envelope)

        out = _run(tmp_path, _P1_MAP_NAT_VALUE, "--fn", "f", "--", "-4",
                   name="p1f.vera")
        assert _NAT_GUARD_TRAP in out, (
            f"the insert accepted `-4` into a `@Nat` map value.  When this "
            f"cell was written it did, and the obligation's unguarded flag "
            f"said so honestly; #1440 gave the store its guard:\n{out}"
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

        # The tuple inside the array literal is typed from the element
        # position (R-1412 F3), so its own store traps before the `let`
        # destructure that caught it when this cell was written.
        out = _run(tmp_path, _P1_ARRAY_OF_REFINED_TUPLES, "--fn", "f", "--",
                   "-4", name="p1j.vera")
        assert "Refinement violation in Tuple(…) construction" in out, out

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

    The destructure half was observable on the u64 `Nat` — it returned a
    reinterpreted `-1`.
    The construction half was not: every consumer path is itself guarded (a
    callee's parameter component check, a return component check, the
    destructure), so the negative could not escape. What it was, was an
    obligation claiming `tier3_unguarded` at a site the composition covered
    — a disclosure pointing at the wrong place. Guarding the store makes the
    site's own claim true rather than borrowing its neighbours'.
    """

    def test_the_destructure_widening_reads_the_top_of_the_range(
        self, tmp_path: Path,
    ) -> None:
        """i64.MAX, the largest `@Nat`, read out of a tuple component into
        an `@Int` binding comes back as itself, with nothing recorded or
        checked at the widening.  On the u64 `Nat`, u64.MAX came back
        reinterpreted, and then guarded."""
        out = _run(tmp_path, _1416_DESTRUCTURE, "--fn", "td", "--", _I64_MAX,
                   name="d1416.vera")
        assert out.strip() == _I64_MAX, out
        ok = _run(tmp_path, _1416_DESTRUCTURE, "--fn", "td", "--", "42",
                  name="d1416ok.vera")
        assert ok.strip() == "42", ok
        obs, envelope = _obligations(
            tmp_path, _1416_DESTRUCTURE, name="d1416_ob.vera")
        assert [(o["kind"], o["status"]) for o in obs] == [
            ("requires", "verified"), ("ensures", "verified")], obs
        _assert_partition(envelope)
        assert _compiled(tmp_path, _1416_DESTRUCTURE,
                         "d1416c.vera").checks() == ()

    def test_the_construction_narrowing_is_guarded_at_the_store(
        self, tmp_path: Path,
    ) -> None:
        """Read from the module, because the value cannot escape to be run.

        Every consumer of the tuple guards it again, so a run cannot separate
        "the store is guarded" from "the read is". The store's own guard is
        what the obligation claims, so the store is what is measured.
        """
        compiled = _compiled(tmp_path, _1416_CONSTRUCT, "c1416.vera")
        assert compiled.checks(kind="nat_guard"), (
            "the `@Int` component stored into a `Tuple<Nat, Int>` carries no "
            "narrowing guard"
        )

    @pytest.mark.parametrize(
        ("label", "source", "kind"),
        [
            ("construct", _1416_CONSTRUCT, "nat_bind"),
        ],
        ids=["construct"],
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


class TestADeclinedChainGuardDoesNotRunTheMeasure1222:
    """The decline path may not make an extra evaluation observable.

    Found by CodeRabbit on PR #1290.  Where the chain guard is declined
    nothing may evaluate the measure at entry: for an effectful component
    that would be a new action, before the body.  Measured on the u64 `Nat`,
    whose measure range check evaluated the component itself:
    `decreases(risky(@Nat.0))` on a function declaring `Exn<Int>`, where
    `risky` throws on zero, turned a program that returned 0 into one that
    threw.
    """

    def test_the_program_still_returns_rather_than_throwing(self) -> None:
        """A measure is held to purity (#1708), so the check refuses this
        one (E187), and no stage after the check runs on a program it
        refuses: an effectful measure never reaches code generation."""
        checked = pipeline.check(_1222_EFFECTFUL_MEASURE)
        assert [d.error_code for d in checked.errors] == ["E187"], [
            (d.error_code, d.description) for d in checked.errors]


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


class TestARankableAdtSiblingKeepsTheChainGuard1222:
    """A non-scalar measure component declines the chain guard only when the
    backend cannot structurally rank it — the #1177 parameterized-ADT case.
    A concrete ADT ranks, so the chain is emitted."""

    def test_a_rankable_adt_sibling_does_not_decline_the_chain(
        self, tmp_path: Path,
    ) -> None:
        """`decreases(size(@Nat.0), @Tree.0)` with a CONCRETE `Tree`."""
        proc = pipeline.cli("compile", "--wat",
                            str(_write(tmp_path, _1222_RANKABLE_ADT_SIBLING,
                                       "rank1222c.vera")), budget_s=_BUDGET_S)
        assert proc.returncode == 0, proc.stderr[-400:]
        assert "dec_prev" in proc.stdout, (
            "the chain guard is NOT emitted for a concrete ADT sibling"
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

    def test_and_the_value_it_refutes_is_refused_at_the_store(
        self, tmp_path: Path,
    ) -> None:
        """The run differential that makes the status a fact about the run.

        When this cell was written nothing guarded the site — `-4` came back
        out of a function whose element type forbids it — and the obligation
        was all that stood between the program and a value its own type
        rules out.  #1426 gives the element store the §2.6.5 guard, so the
        value is refused where it goes in.  The cell keeps its force either
        way: it fails if the program returns the forbidden value.
        """
        out = _run(tmp_path, _N4_REFINED_ELEMENT, "--fn", "f", "--", "-4",
                   name="n4b.vera")
        assert "Refinement violation in array element store" in out, (
            f"the element store accepted a value its type forbids:\n{out}"
        )
        assert out.strip() != "-4", out

    def test_an_opaque_refined_element_discloses_rather_than_refutes(
        self, tmp_path: Path,
    ) -> None:
        """The undecided leg, where the guarded flag is actually consulted.

        `tier3` + E506 since #1426 gave this store a guard: the flag says a
        runtime check covers it, and one does.  It read `tier3_unguarded`
        when the cell was written, which was equally truthful then — the
        point of the cell is that the flag tracks the module, not that it
        holds one particular value.
        """
        obs, envelope = _obligations(
            tmp_path, _N4_REFINED_ELEMENT_OPAQUE, name="n4c.vera")
        binds = [(o["status"], o.get("error_code"))
                 for o in obs if o["kind"] == "refine_bind"]
        assert binds == [("tier3", "E506")], obs
        _assert_partition(envelope)

    def test_a_nat_element_is_obligated_and_its_guard_counted(
        self, tmp_path: Path,
    ) -> None:
        """The other direction, where a guard existed with no obligation.

        The `@Nat` arm was absent at the `ArrayLit` walk outright, so this
        store's sign narrowing was counted by nobody.  It is recorded now,
        and `-4` traps — but this fixture cannot say WHICH check trapped,
        because it ends in `nat_to_int(...[0])` and the read-side
        pattern-bind guard (#765) fires there too.
        :py:meth:`test_the_element_store_itself_guards` below is the
        store-only differential that localizes it: when this cell was
        written that differential returned normally, which is why the
        obligation was recorded UNguarded, and #1440 is what changed the
        answer.  So the trap below is evidence that SOME check covers
        `-4` — never, on its own, evidence about the store.
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
            f"`-4` reached an `@Array<Nat>` element with no check anywhere: "
            f"neither the store's sign guard (#1440) nor the read-side "
            f"pattern-bind guard (#765) fired:\n{out}"
        )

    def test_the_element_store_itself_guards(
        self, tmp_path: Path,
    ) -> None:
        """Store-only: the differential that separates store from read.

        A fixture that reads the element back cannot answer where the guard
        lives, because the read-side bind guard (#765) answers first.  This
        one never reads, which is what makes it the proof that #1440
        landed: when it was written `-4` went into an `@Array<Nat>` and `f`
        returned `1`, and the obligation was recorded UNguarded because
        that is what the module did.  The store has its own guard now, so
        the same differential shows the trap.
        """
        out = _run(tmp_path, _P1_NAT_ELEMENT_STORE_ONLY, "--fn", "f", "--",
                   "-4", name="p1g.vera")
        assert _NAT_GUARD_TRAP in out, (
            f"the element store accepted `-4` into an `@Array<Nat>`.  This "
            f"cell was the store-only differential that PROVED the store "
            f"planted nothing, which is why the obligation was recorded "
            f"unguarded; #1440 closed it, so the same differential now "
            f"shows the guard:\n{out}"
        )
        obs, envelope = _obligations(
            tmp_path, _P1_NAT_ELEMENT_STORE_ONLY, name="p1h.vera")
        binds = [(o["status"], o.get("error_code"))
                 for o in obs if o["kind"] == "nat_bind"]
        assert binds == [("violated", "E503")], obs
        _assert_partition(envelope)

    def test_a_nat_element_of_an_int_array_has_nothing_to_check(
        self, tmp_path: Path,
    ) -> None:
        """The over-reach control.

        Routing refined-first must not put a check on a `@Nat` stored as an
        `@Int` element, which is an `@Int` at the value level: the stream
        records only the index, and the module checks only the index.  (On
        the u64 `Nat` the store carried a widening guard, which #820 added
        and its obligation counted.)
        """
        obs, _ = _obligations(tmp_path, _N4_WIDEN_CONTROL, name="n4f.vera")
        assert [(o["kind"], o["status"]) for o in obs] == [
            ("requires", "verified"), ("index_bounds", "verified"),
            ("ensures", "verified")], obs
        compiled = _compiled(tmp_path, _N4_WIDEN_CONTROL, "n4g.vera")
        assert [c.kind for c in compiled.checks()] == [
            "index_out_of_bounds"], compiled.checks()


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
_A1_TUPLE_TRAP_SITE = "Refinement violation in fn(@Tuple<PosInt, Int> -> @Int)"
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


class TestCallResultClosureOperandIsObligated:
    """A closure OPERAND that is a call result reaches the closure-argument
    arm (#1525).

    `apply_fn(taker(()), mkint(x))` names its closure through a CALL rather
    than a slot.  The arm read the operand's declared function type from
    the slot, so no `refine_bind` was recorded and `verify` reported `ok:
    true` for a program whose payload the formal's `Option<PosInt>`
    forbids; code generation dropped `f` with `E602`, so nothing ran.  Code
    generation now lowers the application from the operand's checked
    function type (#1516), and the arm reads the same type, so the argument
    is obligated, and refuted, as the slot form's is.
    """

    def test_the_arm_reaches_a_call_result_operand(
        self, tmp_path: Path,
    ) -> None:
        obs, envelope = _obligations(
            tmp_path, _A2_CALL_RESULT_OPERAND, name="a2a.vera")
        binds = [(o["status"], o.get("error_code"))
                 for o in obs if o["kind"] == "refine_bind"]
        assert binds == [("violated", "E505")], binds
        assert envelope["ok"] is False, envelope
        _assert_partition(envelope)

    def test_and_the_slot_form_is_obligated_alike(
        self, tmp_path: Path,
    ) -> None:
        """The nearest neighbour: the closure bound to a slot first."""
        slot = _A2_CALL_RESULT_OPERAND.replace(
            "  apply_fn(taker(()), mkint(@Int.0))",
            "  let @Taker = taker(());\n  apply_fn(@Taker.0, mkint(@Int.0))")
        obs, envelope = _obligations(tmp_path, slot, name="a2b.vera")
        binds = [(o["status"], o.get("error_code"))
                 for o in obs if o["kind"] == "refine_bind"]
        assert binds == [("violated", "E505")], binds
        assert envelope["ok"] is False, envelope


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


class TestARefinedIntElementCountsItsPredicateAlone:
    """A refined `@Int` element fed a `@Nat` records its predicate (CR
    PR-review), and nothing for the widening.

    Routing refined-FIRST fixed the swallowed predicate.  On the u64 `Nat`
    the same site also carried a widening guard, for the representation a
    `@Nat` above `i64.MAX` took when it was reinterpreted as a signed
    `i64`, and a record had to count it.  A `@Nat` is an `@Int` at the value
    level now, so the predicate is the one fact the site checks.
    """

    def test_the_refined_element_records_its_predicate(
        self, tmp_path: Path,
    ) -> None:
        obs, envelope = _obligations(
            tmp_path, _CR_REFINED_INT_ELEMENT, name="cr4a.vera")
        assert [(o["kind"], o["status"]) for o in obs] == [
            ("requires", "verified"), ("index_bounds", "verified"),
            ("refine_bind", "verified"), ("ensures", "verified")], obs
        _assert_partition(envelope)

    def test_and_the_module_checks_the_predicate_alone(
        self, tmp_path: Path,
    ) -> None:
        """The plain `@Array<Int>` element is the control: its store checks
        nothing, and the refined element's checks are the control's plus
        the §2.6.5 predicate guard (#1426)."""
        def checks(source: str, name: str) -> list[str]:
            compiled = _compiled(tmp_path, source, name)
            return sorted(c.emitter for c in compiled.checks(function="f"))

        plain = checks(_CR_PLAIN_INT_ELEMENT, "cr4b.vera")
        refined = checks(_CR_REFINED_INT_ELEMENT, "cr4c.vera")
        assert plain == ["wasm/data.py:_translate_index_expr"], plain
        assert refined == sorted(
            plain + ["codegen/contracts.py:_emit_refinement_check"]), refined


#: A refinement-over-refinement `let` whose base the verifier does not model.
#:
#: The base is `@Byte`, not `@Int`, since #1434: an `Int` chain's predicates
#: are now CONJOINED, so `{ @Pos | @Pos.0 < 10 }` over `{ @Int | @Int.0 > 0 }`
#: is decided rather than disclosed — the `Int` spelling of this fixture is
#: now a correct `violated`/E505, because a `Pos` carries no upper bound.  What
#: these cells pin is the E506 RATIONALE for a refined base that codegen will
#: not guard, and `_base_slot_name` still declines a `@Byte` base (its
#: `0..255` is never asserted), so the chain stays undecided and the warning
#: these cells are about is still the one emitted.
_Q1_REFINED_OVER_REFINED_LET = """\
type SmallByte = { @Byte | @Byte.0 < 100 };
type Tiny = { @SmallByte | @SmallByte.0 < 10 };

public fn f(@SmallByte -> @Byte)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Tiny = @SmallByte.0;
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
        envelope = pipeline.verify(_write(
            tmp_path, _Q1_REFINED_OVER_REFINED_LET, "q1a.vera"), budget_s=_BUDGET_S).envelope()
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
        envelope = pipeline.verify(_write(
            tmp_path, _Q1_REFINED_OVER_REFINED_LET, "q1b.vera"), budget_s=_BUDGET_S).envelope()
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
