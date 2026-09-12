"""``throw``'s payload is obligated AND guarded like every other narrowing
site (#1268).

Every position a value narrows into a typed slot carries a proof obligation —
``let``, call argument, constructor field, effect-operation argument, handler
state init — and ``throw(v)`` narrows ``v`` into the ``Exn<E>`` payload exactly
as ``Log.emit(v)`` narrows into a declared op's formal.  It carried none.
``throw(0 - 5)`` under ``effects(<Exn<Nat>>)`` verified at 4/4 Tier 1 and
``vera run`` returned **-5** through the ``@Nat`` slot: no obligation, no
diagnostic, no guard.

The cause is not ``throw``'s ``Never`` return.  ``throw`` is a bare
:class:`~vera.ast.FnCall` with no entry in the function registry, so
``param_types`` is None and the formal loop that obligates a call's arguments
never runs.  #1203 met the same hole at the State ``put`` and added a
table-driven fallback for it — keyed on ``expr.name == "put"``, so ``throw``,
the only other bare built-in op taking an argument, stayed outside it.

Codegen emitted no guard on the payload either — ``throw`` lowered straight to
a WASM ``throw $exn_<family>`` with the argument on the stack — so a program
that never ran ``vera verify`` (and one whose ``E503`` its author ignored)
still delivered the violating value.  It now takes the write boundary's
guards, at the op-call site beside ``put``'s: the ``@Int`` -> ``@Nat`` sign
guard, the ``@Nat`` -> ``@Int`` widening guard, and — refined FIRST, as
everywhere else — the §2.6.5 predicate guard for a refined payload, which
traps through ``$vera.contract_fail`` naming the predicate.  So the obligation
is ``guarded`` at all three arms and its Tier-3 leg is counted, not disclosed.

That claim is checked against codegen rather than asserted: each arm's status
is pinned AND a run confirms the value really is stopped, with a satisfying
twin beside it so "guarded" cannot be satisfied by a site that always traps.
"""
from __future__ import annotations

import re

import pytest

from vera.codegen import execute
from vera.codegen.api import WasmTrapError
from tests.codegen_helpers import (
    _compile,
    _compile_ok,
    _run,
    _run_refine_trap,
    _run_trap,
    wat_fn_body,
)
from tests.verifier_helpers import _verify, _verify_err


_POS = "type Pos = { @Int | @Int.0 > 0 };\n"
_SMALL = "type Small = { @Byte | @Byte.0 < 10 };\n"


def _thrower(payload: str, value: str, *, prelude: str = "",
             params: str = "@Unit", handler_body: str = "0") -> str:
    """A function that throws *value* into an ``Exn<payload>``, and a handler.

    The handler is what makes the program whole; the obligation under test is
    at the ``throw``, in ``boom``.
    """
    return f"""
{prelude}
private fn boom({params} -> @Int)
  requires(true)
  ensures(true)
  effects(<Exn<{payload}>>)
{{
  throw({value})
}}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{{
  handle[Exn<{payload}>] {{
    throw(@{payload}) -> {{ {handler_body} }}
  }} in {{
    boom({'(())' if params == '@Unit' else '(0 - 5)'})
  }}
}}
"""


class TestTheThrowPayloadIsObligated:
    """The obligation exists at all, in each of the three arms."""

    def test_a_negative_literal_into_a_nat_payload_is_refuted(self) -> None:
        """The `@Nat` arm: `throw(0 - 5)` into `Exn<Nat>` is an E503.

        This is the shape that ran to completion returning -5.
        """
        src = _thrower("Nat", "0 - 5", handler_body="nat_to_int(@Nat.0)")
        errs = _verify_err(src, "may be negative")
        assert any(e.error_code == "E503" for e in errs), [
            (e.error_code, e.description[:80]) for e in errs
        ]
        binds = [o for o in _verify(src).obligations if o.kind == "nat_bind"]
        assert [o.status for o in binds] == ["violated"], binds

    def test_a_violating_literal_into_a_refined_payload_is_refuted(
        self,
    ) -> None:
        """The refinement arm, over a base the verifier models: the solver
        refutes `0 - 5 > 0` and the site reports E505."""
        src = _thrower("Pos", "0 - 5", prelude=_POS)
        errs = _verify_err(src, "refinement predicate")
        assert any(e.error_code == "E505" for e in errs), [
            (e.error_code, e.description[:80]) for e in errs
        ]
        binds = [o for o in _verify(src).obligations if o.kind == "refine_bind"]
        assert [o.status for o in binds] == ["violated"], binds

    def test_a_nat_payload_widening_into_an_int_slot_is_obligated(
        self,
    ) -> None:
        """The widening arm: a bare `@Nat` thrown into an `Exn<Int>` payload
        reinterprets above i64.MAX, so the site records a
        `nat_to_int_coerce` obligation where it recorded nothing."""
        src = _thrower("Int", "@Nat.0", params="@Nat",
                       handler_body="@Int.0")
        # `boom(0 - 5)` is not a @Nat argument, so drive the call directly.
        src = src.replace("boom((0 - 5))", "boom(5)")
        result = _verify(src)
        coerce = [o for o in result.obligations
                  if o.kind == "nat_to_int_coerce"]
        assert coerce, [o.kind for o in result.obligations]


class TestTheConcreteGateReachesTheThrowPayload:
    """#1251(b)'s literal gate applies here for free, being the same helper."""

    def test_a_literal_over_an_unmodelled_base_is_decided(self) -> None:
        """`throw(200)` into `Exn<{ @Byte | @Byte.0 < 10 }>`.

        `Byte` is not a base the verifier models, so before #1251(b) this
        would have been the honest-but-silent Tier-3; routing `throw` into the
        shared helper means the concrete gate decides it, naming the value.
        """
        src = _thrower("Small", "200", prelude=_SMALL,
                       handler_body="byte_to_int(@Small.0)")
        errs = _verify_err(src, "violates the refinement")
        assert any(e.error_code == "E505" for e in errs), [
            (e.error_code, e.description[:80]) for e in errs
        ]
        assert any("200" in e.description for e in errs), [
            e.description[:120] for e in errs
        ]

    def test_a_satisfying_literal_over_an_unmodelled_base_proves(self) -> None:
        """The passing twin, so the gate is not "reject every thrown literal".

        Static AND run.  This was static-only when it landed, because a
        `@Byte` payload emitted an `i64.const` under the tag's i32 parameter
        and the module failed WASM validation before any of it could run
        (#1269, PR #1270's review).  With the throw payload marked as the
        write boundary it is, the program the verifier proved is also the
        program that runs — which is what a Tier-1 proof is FOR, and the
        only way to see that the proved value and the delivered one are the
        same 5.
        """
        src = _thrower("Small", "5", prelude=_SMALL,
                       handler_body="byte_to_int(@Small.0)")
        result = _verify(src)
        binds = [o for o in result.obligations if o.kind == "refine_bind"]
        assert [o.status for o in binds] == ["verified"], binds
        assert not [
            d for d in result.diagnostics if d.severity == "error"
        ], [d.description[:90] for d in result.diagnostics]
        assert _run(src) == 5


class TestTheThrowPayloadObligationMatchesEveryOtherSite:
    """Contrast and spelling: the same value, reached three other ways."""

    _USER_EFFECT = """
type Pos = { @Int | @Int.0 > 0 };

effect Log {
  op emit(Pos -> Unit);
}

private fn boom(@Unit -> @Unit)
  requires(true)
  ensures(true)
  effects(<Log>)
{
  Log.emit(0 - 5)
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[Log] {
    emit(@Pos) -> { resume(()) }
  } in {
    boom(());
    0
  }
}
"""

    def test_the_user_effect_op_and_throw_agree(self) -> None:
        """A declared op's argument was loud while `throw`'s was silent, for
        the same value against the same refinement — the asymmetry that made
        this a bug rather than a documented limitation.  Both are loud now,
        at the same site name, so a reader cannot learn one rule from a user
        effect and have it fail to hold for `Exn`."""
        user = _verify_err(self._USER_EFFECT, "refinement predicate")
        thrown = _verify_err(
            _thrower("Pos", "0 - 5", prelude=_POS), "refinement predicate")
        assert {e.error_code for e in user} == {"E505"}, user
        assert {e.error_code for e in thrown} == {"E505"}, thrown
        assert all("effect-operation argument" in e.description
                   for e in user + thrown), [
            e.description[:90] for e in user + thrown
        ]

    def test_the_refined_alias_spelling_is_obligated_too(self) -> None:
        """`Exn<Payload>` where `type Payload = Pos` resolves through the
        alias chain to the same refinement, so it obligates identically — a
        gate keyed on the syntactic spelling would let it through."""
        src = _thrower("Payload", "0 - 5",
                       prelude=_POS + "\ntype Payload = Pos;\n")
        errs = _verify_err(src, "refinement predicate")
        assert any(e.error_code == "E505" for e in errs), [
            (e.error_code, e.description[:80]) for e in errs
        ]


class TestTheThrowPayloadGuardIsRealAndItsDisclosureIsHonest:
    """The verifier's `guarded=True` is checked against what codegen emits.

    A unit assertion that the status is `tier3` says what the verifier
    believes; it cannot say whether the belief is true.  The pair here does:
    the status pins the flag, and the run pins codegen's side of it.  Delete
    the guard emission and the run assertions go red rather than leaving a
    claimed runtime check that is not emitted; flip the flag back without
    removing the guard and the status assertions go red rather than leaving
    the verifier quietly pessimistic about a boundary it does have.
    """

    _UNTRANSLATABLE = """
private fn boom(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(<Exn<Nat>>)
{
  throw(array_length(string_lines("a\\nb")))
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[Exn<Nat>] {
    throw(@Nat) -> { nat_to_int(@Nat.0) }
  } in {
    boom(())
  }
}
"""

    _SYMBOLIC = """
private fn boom(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(<Exn<Nat>>)
{
  throw(@Int.0)
}

public fn main(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[Exn<Nat>] {
    throw(@Nat) -> { nat_to_int(@Nat.0) }
  } in {
    boom(@Int.0)
  }
}
"""

    _REFINED_SYMBOLIC = """
type Pos = { @Int | @Int.0 > 0 };

private fn boom(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(<Exn<Pos>>)
{
  throw(@Int.0)
}

public fn main(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[Exn<Pos>] {
    throw(@Pos) -> { @Pos.0 }
  } in {
    boom(@Int.0)
  }
}
"""

    _REFINED_OPAQUE = """
type Pos = { @Int | @Int.0 > 0 };

private fn boom(@Float64 -> @Int)
  requires(true)
  ensures(true)
  effects(<Exn<Pos>>)
{
  throw(float_to_int(@Float64.0))
}

public fn main(@Float64 -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[Exn<Pos>] {
    throw(@Pos) -> { @Pos.0 }
  } in {
    boom(@Float64.0)
  }
}
"""

    _UNREFINED_INT = """
private fn boom(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(<Exn<Int>>)
{
  throw(@Int.0)
}

public fn main(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[Exn<Int>] {
    throw(@Int) -> { @Int.0 }
  } in {
    boom(@Int.0)
  }
}
"""

    def test_an_undischargeable_payload_discloses_guarded(self) -> None:
        """`array_length` over a non-literal is deliberately untranslatable
        (#802), so the obligation reaches Tier 3 — and lands on the
        runtime-GUARDED leg, counted in the totals, because the guard the leg
        promises is emitted at the throw."""
        result = _verify(self._UNTRANSLATABLE)
        binds = [o for o in result.obligations if o.kind == "nat_bind"]
        assert [o.status for o in binds] == ["tier3"], binds
        assert result.summary.tier3_runtime >= 1, result.summary

    def test_the_payload_really_is_checked_at_run_time(self) -> None:
        """...because codegen emits the sign guard: -5 no longer comes back
        out of the `@Nat` payload, it traps.  This is the measurement the
        `guarded=True` above rests on."""
        _run_trap(self._SYMBOLIC, "main", [-5])

    def test_a_satisfying_payload_still_runs(self) -> None:
        """The over-refusal control for the run above.  A guard that trapped
        unconditionally would satisfy the trap assertion and break every
        correct `throw`; the same program at a non-negative payload must
        deliver it."""
        assert _run(self._SYMBOLIC, "main", [5]) == 5

    def test_a_refined_payload_traps_naming_its_predicate(self) -> None:
        """The refined arm's run: the §2.6.5 predicate guard, not the sign
        guard — `0` clears the `@Int` base but violates `> 0`, so a `>= 0`
        check would let it through.  `_run_refine_trap` pins the
        `$vera.contract_fail` channel rather than any trap."""
        _run_refine_trap(self._REFINED_SYMBOLIC, "main", [0])
        _run_refine_trap(self._REFINED_SYMBOLIC, "main", [-5])

    def test_a_satisfying_refined_payload_still_runs(self) -> None:
        """The refined arm's over-refusal control."""
        assert _run(self._REFINED_SYMBOLIC, "main", [7]) == 7

    def test_an_unrefined_int_payload_keeps_its_negative(self) -> None:
        """The TYPE gate is load-bearing: an `Exn<Int>` payload has no
        non-negativity invariant to violate, so a negative one is a correct
        program and must run.  Guarding on the wrong type — the sign guard
        applied to the `@Int` arm — turns this into a trap.
        """
        assert _run(self._UNREFINED_INT, "main", [-5]) == -5

    _REFINED_STRING = """
type Short = { @String | string_length(@String.0) < 5 };

private fn boom(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(<Exn<Short>>)
{
  throw(to_string(@Int.0))
}

public fn main(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[Exn<Short>] {
    throw(@Short) -> { string_length(@Short.0) }
  } in {
    boom(@Int.0)
  }
}
"""

    def test_a_pair_payload_is_guarded_over_its_pointer(self) -> None:
        """The other REPRESENTATION: a `@String`-based payload is (ptr, len)
        in two locals, not one scalar, so the guard has to save both halves
        and check over the ptr — the shape the lifted closure's `i32_pair`
        return guard uses.  A scalar-only guard emits an ill-typed body here
        rather than a wrong answer, so this is the branch that would fail
        loudly; the satisfying twin beside it is what shows the pair is put
        back on the stack in the right order.
        """
        _run_refine_trap(self._REFINED_STRING, "main", [12345678])
        assert _run(self._REFINED_STRING, "main", [1]) == 1

    def test_a_refined_payload_discloses_guarded(self) -> None:
        """The refined arm's status twin of the `@Nat` one above: an opaque
        payload — `float_to_int`, which the verifier models only as an opaque
        result — records `refine_bind` at the runtime-GUARDED Tier 3, counted
        in the totals, because the predicate guard is emitted."""
        result = _verify(self._REFINED_OPAQUE)
        binds = [o for o in result.obligations if o.kind == "refine_bind"]
        assert [o.status for o in binds] == ["tier3"], binds
        assert result.summary.tier3_runtime >= 1, result.summary

    def test_a_symbolic_payload_the_contract_bounds_proves(self) -> None:
        """The obligation is dischargeable, not merely loud: a `requires`
        implying the payload's type proves it at Tier 1.  Without this the
        suite above is satisfied by a site that always fails."""
        result = _verify("""
private fn boom(@Int -> @Int)
  requires(@Int.0 > 0)
  ensures(true)
  effects(<Exn<Nat>>)
{
  throw(@Int.0)
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[Exn<Nat>] {
    throw(@Nat) -> { nat_to_int(@Nat.0) }
  } in {
    boom(7)
  }
}
""")
        binds = [o for o in result.obligations if o.kind == "nat_bind"]
        assert [o.status for o in binds] == ["verified"], binds
        assert not [
            d for d in result.diagnostics if d.severity == "error"
        ], [d.description[:90] for d in result.diagnostics]


class TestTheGuardedClaimIsNeverWiderThanTheGuard:
    """The three places the claim and the guard could disagree.

    A `guarded` Tier-3 is a PROMISE — "this will be checked at run time" —
    and the obligation stream is the only place a reader can see it.  Each
    cell here is a shape where the promise and the emitted code came apart in
    a direction a value oracle cannot see, because the program either never
    runs or runs identically either way.
    """

    _NESTED = """
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

    def _payload(self, base: str, spelling: str) -> str:
        """A `throw` into `Exn<base>` written bare or qualified.

        The payload is `float_to_int`'s opaque result, so the obligation
        reaches Tier 3 and its GUARDEDNESS is what the status reports —
        a refutation or a proof would hide the flag being compared.
        """
        prelude = ("type Pos = { @Int | @Int.0 > 0 };\n\n"
                   if base == "Pos" else "")
        body = "@Pos.0" if base == "Pos" else "nat_to_int(@Nat.0)"
        return f"""
{prelude}private fn boom(@Float64 -> @Int)
  requires(true)
  ensures(true)
  effects(<Exn<{base}>>)
{{
  {spelling}(float_to_int(@Float64.0))
}}

public fn main(@Float64 -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{{
  handle[Exn<{base}>] {{
    throw(@{base}) -> {{ {body} }}
  }} in {{
    boom(@Float64.0)
  }}
}}
"""

    def test_a_nested_refinement_payload_promises_nothing(self) -> None:
        """A refinement OVER a refinement has no guard and cannot have one.

        `_refinement_guard_parts` refuses the shape outright — the outer
        predicate alone would silently drop the inner membership — and says
        so with a loud E618 at compile.  The verifier's mirror answered
        `True` for it, so `vera verify` exited 0 recording a Tier-3 that
        "will be checked at run time" for a program that cannot be compiled
        at all: a promise about a run that can never happen.  Both halves are
        pinned together, because either alone reads as consistent.
        """
        result = _verify(self._NESTED)
        binds = [o for o in result.obligations if o.kind == "refine_bind"]
        assert [o.status for o in binds] == ["tier3_unguarded"], binds
        # The count is not the bind's: a `tier3_unguarded` discharges to no
        # tier and is excluded from `tier3_runtime`.  The 1 is the payload
        # expression's own `float_to_int` domain obligation, named here so
        # the summary assertion cannot be read as counting the bind.
        domain = [o for o in result.obligations
                  if o.kind == "float_to_int_domain"]
        assert [o.status for o in domain] == ["tier3"], domain
        assert result.summary.tier3_runtime == 1, result.summary
        compiled = _compile(self._NESTED)
        errors = [d for d in compiled.diagnostics if d.severity == "error"]
        assert [d.error_code for d in errors] == ["E618"], [
            (d.error_code, d.description[:80]) for d in errors
        ]

    @pytest.mark.parametrize(
        ("base", "kind"), [("Nat", "nat_bind"), ("Pos", "refine_bind")],
    )
    def test_the_two_spellings_record_the_same_thing(
        self, base: str, kind: str,
    ) -> None:
        """`Exn.throw(v)` is `throw(v)`, so it must obligate identically.

        Codegen's qualified arm SYNTHESIZES a bare node and delegates to the
        dispatcher that emits the guards, so both spellings are guarded — but
        the verifier's `QualifiedCall` arm hardcoded `guarded=False` behind a
        comment stale since [#1203], and disclosed E504/E506 for a boundary
        that traps.  Asserted as a differential rather than two literals: the
        two spellings are ONE boundary, so the statuses must agree whatever
        that agreed value is, and the run confirms which one is true.
        """
        def of(result: object) -> list[tuple[str, str]]:
            return [(o.kind, o.status) for o in result.obligations
                    if o.kind == kind]

        bare = _verify(self._payload(base, "throw"))
        qualified = _verify(self._payload(base, "Exn.throw"))
        assert of(bare) == of(qualified), (of(bare), of(qualified))
        assert of(bare) == [(kind, "tier3")], of(bare)
        assert (bare.summary.tier3_runtime
                == qualified.summary.tier3_runtime), (
            bare.summary, qualified.summary)
        # ...and the guard both now claim is really emitted on both paths.
        _run_trap(self._payload(base, "throw"), "main", [-5.0])
        _run_trap(self._payload(base, "Exn.throw"), "main", [-5.0])

    def test_the_unguarded_disclosure_no_longer_names_the_throw_payload(
        self,
    ) -> None:
        """E504's rationale listed the `Exn` `throw` payload among the sites
        with no runtime guard.  That is false since the guard landed, and it
        contradicts the spec sentences this change amended — a reader taking
        the diagnostic at its word would add a defensive check the compiler
        already emits.  Reached through the site that IS still unguarded, a
        user-declared effect's operation argument, so the sentence is read
        from a real diagnostic rather than from the source.
        """
        result = _verify("""
effect Counter {
  op bump(Nat -> Unit);
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[Counter] {
    bump(@Nat) -> { resume(()) }
  } in {
    Counter.bump(array_length(string_lines("a\\nb")));
    0
  }
}
""")
        binds = [o for o in result.obligations if o.kind == "nat_bind"]
        assert [o.status for o in binds] == ["tier3_unguarded"], binds
        rationales = [d.rationale for d in result.diagnostics
                      if d.error_code == "E504"]
        assert len(rationales) == 1, [d.error_code for d in result.diagnostics]
        assert "throw` payload ARE" in rationales[0], rationales[0]
        assert "or an Exn `throw` payload)" not in rationales[0], rationales[0]


class TestTheQualifiedArmObligatesAllThreeArms:
    """The qualified arm records the WIDENING too, not just two of three.

    PR #1325 review.  The `QualifiedCall` arm was hand-written as a
    refined-then-@Nat chain, and simply had no `@Nat` -> `@Int` widening
    branch — so `State.put(@Nat.0)` / `Exn.throw(@Nat.0)` into an `@Int`
    cell recorded NO obligation at all, while codegen emitted the widening
    guard on both spellings (the qualified forms synthesize a bare node and
    delegate to the dispatcher that emits it).  A guard the obligation
    stream never mentions is the same disease as a guard it claims and does
    not emit: `verify --json` is the only place a reader can see either.

    Asserted as a differential over the two spellings of each op rather
    than as literals, because the two spellings ARE one boundary.
    """

    def _widen(self, op: str, spelling: str) -> str:
        """A `@Nat` argument widening into an `@Int` cell / payload."""
        if op == "throw":
            return f"""
private fn boom(@Nat -> @Int)
  requires(true)
  ensures(true)
  effects(<Exn<Int>>)
{{
  {spelling}(@Nat.0)
}}

public fn main(@Nat -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{{
  handle[Exn<Int>] {{
    throw(@Int) -> {{ @Int.0 }}
  }} in {{
    boom(@Nat.0)
  }}
}}
"""
        return f"""
private fn store(@Nat -> @Unit)
  requires(true)
  ensures(true)
  effects(<State<Int>>)
{{
  {spelling}(@Nat.0)
}}

public fn main(@Nat -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{{
  handle[State<Int>](@Int = 1) {{
    get(@Unit) -> {{ resume(@Int.0) }},
    put(@Int) -> {{ resume(()) }}
  }} in {{
    store(@Nat.0);
    0
  }}
}}
"""

    @pytest.mark.parametrize(
        ("op", "bare", "qualified"),
        [("throw", "throw", "Exn.throw"), ("put", "put", "State.put")],
    )
    def test_both_spellings_record_the_widening(
        self, op: str, bare: str, qualified: str,
    ) -> None:
        """One `nat_to_int_coerce` on each side, at the same status."""
        def coerce(src: str) -> list[tuple[str, str]]:
            return [(o.kind, o.status) for o in _verify(src).obligations
                    if o.kind == "nat_to_int_coerce"]

        b = coerce(self._widen(op, bare))
        q = coerce(self._widen(op, qualified))
        assert b == q, (b, q)
        assert b == [("nat_to_int_coerce", "tier3")], b

    @pytest.mark.parametrize(
        ("op", "spelling"),
        [("throw", "throw"), ("throw", "Exn.throw"),
         ("put", "put"), ("put", "State.put")],
    )
    def test_the_guard_the_obligation_promises_is_emitted(
        self, op: str, spelling: str,
    ) -> None:
        """...and codegen really does emit it, on BOTH spellings.

        The obligation above says `tier3` — runtime-guarded — so this is the
        half that makes that a fact rather than a claim.  Without it the
        differential is satisfied by two sides agreeing on a promise neither
        keeps.
        """
        result = _compile_ok(self._widen(op, spelling))
        body = wat_fn_body(result.wat, "boom" if op == "throw" else "store")
        # The signal call between the `if` and the `unreachable` is #1438's:
        # the widening guard names itself so its trap reports
        # `kind="widen_guard"` rather than the generic paragraph.  Required,
        # not optional — a guard that traps anonymously here is the defect
        # #1438 closed.
        guard = re.compile(
            r"local\.tee \d+\s+i64\.const 0\s+i64\.lt_s\s+if\s+"
            r"call \$vera\.widen_trap\s+unreachable\s+end",
            re.S,
        )
        assert guard.search(body), body


class TestARefinementDoesNotDisableTheWideningGuard:
    """A refinement OVER `@Int` rides BESIDE the widening obligation.

    The #820 intersection, which the shared triple was missing at this
    boundary (PR #1325 review).  The three arms are an `elif` chain, so a
    refined formal claimed the value and the widening check never ran — and
    codegen mirrored it exactly, which is why this was not a
    verifier-versus-codegen desync but something worse in one respect: both
    sides agreed to skip a check the UNREFINED spelling performs.

    A refinement predicate does not imply fit-in-i64.  `@Nat` is u64 and
    `@Int` is i64, so a `@Nat` above i64.MAX reinterprets to a negative
    `@Int` — and `{ @Int | true }` is satisfied by that negative, as `< 100`
    would be.  Adding a refinement therefore WEAKENED the boundary: measured
    before the fix, `Exn<Int>` fed u64.MAX trapped on the widening guard
    while `Exn<{ @Int | true }>` fed the same value returned -1.
    """

    _REFINED = """
type AnyInt = { @Int | true };

private fn boom(@Nat -> @Int)
  requires(true)
  ensures(true)
  effects(<Exn<AnyInt>>)
{
  throw(@Nat.0)
}

public fn main(@Nat -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[Exn<AnyInt>] {
    throw(@AnyInt) -> { @AnyInt.0 }
  } in {
    boom(@Nat.0)
  }
}
"""

    #: The same program with the refinement removed — the spelling whose
    #: protection the refined one has to match.
    _BARE = _REFINED.replace(
        "type AnyInt = { @Int | true };\n\n", "").replace("AnyInt", "Int")

    #: u64.MAX in an i64 slot reads back as -1.
    _U64_MAX = 18446744073709551615

    def test_both_obligations_are_recorded(self) -> None:
        """`refine_bind` AND `nat_to_int_coerce`, not one or the other.

        Different kinds describing different facts about one value, so this
        is a pair rather than a double-record: the predicate is about which
        inhabitants are legal, the coercion about whether the value survives
        the u64-to-i64 reinterpretation at all.
        """
        kinds = [o.kind for o in _verify(self._REFINED).obligations
                 if o.kind in ("refine_bind", "nat_to_int_coerce")]
        assert kinds == ["refine_bind", "nat_to_int_coerce"], kinds

    def test_both_guards_are_emitted(self) -> None:
        """...and codegen emits both, so neither obligation is a promise
        the module does not keep."""
        body = wat_fn_body(_compile_ok(self._REFINED).wat, "boom")
        assert "contract_fail" in body, body
        assert re.search(
            r"i64\.const 0\s+i64\.lt_s\s+if\s+call \$vera\.widen_trap",
            body, re.S,
        ), body

    def test_the_refinement_does_not_weaken_the_boundary(self) -> None:
        """The behavioural pin, as a DIFFERENTIAL against the bare spelling.

        Asserting "the refined one traps" alone would be satisfied by a
        boundary that traps on everything; asserting it agrees with the bare
        spelling is the property that was broken — refined returned -1 where
        bare trapped.
        """
        with pytest.raises(WasmTrapError):
            execute(_compile_ok(self._BARE), fn_name="main",
                    args=[self._U64_MAX])
        with pytest.raises(WasmTrapError):
            execute(_compile_ok(self._REFINED), fn_name="main",
                    args=[self._U64_MAX])

    def test_a_value_that_fits_still_passes(self) -> None:
        """The over-refusal control: the guard is dead for an in-range value,
        on both spellings."""
        assert _run(self._REFINED, "main", [5]) == 5
        assert _run(self._BARE, "main", [5]) == 5


class TestAProvedContractSurvivesTheThrowPayload:
    """The soundness differential: verify says PROVED, so run must agree.

    The clause parameter `@Nat` is not a claim the handler makes, it is one
    the verifier hands every DOWNSTREAM consumer: `is_nonneg` discharges
    `ensures(@Bool.result)` at Tier 1 purely from its parameter's type, with
    no `requires` doing the work.  So the payload reaching it decides whether
    a Tier-1 proof is worth anything.  Pre-fix it was not — the run reported
    ``Postcondition violation in is_nonneg`` on a postcondition `vera verify`
    had just proved, which is the signature the repo's verifier-probing rule
    names.  Everything between the throw and the consumer is deliberately
    guard-free: the argument `@Nat.0` is already `@Nat`-typed, so no call-site
    narrowing guard fires, and no `nat_to_int` coercion sits in the path.
    """

    _SRC = """
private fn boom(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(<Exn<Nat>>)
{
  throw(0 - 5)
}

private fn is_nonneg(@Nat -> @Bool)
  requires(true)
  ensures(@Bool.result)
  effects(pure)
{
  @Nat.0 >= 0
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[Exn<Nat>] {
    throw(@Nat) -> { if is_nonneg(@Nat.0) then { 1 } else { 0 } }
  } in {
    boom(())
  }
}
"""

    def test_the_consumers_postcondition_is_proved(self) -> None:
        """Half one: `is_nonneg`'s `ensures` really is a Tier-1 proof, and it
        rests on the parameter's `@Nat` invariant alone.  Without this the
        run below proves nothing — a postcondition the verifier had left at
        Tier 3 would be entitled to fail."""
        result = _verify(self._SRC)
        proved = [o for o in result.obligations
                  if o.kind == "ensures" and o.status == "verified"
                  and o.fn_name == "is_nonneg"]
        assert [o.expr_text for o in proved] == ["@Bool.result"], [
            (o.fn_name, o.kind, o.status, o.expr_text)
            for o in result.obligations
        ]

    def test_the_proof_is_not_violated_at_run(self) -> None:
        """Half two: the run.  The program is refuted statically (E503 at the
        throw), but `vera run` does not verify, so this is the unverified
        path §2.6.5 calls defense in depth — it must stop at the boundary
        that was violated, not carry -5 into a function that proved it could
        not receive one.

        The assertion is on WHICH failure, not merely that one occurred: a
        contract violation reaches the host through the same
        ``WasmTrapError`` channel a guard trap does, so `_run_trap` alone is
        satisfied by the pre-fix behaviour and would be green either way.
        The pre-fix RED is a `Postcondition violation in is_nonneg` — the
        proved postcondition failing — so that is what must be absent.
        """
        result = _compile_ok(self._SRC)
        with pytest.raises(WasmTrapError) as caught:
            execute(result)
        message = str(caught.value)
        assert "Postcondition violation" not in message, message
        assert "is_nonneg" not in message, message


class TestABareOpArgumentIsObligatedByStructureNotByName:
    """The fallback is keyed on "this resolves to an effect operation".

    Its first version listed the two built-in op NAMES that take a value, and
    a name list is a claim about every other name.  A user effect's op called
    bare is the same narrowing at the same site, and it was obligated iff it
    happened to be spelled `put` — `emit` was silent for the identical value
    against the identical refinement.  That falsifies the two places the rule
    is written down: spec §2.6.4 lists effect-operation arguments among the
    sites every narrowing is obligated at, and KNOWN_ISSUES.md's #754 row
    says every narrowing binding site is statically obligated.

    Resolving the operation is the structural question, and the code already
    resolved it one line below the gate to compute guardedness.
    """

    _USER_OP = """
type Pos = { @Int | @Int.0 > 0 };

effect Log {
  op %(name)s(Pos -> Unit);
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[Log] {
    %(name)s(@Pos) -> { resume(()) }
  } in {
    %(name)s(0 - 5);
    0
  }
}
"""

    @pytest.mark.parametrize("name", ["emit", "put"])
    def test_a_bare_user_op_argument_is_obligated_whatever_its_name(
        self, name: str,
    ) -> None:
        """Both spellings are loud.  `put` was already, by coincidence."""
        errs = _verify_err(self._USER_OP % {"name": name},
                           "refinement predicate")
        assert any(e.error_code == "E505" for e in errs), [
            (e.error_code, e.description[:80]) for e in errs
        ]

    def test_a_user_op_is_not_claimed_runtime_guarded(self) -> None:
        """Guardedness stays keyed on the PARENT EFFECT, so a user effect's
        op — of either name — is the unguarded class and discloses E504
        rather than claiming the built-in `State` store's runtime guard.

        Named `put` deliberately: the coincidence that made the old gate look
        right is the same coincidence that would make a name-keyed
        guardedness computation look right.
        """
        result = _verify("""
effect Log {
  op put(Nat -> Unit);
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[Log] {
    put(@Nat) -> { resume(()) }
  } in {
    put(array_length(string_lines("a\\nb")));
    0
  }
}
""")
        binds = [o for o in result.obligations if o.kind == "nat_bind"]
        assert [o.status for o in binds] == ["tier3_unguarded"], binds
        assert [o.error_code for o in binds] == ["E504"], binds
        assert result.summary.tier3_runtime == 0, result.summary

    def test_a_resume_value_is_obligated_exactly_once(self) -> None:
        """A `State` get clause's tail `resume(v)` is obligated from the
        HandleExpr arm, where the clause's effect identity is known.  Widening
        the bare-call gate must not let the walk obligate it a SECOND time
        from the call site — one violation, one diagnostic.
        """
        result = _verify("""
type Pos = { @Int | @Int.0 > 0 };

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Pos>](@Pos = 1) {
    get(@Unit) -> { resume(0 - 5) },
    put(@Pos) -> { resume(()) }
  } in {
    get(())
  }
}
""")
        binds = [o for o in result.obligations
                 if o.kind == "refine_bind" and o.status == "violated"]
        assert len(binds) == 1, binds
        assert len([d for d in result.diagnostics
                    if d.error_code == "E505"]) == 1, [
            d.description[:80] for d in result.diagnostics
        ]


@pytest.mark.parametrize("program", [
    "ch07_exn_handler.vera",
    "ch07_exn_string.vera",
    "ch07_exn_composite.vera",
    "ch07_exn_scalar_alias.vera",
    "ch07_exn_string_alias.vera",
    "ch07_exn_param_alias.vera",
])
def test_the_exn_conformance_programs_stay_clean(program: str) -> None:
    """The canaries: obligating a position that had none must not turn a
    correct `throw` into a rejection.  Every conformance program that throws
    is verified whole here, so a regression names itself instead of arriving
    as one line of a corpus sweep."""
    import pathlib

    path = pathlib.Path(__file__).parent / "conformance" / program
    result = _verify(path.read_text(encoding="utf-8"))
    assert not [
        d for d in result.diagnostics if d.severity == "error"
    ], [d.description[:90] for d in result.diagnostics]
