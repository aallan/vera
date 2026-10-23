"""A parameterised alias APPLICATION substitutes its arguments (#1237).

``type Box<T> = T;`` declares an alias whose body is its own type parameter.
Applied — ``@Box<Cnt>`` — the resolved type is whatever ``Cnt`` resolves to;
the parameter ``T`` is a binder, not a type name.  The verifier's own
``_resolve_type`` ignored the application's type arguments entirely and handed
back the alias's registered body unchanged, so ``Box<Cnt>`` resolved to
``AdtType(name='T')`` — the binder leaking out as an ADT name.

Everything downstream that asks what a type IS then got the wrong answer.  The
reported symptom is a refinement's BASE: ``{ @Box<Cnt> | @Box<Cnt>.0 >= 18 }``
resolved its base to that phantom ADT, which fails the modelled-primitive gate
in ``SmtContext._translate_call_with_info``, so the refined-return fact was
dropped and a valid program was rejected with a spurious E501 while `vera run`
returned the right answer.

The checker has substituted since #660 (``vera/checker/resolution.py``), which
is why the program type-checks; only the verifier's parallel resolver did not.
Two halves have to move together and both are asserted here: the alias's body
must resolve its OWN parameters as type variables at registration (``T`` was
otherwise registered as an opaque ADT, and ``substitute`` maps type variables),
and the application must substitute.

Each verdict is checked against the runtime, because the two failure modes of
a wrong base — a fact that vanishes and a fact assumed that was never granted
— look identical from inside the verifier, and only `vera run` says which one
a verdict is.
"""
from __future__ import annotations

import pytest

from vera.runtime.traps import WasmTrapError
from vera.types import NAT, AdtType, RefinedType
from vera.verifier import ContractVerifier, VerifyResult
from tests import pipeline


# =====================================================================
# Helpers
# =====================================================================

def _verify(source: str) -> VerifyResult:
    """Type-check and verify *source*, asserting it type-checks cleanly.

    Check-clean is this file's premise: the whole point is that the CHECKER
    accepts these programs (it substitutes) and the verifier did not.
    """
    verified = pipeline.verify(source)
    _ = verified.checked.program  # raises the parse or transform error, if any
    check_errors = verified.checked.errors
    assert not check_errors, (
        "fixture must type-check cleanly, got: "
        f"{[(d.error_code, d.description[:70]) for d in check_errors]}"
    )
    return verified.result


def _codes(result: VerifyResult) -> set[str]:
    return {d.error_code for d in result.diagnostics if d.severity == "error"}


def _warn_codes(result: VerifyResult) -> set[str]:
    return {
        d.error_code for d in result.diagnostics if d.severity == "warning"
    }


def _run(source: str) -> object:
    """Compile *source* and call ``main`` — the runtime oracle.

    Compiled unchecked (no type check, none of the checker's tables), as
    ``fixture.vera``.
    """
    result = pipeline.compile(source, file="fixture.vera").result
    errors = [d for d in result.diagnostics if d.severity == "error"]
    assert not errors, f"unexpected codegen errors: {errors}"
    return pipeline.run(result, "main", capture_stderr=False).value


def _resolve_in_verifier(source: str, type_name: str) -> object:
    """What ``ContractVerifier._resolve_type`` makes of ``@<type_name>``.

    Registers *source*'s declarations the way ``verify_program`` does, then
    resolves the named alias through the verifier's own resolver — the layer
    under test, one step below any refinement or SMT machinery.
    """
    typed = pipeline.check(source).typed
    verifier = ContractVerifier(typed, source=source)
    verifier.register_program(typed.program)
    return verifier.env.type_aliases[type_name].resolved_type


# The issue's exact shape.  `mk`'s result is a fresh variable constrained ONLY
# by the refinement predicate — its `ensures` is `true` and the literal `20`
# tells the caller nothing about it — so `need18(mk(20))` is provable exactly
# when the refined-return fact survives.
_APPLIED = """\
type Cnt = Nat;

type Box<T> = T;

type Grown = { @Box<Cnt> | @Box<Cnt>.0 >= 18 };

private fn mk(@Nat -> @Grown)
  requires(@Nat.0 >= 18)
  ensures(true)
  effects(pure)
{
  @Nat.0
}

private fn need18(@Nat -> @Nat)
  requires(@Nat.0 >= 18)
  ensures(true)
  effects(pure)
{
  @Nat.0
}

public fn main(@Unit -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  need18(mk(20))
}
"""


class TestTheApplicationResolvesToItsArgument:
    """The layer under test, before any refinement is involved."""

    def test_the_alias_body_registers_its_own_parameter_as_a_type_variable(
        self,
    ) -> None:
        """``type Box<T> = T;`` registers ``TypeVar('T')``, not ``AdtType('T')``.

        The first of the two halves.  ``substitute`` maps TYPE VARIABLES, so an
        alias body registered with its parameter as an opaque ADT is
        unsubstitutable however carefully the application side is written — the
        application would map ``T`` and the body would hold something that is
        not ``T`` to a substitution.
        """
        from vera.types import TypeVar

        registered = _resolve_in_verifier(_APPLIED, "Box")
        assert registered == TypeVar("T"), registered

    def test_the_application_substitutes_its_argument(self) -> None:
        """``Grown``'s base is ``Nat`` — what ``Box<Cnt>`` means — and in
        particular is not the alias's own parameter wearing an ADT's name."""
        grown = _resolve_in_verifier(_APPLIED, "Grown")
        assert isinstance(grown, RefinedType), grown
        assert grown.base == NAT, grown.base
        assert not isinstance(grown.base, AdtType), (
            f"the alias's parameter leaked as an ADT name: {grown.base}"
        )


class TestTheValidProgramIsAccepted:
    """The reported symptom, and its runtime oracle."""

    def test_no_spurious_e501(self) -> None:
        result = _verify(_APPLIED)
        assert not _codes(result), (
            "the refined-return fact was dropped because the base resolved to "
            f"the alias's own parameter: {_codes(result)}"
        )

    def test_the_program_really_does_run(self) -> None:
        """The oracle: the rejected program returns 20, so the E501 was
        spurious rather than a contract the runtime also refuses."""
        assert _run(_APPLIED) == 20

    def test_the_producer_discharges_at_tier_1(self) -> None:
        """The other side of the same base: ``mk``'s own return obligation.

        A base outside the five modelled primitives is not merely unassumable
        by the caller — the PRODUCER cannot prove it either, so the refined
        return demoted to a Tier-3 runtime guard (E506).  Conservative rather
        than unsound, but a provable refinement that no longer proves.
        """
        result = _verify(_APPLIED)
        assert "E506" not in _warn_codes(result), [
            d.description[:90] for d in result.diagnostics
        ]
        assert result.summary.tier3_runtime == 0, result.summary

    def test_the_fact_is_BOUNDED_by_what_the_refinement_grants(self) -> None:
        """The over-correction direction: assuming the predicate is not the
        same as assuming anything.

        Every other test here asserts the refined-return fact SURVIVES, so a
        "fix" that resolved the base to some modelled primitive and then
        assumed the predicate unconditionally would pass all of them.  Here the
        consumer wants ``>= 100`` where the refinement grants ``>= 18``, so the
        call must still be rejected — and the runtime agrees, which is what
        separates a correct rejection from the spurious one this file exists to
        remove.
        """
        # Keyed on the function HEADER, so the substitution names `need18`
        # rather than selecting it by its position before `main`: `mk` and
        # `need18` have byte-identical contract bodies, and a positional
        # anchor would silently retarget if either moved.
        bounded = _APPLIED.replace(
            "private fn need18(@Nat -> @Nat)\n  requires(@Nat.0 >= 18)",
            "private fn need18(@Nat -> @Nat)\n  requires(@Nat.0 >= 100)",
        )
        assert (
            "private fn need18(@Nat -> @Nat)\n  requires(@Nat.0 >= 100)"
            in bounded
        ), bounded
        # ... and `mk` still grants `>= 18`, so the rejection below is about
        # what the refinement provides rather than about a callee that was
        # rewritten too.
        assert (
            "private fn mk(@Nat -> @Grown)\n  requires(@Nat.0 >= 18)" in bounded
        ), bounded
        assert bounded.count("requires(@Nat.0 >= 100)") == 1, bounded
        result = _verify(bounded)
        assert "E501" in _codes(result), (
            "the refined return grants `>= 18`; a consumer wanting `>= 100` "
            f"must not be discharged from it: {_codes(result)}"
        )
        with pytest.raises(WasmTrapError) as exc:
            _run(bounded)
        assert exc.value.kind == "contract_violation", exc.value.kind


class TestApplicationDepth:
    """One substitution is not the same as substituting to a fixed point."""

    def test_an_alias_applied_to_an_application(self) -> None:
        """``Box<Box<Cnt>>`` — the argument is itself an application.

        A resolver that substituted only the OUTER application (mapping ``T``
        to whatever ``Box<Cnt>``'s registered body is, rather than to what it
        RESOLVES to) leaves the inner parameter in place and the base is the
        phantom ADT again, one level down.
        """
        source = _APPLIED.replace("@Box<Cnt>", "@Box<Box<Cnt>>")
        assert "@Box<Box<Cnt>>" in source
        grown = _resolve_in_verifier(source, "Grown")
        assert isinstance(grown, RefinedType), grown
        assert grown.base == NAT, grown.base
        codes = _codes(_verify(source))
        assert not codes, codes
        assert _run(source) == 20

    def test_an_alias_whose_body_applies_another_alias(self) -> None:
        """``type Wrap<U> = Box<U>;`` — the parameter is passed THROUGH one
        alias into another, so the substitution has to reach the body of the
        alias the body applies, not only the outermost one."""
        source = _APPLIED.replace(
            "type Box<T> = T;",
            "type Box<T> = T;\n\ntype Wrap<U> = Box<U>;",
        ).replace("@Box<Cnt>", "@Wrap<Cnt>")
        assert "@Wrap<Cnt>" in source and "type Wrap<U> = Box<U>;" in source
        grown = _resolve_in_verifier(source, "Grown")
        assert isinstance(grown, RefinedType), grown
        assert grown.base == NAT, grown.base
        codes = _codes(_verify(source))
        assert not codes, codes
        assert _run(source) == 20


class TestAnUnmodelledBaseStillDegradesConservatively:
    """Substituting correctly must not turn the modelled-primitive gate off.

    ``@Byte`` is a real type with a real runtime representation and no Z3
    model, so a refinement over it is exactly the case the gate exists for:
    the caller must NOT assume the predicate.  Reached through an alias
    application, it is the case a fix that resolved every application to
    "something modelled" — or that dropped the gate along with the phantom ADT
    it kept failing — would silently start assuming.
    """

    _BYTE = """\
type B = Byte;

type Box<T> = T;

type SmallByte = { @Box<B> | byte_to_int(@Box<B>.0) < 100 };

private fn mk(@Byte -> @SmallByte)
  requires(byte_to_int(@Byte.0) < 100)
  ensures(true)
  effects(pure)
{
  @Byte.0
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  byte_to_int(mk(7))
}
"""

    def test_the_base_resolves_but_stays_unmodelled(self) -> None:
        """The substitution happens — the base is ``Byte``, not ``AdtType('T')``
        — and ``Byte`` is still outside the five modelled primitives."""
        from vera.types import BYTE

        small = _resolve_in_verifier(self._BYTE, "SmallByte")
        assert isinstance(small, RefinedType), small
        assert small.base == BYTE, small.base

    def test_the_predicate_still_degrades_to_a_runtime_check(self) -> None:
        """Conservative, not unsound: the producer's refined return is
        DISCLOSED as a Tier-3 runtime check rather than proved (or silently
        assumed), and the program the runtime accepts still runs.

        The ``@Nat`` sibling above proves the same obligation at Tier 1, so
        this is the gate doing its job on a base it cannot model, not the
        substitution failing to happen — ``test_the_base_resolves_but_stays_
        unmodelled`` separates the two.
        """
        result = _verify(self._BYTE)
        assert not _codes(result), _codes(result)
        assert "E506" in _warn_codes(result), [
            (d.error_code, d.description[:70]) for d in result.diagnostics
        ]
        assert result.summary.tier3_runtime > 0, (
            "an unmodelled refinement base must still be DISCLOSED as a "
            f"runtime check rather than assumed: {result.summary}"
        )
        assert _run(self._BYTE) == 7

    def test_a_consumer_is_still_not_granted_the_unmodelled_predicate(
        self,
    ) -> None:
        """The caller-side half of the same gate.

        ``SmtContext._translate_call_with_info`` assumes a refined return's
        predicate only for the five modelled primitive bases, because an
        unmodelled one has no substitutable binder and (for ``@Unit``) no
        runtime guard either — assuming it could add ``false`` and discharge
        the caller's obligations vacuously.  Substituting the application
        correctly must not smuggle a base past that gate: here a consumer wants
        the very predicate the refinement states, and must still be REJECTED,
        even though the runtime is perfectly happy.  Rejecting a program the
        runtime accepts is the honest price of a base Z3 cannot model, and it
        is the outcome that flips if the gate is widened.
        """
        source = self._BYTE.replace(
            "public fn main(@Unit -> @Int)\n"
            "  requires(true)\n"
            "  ensures(true)\n"
            "  effects(pure)\n"
            "{\n"
            "  byte_to_int(mk(7))\n"
            "}\n",
            "private fn need_small(@Byte -> @Int)\n"
            "  requires(byte_to_int(@Byte.0) < 100)\n"
            "  ensures(true)\n"
            "  effects(pure)\n"
            "{\n"
            "  byte_to_int(@Byte.0)\n"
            "}\n"
            "\n"
            "public fn main(@Unit -> @Int)\n"
            "  requires(true)\n"
            "  ensures(true)\n"
            "  effects(pure)\n"
            "{\n"
            "  need_small(mk(7))\n"
            "}\n",
        )
        assert "need_small(mk(7))" in source, source
        codes = _codes(_verify(source))
        assert "E501" in codes, codes
        assert _run(source) == 7
