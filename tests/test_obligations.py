"""Tests for vera/obligations/ — reified obligations + warm session (#222 Phase A).

Three layers:

1. **Differential oracle** — the load-bearing suite.  For every example
   program and every verify/run-level conformance program, the warm
   :class:`VerificationSession` must produce *identical* verification
   diagnostics and an identical :class:`VerifySummary` to the cold
   :func:`vera.verifier.verify` path, and a second warm run over the
   same source must match the first (solver-reuse determinism).  This
   is the safety net that lets Phase B swap incremental invalidation in
   behind the same API: any reuse-induced divergence (e.g. the
   rank-axiom staleness that ``SmtContext.reset()`` originally had)
   fails here.

2. **Summary consistency** — the reified obligation stream must mirror
   the verifier's tier bookkeeping exactly: ``tier1_verified`` equals
   the count of ``verified`` obligations, ``tier3_runtime`` equals the
   count of ``tier3`` + ``timeout`` obligations, on every corpus
   program (cold and warm).

3. **Unit tests** — obligation kinds, statuses, counterexamples,
   content-key stability and span-disambiguation, and session
   short-circuit on type errors.
"""

from __future__ import annotations

import json

from pathlib import Path

import pytest

from vera.checker import typecheck
from vera.errors import Diagnostic
from vera.obligations import ProofObligation, VerificationSession
from vera.parser import parse
from vera.resolver import ModuleResolver
from vera.transform import transform
from vera.verifier import VerifyResult, verify

REPO_ROOT = Path(__file__).parent.parent
EXAMPLES_DIR = REPO_ROOT / "examples"
CONFORMANCE_DIR = REPO_ROOT / "tests" / "conformance"


def _conformance_corpus() -> list[Path]:
    """Conformance programs whose manifest level reaches verification."""
    manifest = json.loads(
        (CONFORMANCE_DIR / "manifest.json").read_text(encoding="utf-8"),
    )
    return sorted(
        CONFORMANCE_DIR / entry["file"]
        for entry in manifest
        if entry["level"] in ("verify", "run")
    )


def _example_corpus() -> list[Path]:
    return sorted(EXAMPLES_DIR.glob("*.vera"))


CORPUS = _example_corpus() + _conformance_corpus()


def _cold_verify(path: Path) -> tuple[VerifyResult, str]:
    """Run the cold pipeline exactly as cmd_verify does."""
    source = path.read_text(encoding="utf-8")
    program = transform(parse(source, file=str(path)))
    resolver = ModuleResolver(_root=path.parent)
    resolved = resolver.resolve_imports(program, path)
    diags = resolver.errors + typecheck(
        program, source, file=str(path), resolved_modules=resolved,
    )
    errors = [d for d in diags if d.severity == "error"]
    assert not errors, f"{path.name}: corpus program failed typecheck: {errors}"
    return (
        verify(program, source, file=str(path), resolved_modules=resolved),
        source,
    )


def _diag_fingerprint(diags: list[Diagnostic]) -> list[tuple[str, ...]]:
    return [
        (
            d.severity,
            d.error_code,
            d.description,
            str(d.location.line),
            str(d.location.column),
        )
        for d in diags
    ]


def _obligation_fingerprint(
    obligations: list[ProofObligation],
) -> list[tuple[str, ...]]:
    return [
        (o.fn_name, o.kind, o.status, o.expr_text, o.content_key())
        for o in obligations
    ]


def _assert_summary_consistent(result_name: str, result: object) -> None:
    """summary counters must mirror the obligation stream exactly."""
    obligations = result.obligations  # type: ignore[attr-defined]
    summary = result.summary  # type: ignore[attr-defined]
    verified = sum(1 for o in obligations if o.status == "verified")
    tier3 = sum(1 for o in obligations if o.status in ("tier3", "timeout"))
    assert verified == summary.tier1_verified, (
        f"{result_name}: tier1_verified={summary.tier1_verified} but "
        f"{verified} obligations have status=verified"
    )
    assert tier3 == summary.tier3_runtime, (
        f"{result_name}: tier3_runtime={summary.tier3_runtime} but "
        f"{tier3} obligations have status tier3/timeout"
    )


class TestDifferentialOracle:
    """Warm session == cold verify, on the whole corpus."""

    @pytest.mark.parametrize(
        "path", CORPUS, ids=lambda p: p.name.removesuffix(".vera"),
    )
    def test_warm_equals_cold(self, path: Path) -> None:
        cold, source = _cold_verify(path)

        session = VerificationSession()
        warm1 = session.verify_source(source, file=str(path))
        warm2 = session.verify_source(source, file=str(path))

        # Diagnostics: identical content in identical order.
        assert _diag_fingerprint(warm1.verify_diagnostics) == \
            _diag_fingerprint(cold.diagnostics), (
                f"{path.name}: warm verify diagnostics diverge from cold"
            )
        # Summary: field-for-field equal.
        assert warm1.summary == cold.summary, (
            f"{path.name}: warm summary {warm1.summary} != "
            f"cold {cold.summary}"
        )
        # Obligations: same stream, same identities, same outcomes.
        assert _obligation_fingerprint(warm1.obligations) == \
            _obligation_fingerprint(cold.obligations), (
                f"{path.name}: warm obligations diverge from cold"
            )
        # Determinism: a second warm run over the same source is
        # byte-identical (solver reuse must not leak state).
        assert _diag_fingerprint(warm2.verify_diagnostics) == \
            _diag_fingerprint(warm1.verify_diagnostics)
        assert warm2.summary == warm1.summary
        assert _obligation_fingerprint(warm2.obligations) == \
            _obligation_fingerprint(warm1.obligations)

    @pytest.mark.parametrize(
        "path", CORPUS, ids=lambda p: p.name.removesuffix(".vera"),
    )
    def test_summary_obligation_consistency(self, path: Path) -> None:
        cold, source = _cold_verify(path)
        _assert_summary_consistent(f"{path.name} (cold)", cold)
        session = VerificationSession()
        warm = session.verify_source(source, file=str(path))
        _assert_summary_consistent(f"{path.name} (warm)", warm)


class TestObligationKinds:
    """Unit coverage of each obligation kind / status path."""

    def _verify_source(self, source: str) -> VerifyResult:
        program = transform(parse(source))
        diags = typecheck(program, source)
        errors = [d for d in diags if d.severity == "error"]
        assert not errors, errors
        return verify(program, source)

    def test_kinds_enumerated_for_full_contract_function(self) -> None:
        source = (
            "public fn dec(@Nat -> @Nat)\n"
            "  requires(@Nat.0 >= 1)\n"
            "  ensures(@Nat.result < @Nat.0)\n"
            "  effects(pure)\n"
            "{\n"
            "  @Nat.0 - 1\n"
            "}\n"
            "\n"
            "public fn count(@Nat -> @Nat)\n"
            "  requires(true)\n"
            "  ensures(true)\n"
            "  decreases(@Nat.0)\n"
            "  effects(pure)\n"
            "{\n"
            "  if @Nat.0 == 0 then { 0 } else { count(@Nat.0 - 1) }\n"
            "}\n"
        )
        result = self._verify_source(source)
        kinds = [(o.fn_name, o.kind, o.status) for o in result.obligations]
        assert ("dec", "requires", "verified") in kinds
        assert ("dec", "nat_sub", "verified") in kinds
        assert ("dec", "ensures", "verified") in kinds
        assert ("count", "decreases", "verified") in kinds
        # Trivial requires(true)/ensures(true) still enumerate.
        assert ("count", "requires", "verified") in kinds
        assert ("count", "ensures", "verified") in kinds

    def test_violated_ensures_carries_counterexample(self) -> None:
        source = (
            "public fn bad(@Int -> @Int)\n"
            "  requires(true)\n"
            "  ensures(@Int.result > @Int.0)\n"
            "  effects(pure)\n"
            "{\n"
            "  @Int.0\n"
            "}\n"
        )
        result = self._verify_source(source)
        violated = [o for o in result.obligations if o.status == "violated"]
        assert len(violated) == 1
        ob = violated[0]
        assert ob.kind == "ensures"
        assert ob.fn_name == "bad"
        assert ob.counterexample is not None
        # The violation is excluded from summary totals (matching the
        # verifier's `summary.total -= 1` convention) and an error
        # diagnostic was emitted alongside the obligation.
        assert any(d.severity == "error" for d in result.diagnostics)
        _assert_summary_consistent("violated-ensures", result)

    def test_violated_nat_sub_carries_e502(self) -> None:
        source = (
            "public fn under(@Nat, @Nat -> @Nat)\n"
            "  requires(true)\n"
            "  ensures(true)\n"
            "  effects(pure)\n"
            "{\n"
            "  @Nat.1 - @Nat.0\n"
            "}\n"
        )
        result = self._verify_source(source)
        violated = [o for o in result.obligations if o.status == "violated"]
        assert len(violated) == 1
        assert violated[0].kind == "nat_sub"
        assert violated[0].error_code == "E502"
        assert violated[0].counterexample is not None

    def test_generic_fn_contracts_fall_to_tier3(self) -> None:
        source = (
            "public forall<T> fn ident(@T -> @T)\n"
            "  requires(true)\n"
            "  ensures(@T.result == @T.0)\n"
            "  effects(pure)\n"
            "{\n"
            "  @T.0\n"
            "}\n"
        )
        result = self._verify_source(source)
        by_status = {
            (o.kind, o.status) for o in result.obligations
            if o.fn_name == "ident"
        }
        # Trivial requires(true) counts tier-1; the non-trivial ensures
        # falls to tier 3 with the generic-function code.
        assert ("requires", "verified") in by_status
        assert ("ensures", "tier3") in by_status
        tier3 = [o for o in result.obligations if o.status == "tier3"]
        assert all(o.error_code == "E520" for o in tier3)
        _assert_summary_consistent("generic-fn", result)

    def test_content_key_distinguishes_identical_text_at_two_sites(
        self,
    ) -> None:
        source = (
            "public fn twice(@Nat -> @Nat)\n"
            "  requires(@Nat.0 >= 2)\n"
            "  ensures(true)\n"
            "  effects(pure)\n"
            "{\n"
            "  if @Nat.0 >= 2 then { @Nat.0 - 1 } else { @Nat.0 - 1 }\n"
            "}\n"
        )
        result = self._verify_source(source)
        subs = [o for o in result.obligations if o.kind == "nat_sub"]
        assert len(subs) == 2
        assert subs[0].expr_text == subs[1].expr_text == "@Nat.0 - 1"
        # Same text, different columns → distinct identities.
        assert subs[0].content_key() != subs[1].content_key()

    def test_call_pre_keyed_by_call_site_not_callee_contract(self) -> None:
        """Two call sites violating the same callee precondition must be
        distinct obligations: the span comes from the call site, the
        expression text from the callee's contract, and the error code
        matches _report_call_violation's E501.
        """
        source = (
            "public fn need_pos(@Int -> @Int)\n"
            "  requires(@Int.0 > 0)\n"
            "  ensures(true)\n"
            "  effects(pure)\n"
            "{\n"
            "  @Int.0\n"
            "}\n"
            "\n"
            "public fn caller(@Int -> @Int)\n"
            "  requires(true)\n"
            "  ensures(true)\n"
            "  effects(pure)\n"
            "{\n"
            "  need_pos(0 - 1) + need_pos(0 - 2)\n"
            "}\n"
        )
        result = self._verify_source(source)
        call_pres = [o for o in result.obligations if o.kind == "call_pre"]
        assert len(call_pres) == 2
        assert all(o.status == "violated" for o in call_pres)
        assert all(o.error_code == "E501" for o in call_pres)
        assert all(o.fn_name == "caller" for o in call_pres)
        # Same contract text, but distinct identities via call-site spans.
        assert call_pres[0].expr_text == call_pres[1].expr_text
        assert call_pres[0].content_key() != call_pres[1].content_key()
        # Spans point at the caller's body line, not the callee contract
        # (line 2 of the source).
        assert all(o.line != 2 for o in call_pres)

    def test_content_key_stable_across_runs(self) -> None:
        source = (
            "public fn f(@Nat -> @Nat)\n"
            "  requires(@Nat.0 >= 1)\n"
            "  ensures(true)\n"
            "  effects(pure)\n"
            "{\n"
            "  @Nat.0 - 1\n"
            "}\n"
        )
        first = self._verify_source(source)
        second = self._verify_source(source)
        assert [o.content_key() for o in first.obligations] == \
            [o.content_key() for o in second.obligations]


class TestVerificationSession:
    """Session-specific behaviour not covered by the oracle."""

    def test_type_errors_short_circuit_verification(self) -> None:
        session = VerificationSession()
        result = session.verify_source(
            "public fn f(@Int -> @Int)\n"
            "  requires(true)\n"
            "  ensures(true)\n"
            "  effects(pure)\n"
            "{\n"
            '  "not an int"\n'
            "}\n"
        )
        assert not result.ok
        assert any(d.severity == "error" for d in result.check_diagnostics)
        assert result.verify_diagnostics == []
        assert result.obligations == []
        assert result.summary.total == 0

    def test_session_reuses_one_solver(self) -> None:
        session = VerificationSession()
        source = (
            "public fn f(@Int -> @Int)\n"
            "  requires(true)\n"
            "  ensures(true)\n"
            "  effects(pure)\n"
            "{\n"
            "  @Int.0\n"
            "}\n"
        )
        session.verify_source(source)
        first_smt = session._smt
        assert first_smt is not None
        session.verify_source(source)
        assert session._smt is first_smt

    def test_session_caches_last_program(self) -> None:
        session = VerificationSession()
        source = (
            "public fn f(@Int -> @Int)\n"
            "  requires(true)\n"
            "  ensures(true)\n"
            "  effects(pure)\n"
            "{\n"
            "  @Int.0\n"
            "}\n"
        )
        assert session.last_program is None
        result = session.verify_source(source)
        assert result.ok
        assert session.last_program is not None

    def test_adt_registry_resyncs_between_programs(self) -> None:
        """An ADT from program 1 must not linger into program 2."""
        session = VerificationSession()
        with_adt = (
            "public data Pair { MkPair(Int, Int) }\n"
            "\n"
            "public fn mk(@Int -> @Pair)\n"
            "  requires(true)\n"
            "  ensures(true)\n"
            "  effects(pure)\n"
            "{\n"
            "  MkPair(@Int.0, @Int.0)\n"
            "}\n"
        )
        without_adt = (
            "public fn g(@Int -> @Int)\n"
            "  requires(true)\n"
            "  ensures(true)\n"
            "  effects(pure)\n"
            "{\n"
            "  @Int.0\n"
            "}\n"
        )
        r1 = session.verify_source(with_adt)
        assert r1.ok
        smt = session._smt
        assert smt is not None
        assert "Pair" in smt._adt_registry
        r2 = session.verify_source(without_adt)
        assert r2.ok
        assert "Pair" not in smt._adt_registry
