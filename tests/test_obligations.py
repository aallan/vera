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

    def test_refine_bind_kind_enumerated(self) -> None:
        """#746: a refinement narrowing records a `refine_bind` obligation —
        discharged at the call argument and at the refined return position."""
        source = (
            "type PosInt = { @Int | @Int.0 > 0 };\n"
            "\n"
            "public fn use(@PosInt -> @Int)\n"
            "  requires(true) ensures(true) effects(pure)\n"
            "{ @PosInt.0 }\n"
            "\n"
            "public fn mk(@Int -> @PosInt)\n"
            "  requires(@Int.0 > 0) ensures(true) effects(pure)\n"
            "{ @Int.0 }\n"
            "\n"
            "public fn caller(@Unit -> @Int)\n"
            "  requires(true) ensures(true) effects(pure)\n"
            "{ use(5) }\n"
        )
        result = self._verify_source(source)
        kinds = [(o.fn_name, o.kind, o.status) for o in result.obligations]
        # call argument `use(5)` discharges `5 > 0`
        assert ("caller", "refine_bind", "verified") in kinds
        # `mk`'s body discharges the `@PosInt` return predicate
        assert ("mk", "refine_bind", "verified") in kinds
        _assert_summary_consistent("refine-bind", result)

    def test_refine_bind_violation_carries_e505(self) -> None:
        """A refuted refinement narrowing records `refine_bind`/`violated`
        with error code E505 and a counterexample."""
        source = (
            "type PosInt = { @Int | @Int.0 > 0 };\n"
            "\n"
            "public fn bad(@Int -> @PosInt)\n"
            "  requires(true) ensures(true) effects(pure)\n"
            "{ @Int.0 }\n"
        )
        result = self._verify_source(source)
        violated = [
            o for o in result.obligations
            if o.kind == "refine_bind" and o.status == "violated"
        ]
        assert len(violated) == 1
        assert violated[0].error_code == "E505"
        assert violated[0].counterexample is not None
        _assert_summary_consistent("refine-bind-violation", result)

    def test_refine_bind_tier3_runtime_checked(self) -> None:
        """A Tier-3 refinement narrowing (non-primitive `Array` base) is
        recorded as a runtime-checked `tier3` with an informational E506 — not
        `tier1_verified` and not silently dropped — because codegen guards the
        predicate at the function boundary.  Exercises the `tier3_runtime`
        bookkeeping `_assert_summary_consistent` checks (status `tier3` ↔
        `summary.tier3_runtime`)."""
        source = (
            "type NonEmptyArray = "
            "{ @Array<Int> | array_length(@Array<Int>.0) > 0 };\n"
            "\n"
            "public fn head(@NonEmptyArray -> @Int)\n"
            "  requires(true) ensures(true) effects(pure)\n"
            "{ @NonEmptyArray.0[0] }\n"
            "\n"
            "public fn caller(@Unit -> @Int)\n"
            "  requires(true) ensures(true) effects(pure)\n"
            "{ head([42, 1, 2]) }\n"
        )
        result = self._verify_source(source)
        tier3 = [
            o for o in result.obligations
            if o.kind == "refine_bind" and o.status == "tier3"
        ]
        assert len(tier3) == 1
        assert tier3[0].error_code == "E506"
        # Counted as a runtime check, never a silent pass or a Tier-1.
        assert not any(
            o.kind == "refine_bind" and o.status == "verified"
            for o in result.obligations
        )
        assert result.summary.tier3_runtime >= 1
        _assert_summary_consistent("refine-bind-tier3", result)

    def test_refine_bind_unguarded_internal_site(self) -> None:
        """An *internal* Tier-3 refinement narrowing (a `let` over a
        non-primitive base) has no codegen guard, so it is `tier3_unguarded`
        and excluded from the totals — NOT overstated as a runtime-checked
        `tier3_runtime` (the guarded/unguarded distinction mirrors `nat_bind`)."""
        source = (
            "type NonEmptyArray = "
            "{ @Array<Int> | array_length(@Array<Int>.0) > 0 };\n"
            "\n"
            "private fn mk(@Unit -> @Array<Int>)\n"
            "  requires(true) ensures(true) effects(pure)\n"
            "{ [1, 2] }\n"
            "\n"
            "private fn f(@Unit -> @Int)\n"
            "  requires(true) ensures(true) effects(pure)\n"
            "{ let @NonEmptyArray = mk(@Unit.0); 0 }\n"
        )
        result = self._verify_source(source)
        unguarded = [
            o for o in result.obligations
            if o.kind == "refine_bind" and o.status == "tier3_unguarded"
        ]
        assert len(unguarded) == 1
        assert unguarded[0].error_code == "E506"
        # Excluded from totals and NOT counted as a runtime check.
        assert not any(
            o.kind == "refine_bind" and o.status == "tier3"
            for o in result.obligations
        )
        _assert_summary_consistent("refine-bind-unguarded", result)

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
        # Same contract text (the callee's precondition, rendered by
        # format_expr without decoration), distinct identities via
        # call-site spans.
        assert call_pres[0].expr_text == "@Int.0 > 0"
        assert call_pres[1].expr_text == "@Int.0 > 0"
        assert call_pres[0].content_key() != call_pres[1].content_key()
        # Both spans pin the caller's body line (line 14, the two calls)
        # — not line 2, where the callee's contract lives — and the two
        # call sites are distinguished by column.
        assert [o.line for o in call_pres] == [14, 14]
        assert call_pres[0].column != call_pres[1].column

    def test_call_in_let_records_violation_once(self) -> None:
        """A violating call in a `let` RHS yields exactly ONE E501
        diagnostic and ONE call_pre obligation (#727).

        The @Nat-subtraction walker re-translates let RHSes to rebuild
        its slot environment; before the fix, that second translation
        re-recorded the same CallViolation, doubling both the
        diagnostic and the obligation for the SAME call site.  The SMT
        layer now dedups by (call node, precondition) identity at
        recording time, so repeat translation passes collapse to one
        violation.
        """
        source = (
            "private fn need_pos(@Int -> @Int)\n"
            "  requires(@Int.0 > 0)\n"
            "  ensures(true)\n"
            "  effects(pure)\n"
            "{\n"
            "  @Int.0\n"
            "}\n"
            "\n"
            "public fn caller(-> @Int)\n"
            "  requires(true)\n"
            "  ensures(true)\n"
            "  effects(pure)\n"
            "{\n"
            "  let @Int = need_pos(0);\n"
            "  @Int.0\n"
            "}\n"
        )
        result = self._verify_source(source)
        e501s = [d for d in result.diagnostics if d.error_code == "E501"]
        assert len(e501s) == 1
        call_pres = [
            o for o in result.obligations if o.kind == "call_pre"
        ]
        assert len(call_pres) == 1
        assert call_pres[0].status == "violated"

    def test_walker_only_call_site_still_detected(self) -> None:
        """A violating call that ONLY the @Nat-subtraction walker ever
        translates — a subtraction operand inside an ExprStmt, which
        the body pass skips — must still record its E501 exactly once
        (#727 review round: blanket suppression of the walker hid
        these entirely; identity dedup keeps the sole recorder).
        """
        source = (
            "private fn need_pos(@Nat -> @Nat)\n"
            "  requires(@Nat.0 >= 1)\n"
            "  ensures(true)\n"
            "  effects(pure)\n"
            "{\n"
            "  @Nat.0\n"
            "}\n"
            "\n"
            "private fn consume(@Nat -> @Nat)\n"
            "  requires(true)\n"
            "  ensures(true)\n"
            "  effects(pure)\n"
            "{\n"
            "  @Nat.0\n"
            "}\n"
            "\n"
            "public fn caller(@Nat -> @Nat)\n"
            "  requires(true)\n"
            "  ensures(true)\n"
            "  effects(pure)\n"
            "{\n"
            "  consume(need_pos(@Nat.0) - 1);\n"
            "  @Nat.0\n"
            "}\n"
        )
        result = self._verify_source(source)
        e501s = [d for d in result.diagnostics if d.error_code == "E501"]
        assert len(e501s) == 1
        call_pres = [
            o for o in result.obligations if o.kind == "call_pre"
        ]
        assert len(call_pres) == 1

    def test_let_nat_subtraction_records_once(self) -> None:
        """A violating call as a @Nat-subtraction operand in a let RHS
        is visited by THREE translation passes (body, walker env
        rebuild, walker operand discharge) — pre-fix it recorded three
        E501s; identity dedup collapses them to one (#727).
        """
        source = (
            "private fn need_pos(@Nat -> @Nat)\n"
            "  requires(@Nat.0 >= 1)\n"
            "  ensures(true)\n"
            "  effects(pure)\n"
            "{\n"
            "  @Nat.0\n"
            "}\n"
            "\n"
            "public fn caller(@Nat -> @Nat)\n"
            "  requires(true)\n"
            "  ensures(true)\n"
            "  effects(pure)\n"
            "{\n"
            "  let @Nat = need_pos(@Nat.0) - 1;\n"
            "  @Nat.0\n"
            "}\n"
        )
        result = self._verify_source(source)
        e501s = [d for d in result.diagnostics if d.error_code == "E501"]
        assert len(e501s) == 1
        call_pres = [
            o for o in result.obligations if o.kind == "call_pre"
        ]
        assert len(call_pres) == 1

    def test_pipe_call_violation_records_once(self) -> None:
        """A violating call reached via pipe desugaring records once.

        Pipe translation constructs a fresh synthetic ``ast.FnCall``
        on every pass, so object-identity dedup misses repeat visits —
        the dedup keys on the (stable) call-site span instead (#729
        round 2).
        """
        source = (
            "private fn need_pos(@Nat -> @Nat)\n"
            "  requires(@Nat.0 >= 1)\n"
            "  ensures(true)\n"
            "  effects(pure)\n"
            "{\n"
            "  @Nat.0\n"
            "}\n"
            "\n"
            "public fn caller(@Nat -> @Nat)\n"
            "  requires(true)\n"
            "  ensures(true)\n"
            "  effects(pure)\n"
            "{\n"
            "  let @Nat = (@Nat.0 |> need_pos()) - 1;\n"
            "  @Nat.0\n"
            "}\n"
        )
        result = self._verify_source(source)
        e501s = [d for d in result.diagnostics if d.error_code == "E501"]
        assert len(e501s) == 1
        call_pres = [
            o for o in result.obligations if o.kind == "call_pre"
        ]
        assert len(call_pres) == 1

    def test_e501_renders_precondition_in_call_site_terms(self) -> None:
        """E501's message states the precondition with the actual
        arguments substituted, and the fix shows concrete code — the
        guard with the rendered call, and the requires() to add.
        """
        source = (
            "private fn need_pos(@String -> @String)\n"
            "  requires(string_length(@String.0) > 0)\n"
            "  ensures(true)\n"
            "  effects(pure)\n"
            "{\n"
            "  @String.0\n"
            "}\n"
            "\n"
            "public fn caller(-> @Int)\n"
            "  requires(true)\n"
            "  ensures(true)\n"
            "  effects(pure)\n"
            "{\n"
            '  let @String = need_pos("");\n'
            "  0\n"
            "}\n"
        )
        result = self._verify_source(source)
        e501 = [d for d in result.diagnostics if d.error_code == "E501"]
        assert len(e501) == 1
        d = e501[0]
        assert 'At this call site: string_length("") > 0' in d.description
        assert d.fix is not None
        assert (
            'if string_length("") > 0 then { need_pos("") } else { ... }'
            in d.fix
        )
        assert "requires(string_length(\"\") > 0)" in d.fix

    def test_e501_substitution_resolves_de_bruijn_order(self) -> None:
        """Slot substitution must honour De Bruijn most-recent-first:
        for callee (@Int, @Int) with requires(@Int.1 > @Int.0),
        @Int.1 is parameter 1 and @Int.0 is parameter 2."""
        source = (
            "private fn cmp(@Int, @Int -> @Int)\n"
            "  requires(@Int.1 > @Int.0)\n"
            "  ensures(true)\n"
            "  effects(pure)\n"
            "{\n"
            "  @Int.0\n"
            "}\n"
            "\n"
            "public fn caller(-> @Int)\n"
            "  requires(true)\n"
            "  ensures(true)\n"
            "  effects(pure)\n"
            "{\n"
            "  let @Int = cmp(1, 2);\n"
            "  @Int.0\n"
            "}\n"
        )
        result = self._verify_source(source)
        e501 = [d for d in result.diagnostics if d.error_code == "E501"]
        assert len(e501) == 1
        assert "At this call site: 1 > 2" in e501[0].description

    def test_e501_unmappable_slot_keeps_generic_fix(self) -> None:
        """When a precondition slot cannot be mapped to an argument,
        the message keeps the generic wording instead of guessing."""
        from vera import ast as A
        from vera.verifier import ContractVerifier

        v = ContractVerifier.__new__(ContractVerifier)
        pre = A.Requires(
            expr=A.SlotRef(
                type_name="String", type_args=None, index=5, span=None,
            ),
            span=None,
        )
        call = A.FnCall(name="f", args=(), span=None)
        out = v._pre_at_call_site((), call, pre)
        assert out is None

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


class TestIncrementalInvalidation:
    """#222 Phase B: discharge cache + invalidation soundness.

    The corpus-wide differential oracle (TestDifferentialOracle) already
    pins replay == cold on every corpus program — its warm-twice leg
    goes through the cache.  These tests pin the *invalidation rules*
    and the cache's observability/eviction behaviour on targeted edits.
    """

    BASE = (
        "public fn helper(@Int -> @Int)\n"
        "  requires(@Int.0 > 0)\n"
        "  ensures(@Int.result >= 0)\n"
        "  effects(pure)\n"
        "{\n"
        "  @Int.0\n"
        "}\n"
        "\n"
        "public fn top(@Int -> @Int)\n"
        "  requires(@Int.0 > 1)\n"
        "  ensures(true)\n"
        "  effects(pure)\n"
        "{\n"
        "  helper(@Int.0)\n"
        "}\n"
    )

    def _cold(self, source: str) -> VerifyResult:
        program = transform(parse(source))
        diags = typecheck(program, source)
        assert not [d for d in diags if d.severity == "error"]
        return verify(program, source)

    def _assert_matches_cold(self, source: str, warm: object) -> None:
        cold = self._cold(source)
        assert _diag_fingerprint(
            warm.verify_diagnostics,  # type: ignore[attr-defined]
        ) == _diag_fingerprint(cold.diagnostics)
        assert warm.summary == cold.summary  # type: ignore[attr-defined]
        assert _obligation_fingerprint(
            warm.obligations,  # type: ignore[attr-defined]
        ) == _obligation_fingerprint(cold.obligations)

    def test_identical_source_replays_everything(self) -> None:
        session = VerificationSession()
        session.verify_source(self.BASE)
        assert session.last_run_stats.verified_fns == 2
        result = session.verify_source(self.BASE)
        assert session.last_run_stats.replayed_fns == 2
        assert session.last_run_stats.verified_fns == 0
        self._assert_matches_cold(self.BASE, result)

    def test_body_edit_reverifies_only_that_function(self) -> None:
        """Callee body change must NOT invalidate callers — bodies are
        never read across the call boundary (only contracts are)."""
        session = VerificationSession()
        session.verify_source(self.BASE)
        edited = self.BASE.replace("  @Int.0\n}", "  @Int.0 + 0\n}", 1)
        result = session.verify_source(edited)
        assert session.last_run_stats.verified_fns == 1  # helper only
        assert session.last_run_stats.replayed_fns == 1  # top replays
        self._assert_matches_cold(edited, result)

    def test_callee_contract_edit_invalidates_caller(self) -> None:
        """Callers check callee preconditions and assume callee
        postconditions, so a contract change must re-verify them."""
        session = VerificationSession()
        session.verify_source(self.BASE)
        edited = self.BASE.replace(
            "requires(@Int.0 > 0)", "requires(@Int.0 > 2)",
        )
        result = session.verify_source(edited)
        assert session.last_run_stats.verified_fns == 2
        assert session.last_run_stats.replayed_fns == 0
        # The tightened precondition is now violated at top's call site
        # — proof the caller genuinely re-verified.
        call_pres = [
            o for o in result.obligations if o.kind == "call_pre"
        ]
        assert [o.status for o in call_pres] == ["violated"]
        self._assert_matches_cold(edited, result)

    def test_span_shift_invalidates_conservatively(self) -> None:
        """Inserting a line above shifts every span; cached output
        carries spans/source_lines, so exact replay is impossible and
        everything must re-verify (conservative by design)."""
        session = VerificationSession()
        session.verify_source(self.BASE)
        shifted = "-- a leading comment\n" + self.BASE
        result = session.verify_source(shifted)
        assert session.last_run_stats.verified_fns == 2
        assert session.last_run_stats.replayed_fns == 0
        self._assert_matches_cold(shifted, result)

    def test_adt_edit_invalidates_everything(self) -> None:
        """Non-function declarations are program context: any change
        invalidates all functions (coarse, sound)."""
        with_adt = (
            "public data Box { MkBox(Int) }\n\n" + self.BASE
        )
        session = VerificationSession()
        session.verify_source(with_adt)
        assert session.last_run_stats.verified_fns == 2
        edited = with_adt.replace(
            "MkBox(Int)", "MkBox(Int, Int)",
        )
        result = session.verify_source(edited)
        assert session.last_run_stats.verified_fns == 2
        assert session.last_run_stats.replayed_fns == 0
        self._assert_matches_cold(edited, result)

    def test_cross_program_no_stale_bleed(self) -> None:
        """Identical source under a different file name is a different
        program for caching purposes: the file is baked into every
        cached diagnostic's location, so nothing may replay across
        file boundaries.

        The source deliberately violates a postcondition so each run
        produces at least one diagnostic — otherwise the location-file
        assertion below would be vacuously true over an empty list.
        """
        source = self.BASE.replace(
            "ensures(@Int.result >= 0)", "ensures(@Int.result < 0)", 1,
        )
        session = VerificationSession()
        first = session.verify_source(source, file="prog_a.vera")
        assert session.last_run_stats.verified_fns == 2
        assert len(first.verify_diagnostics) > 0
        assert all(
            d.location.file == "prog_a.vera"
            for d in first.verify_diagnostics
        )
        result = session.verify_source(source, file="prog_b.vera")
        assert session.last_run_stats.verified_fns == 2
        assert session.last_run_stats.replayed_fns == 0
        # Non-vacuous: the violated ensures guarantees a diagnostic,
        # and it must carry the SECOND file's name — a stale replay
        # from prog_a would surface here as a prog_a.vera location.
        assert len(result.verify_diagnostics) > 0
        assert all(
            d.location.file == "prog_b.vera"
            for d in result.verify_diagnostics
        )

    def test_timeout_outcomes_are_never_cached(
        self, monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        """Hard rail: a function whose slice contains a timeout-status
        obligation must be re-verified every run, never replayed."""
        from vera.smt import SmtContext, SmtResult

        source = (
            "public fn f(@Int -> @Int)\n"
            "  requires(true)\n"
            "  ensures(@Int.result == @Int.0)\n"
            "  effects(pure)\n"
            "{\n"
            "  @Int.0\n"
            "}\n"
        )
        original = SmtContext.check_valid

        def always_unknown(
            self: SmtContext, goal: object, assumptions: object,
        ) -> SmtResult:
            return SmtResult(status="unknown")

        monkeypatch.setattr(SmtContext, "check_valid", always_unknown)
        session = VerificationSession()
        r1 = session.verify_source(source)
        assert any(o.status == "timeout" for o in r1.obligations)
        assert session.last_run_stats.verified_fns == 1

        # Second run with the solver healthy again: the function must
        # NOT replay the stale timeout — it re-verifies and succeeds.
        monkeypatch.setattr(SmtContext, "check_valid", original)
        r2 = session.verify_source(source)
        assert session.last_run_stats.verified_fns == 1
        assert session.last_run_stats.replayed_fns == 0
        assert all(o.status == "verified" for o in r2.obligations)

    def test_cache_eviction_bound(self) -> None:
        """The FIFO bound evicts oldest entries past max_entries."""
        from vera.obligations.cache import DischargeCache, FnCacheEntry

        cache = DischargeCache(max_entries=2)
        entry = FnCacheEntry([], [], 0, 0, 0)
        cache.put("a", entry)
        cache.put("b", entry)
        cache.put("c", entry)
        assert len(cache) == 2
        assert cache.get("a") is None
        assert cache.get("b") is not None
        assert cache.get("c") is not None


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
