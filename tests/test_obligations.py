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

from vera.checker import typecheck, typecheck_with_artifacts
from vera.errors import Diagnostic
from vera.obligations import ProofObligation, VerificationSession
from vera.parser import parse
from vera.resolver import ModuleResolver
from vera.transform import transform
from vera.verifier import ContractVerifier, VerifyResult, summarize, verify

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


def _checkable_conformance_corpus() -> list[Path]:
    """Every conformance program that type-checks — whatever its level (#1242).

    :func:`_conformance_corpus` above stops at the ``verify`` / ``run`` levels,
    which is the right set for the warm/cold differential (those are the
    programs CI verifies).  The ``--json`` summary/stream contract, though, is
    what `vera verify --json` promises on ANY program a user points it at, and
    the one corpus program whose stream the summary could not be reproduced
    from — ``ch08_transitive_module_import_base`` — is a ``check``-level base
    module, outside that set and therefore never asserted (#1242).  Only the
    negative fixtures are excluded here: they carry an ``expected_error`` and
    fail `check`, so verification never runs on them at all.
    """
    manifest = json.loads(
        (CONFORMANCE_DIR / "manifest.json").read_text(encoding="utf-8"),
    )
    return sorted(
        CONFORMANCE_DIR / entry["file"]
        for entry in manifest
        if not entry.get("expected_error")
    )


def _example_corpus() -> list[Path]:
    return sorted(EXAMPLES_DIR.glob("*.vera"))


CORPUS = _example_corpus() + _conformance_corpus()
CHECKABLE_CORPUS = _example_corpus() + _checkable_conformance_corpus()


def _cold_verify(path: Path) -> tuple[VerifyResult, str]:
    """Run the cold pipeline exactly as cmd_verify does — including the #747
    semantic-type side-tables (expr_types / expr_target_types), without which
    target-type-dependent obligations demote to Tier-3 and the corpus tier
    counts measure a pipeline no user runs (PR #983 review)."""
    source = path.read_text(encoding="utf-8")
    program = transform(parse(source, file=str(path)))
    resolver = ModuleResolver(_root=path.parent)
    resolved = resolver.resolve_imports(program, path)
    check_diags, artifacts = typecheck_with_artifacts(
        program, source, file=str(path), resolved_modules=resolved,
    )
    diags = resolver.errors + check_diags
    errors = [d for d in diags if d.severity == "error"]
    assert not errors, f"{path.name}: corpus program failed typecheck: {errors}"
    return (
        verify(program, source, file=str(path), resolved_modules=resolved,
               expr_types=artifacts.expr_semantic_types,
               expr_target_types=artifacts.expr_target_types),
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
    """summary counters must mirror the obligation stream exactly.

    ``tier1_verified`` equals the count of ``verified`` obligations,
    ``tier3_runtime`` the count of ``tier3`` + ``timeout`` obligations, and
    ``total`` their sum (``violated`` / ``tier3_unguarded`` are surfaced as
    diagnostics and excluded from every count).  The ``total`` leg is the
    #967 differential: a call-site precondition demotion (#882) reified a
    ``tier3`` obligation and bumped ``tier3_runtime`` but omitted the matching
    ``total`` bump, so ``tier1_verified + tier3_runtime == total + 1`` on the
    three examples that hit it — until the summary is *derived* from the
    obligation stream, which makes the desync unrepresentable.
    """
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
    assert verified + tier3 == summary.total, (
        f"{result_name}: total={summary.total} but derived "
        f"tier1_verified+tier3_runtime={verified + tier3} "
        f"(verified={verified}, tier3/timeout={tier3})"
    )


#: The statuses ``summarize`` counts toward each summary field, and the ones it
#: deliberately counts toward none.  Spelled here as a PARTITION of
#: :data:`~vera.obligations.core.ObligationStatus` so the assertion below can
#: check it is exhaustive against the Literal itself: a sixth status added to
#: the vocabulary without a decision about which bucket it belongs in would
#: otherwise vanish from the counts AND from the array's accounting in silence.
_TIER1_STATUSES = ("verified",)
_TIER3_STATUSES = ("tier3", "timeout")
_UNCOUNTED_STATUSES = ("violated", "tier3_unguarded")


def _assert_stream_partition(result_name: str, result: object) -> None:
    """The obligation array is exhaustively accounted for by the summary (#1242).

    The complement of :func:`_assert_summary_consistent`, which checks that the
    counts can be *reproduced* from the stream.  This checks the other
    direction — that nothing in the stream is unexplained — because the two
    together are what the ``verify --json`` contract in CLAUDE.md promises, and
    only their conjunction rules out the reading that produced #1242:
    ``verification.total = 2`` beside a three-entry ``obligations`` array on
    ``ch08_transitive_module_import_base`` looks like a disagreement until the
    third entry's ``violated`` status is named as counted-nowhere-on-purpose (a
    refutation discharged to no tier, surfaced as the E500 error instead).

    Two legs:

    1. every status is one of the documented five, partitioned into the tier-1
       bucket, the tier-3 bucket and the uncounted bucket; and
    2. ``len(obligations) == total + uncounted`` — so a consumer reads the
       counts by FILTERING on ``status``, and the array's length is the sum of
       the three buckets rather than of any one of them.
    """
    obligations = result.obligations  # type: ignore[attr-defined]
    summary = result.summary  # type: ignore[attr-defined]
    known = set(_TIER1_STATUSES + _TIER3_STATUSES + _UNCOUNTED_STATUSES)
    unknown = sorted({o.status for o in obligations} - known)
    assert not unknown, (
        f"{result_name}: obligation status(es) {unknown} are outside the "
        f"documented vocabulary {sorted(known)}, so they are counted by no "
        f"summary field and accounted for by no bucket"
    )
    uncounted = sum(1 for o in obligations if o.status in _UNCOUNTED_STATUSES)
    assert len(obligations) == summary.total + uncounted, (
        f"{result_name}: {len(obligations)} obligations != total="
        f"{summary.total} + {uncounted} uncounted "
        f"(violated / tier3_unguarded)"
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


class TestObligationStreamPartition:
    """The summary accounts for every reified obligation, corpus-wide (#1242).

    Over :data:`CHECKABLE_CORPUS` — every program `vera verify --json` runs on,
    including the ``check``-level base modules the differential above skips,
    which is where #1242 was hiding.  Both directions of the documented
    contract are asserted on each program: the counts are reproducible from the
    stream (:func:`_assert_summary_consistent`) and the stream is exhaustively
    bucketed by the counts (:func:`_assert_stream_partition`).
    """

    @pytest.mark.parametrize(
        "path", CHECKABLE_CORPUS, ids=lambda p: p.name.removesuffix(".vera"),
    )
    def test_stream_is_fully_accounted_for(self, path: Path) -> None:
        cold, _source = _cold_verify(path)
        _assert_summary_consistent(f"{path.name} (cold)", cold)
        _assert_stream_partition(f"{path.name} (cold)", cold)

    def test_the_1242_program_has_an_uncounted_entry(self) -> None:
        """The partition leg is not vacuous: this program really does emit an
        obligation no summary field counts.

        Without this, a corpus that happened to contain no ``violated`` and no
        ``tier3_unguarded`` obligation would satisfy
        :func:`_assert_stream_partition` for the trivial reason that
        ``uncounted == 0`` — the assertion would collapse into
        ``len(obligations) == total``, the very reading #1242 reports as
        broken, and would then break the day a corpus program acquires a
        refutation.  Pinning the shape here keeps the corpus leg honest.
        """
        path = CONFORMANCE_DIR / "ch08_transitive_module_import_base.vera"
        result, _source = _cold_verify(path)
        statuses = [o.status for o in result.obligations]
        assert "violated" in statuses, statuses
        assert len(result.obligations) > result.summary.total, (
            f"{path.name} is the #1242 shape: {len(result.obligations)} "
            f"obligations against total={result.summary.total}"
        )
        _assert_summary_consistent(path.name, result)
        _assert_stream_partition(path.name, result)


# The three examples that hit the #882 call-site precondition demotion path,
# where the pre-fix verifier bumped `tier3_runtime` without the matching
# `total`, leaving `tier1_verified + tier3_runtime == total + 1` (#967).
_SUMMARY_TOTAL_EXAMPLES = ["async_http_fanout", "http", "inference"]


class TestSummaryTotalSelfConsistency:
    """#967: `total` must equal `tier1_verified + tier3_runtime` (self-check).

    A tighter, source-independent restatement of the differential above: the
    summary a consumer reads must be internally arithmetic-consistent, with no
    reference to the obligation stream.  Fails on the three demotion examples
    until the summary is derived from the obligations.
    """

    @pytest.mark.parametrize(
        "path",
        [EXAMPLES_DIR / f"{n}.vera" for n in _SUMMARY_TOTAL_EXAMPLES],
        ids=_SUMMARY_TOTAL_EXAMPLES,
    )
    def test_total_equals_tier_sum(self, path: Path) -> None:
        result, source = _cold_verify(path)
        s = result.summary
        assert s.total == s.tier1_verified + s.tier3_runtime, (
            f"{path.name}: total={s.total} != tier1_verified"
            f"({s.tier1_verified}) + tier3_runtime({s.tier3_runtime})"
        )
        session = VerificationSession()
        warm = session.verify_source(source, file=str(path))
        ws = warm.summary
        assert ws.total == ws.tier1_verified + ws.tier3_runtime, (
            f"{path.name} (warm): total={ws.total} != tier1_verified"
            f"({ws.tier1_verified}) + tier3_runtime({ws.tier3_runtime})"
        )


class TestSummarizeUnit:
    """Direct unit coverage of :func:`summarize` (PR #974 review).

    The corpus contains no ``timeout`` obligations and no empty streams,
    so without a hand-built stream the ``timeout`` leg of the mapping and
    the empty case carry no mutation coverage.
    """

    @staticmethod
    def _obl(status: str) -> ProofObligation:
        return ProofObligation(
            fn_name="f", kind="ensures", expr_text="@Int.0 > 0",
            status=status,  # type: ignore[arg-type]
        )

    def test_empty_stream(self) -> None:
        s = summarize([])
        assert (s.tier1_verified, s.tier3_runtime, s.total) == (0, 0, 0)

    def test_all_five_statuses(self) -> None:
        stream = [
            self._obl("verified"),
            self._obl("verified"),
            self._obl("tier3"),
            self._obl("timeout"),
            self._obl("violated"),
            self._obl("tier3_unguarded"),
        ]
        s = summarize(stream)
        assert s.tier1_verified == 2  # verified only
        assert s.tier3_runtime == 2  # tier3 + timeout
        assert s.total == 4  # violated / tier3_unguarded excluded

    def test_the_status_vocabulary_is_closed_and_partitioned(self) -> None:
        """Every member of ``ObligationStatus`` lands in exactly one bucket
        (#1242).

        The test above enumerates the five statuses by hand, so a SIXTH added
        to the Literal leaves it green while ``summarize`` silently counts the
        new status nowhere — the obligation would appear in ``verify --json``'s
        array, be counted by no field, and be explained by no documented
        exclusion.  Reading the vocabulary from the Literal instead makes that
        addition fail here, at the one place that has to decide which bucket it
        belongs in.
        """
        from typing import get_args

        from vera.obligations.core import ObligationStatus

        declared = set(get_args(ObligationStatus))
        buckets = {
            "tier1": set(_TIER1_STATUSES),
            "tier3": set(_TIER3_STATUSES),
            "uncounted": set(_UNCOUNTED_STATUSES),
        }
        covered: set[str] = set()
        for name, members in buckets.items():
            assert not (covered & members), (
                f"{name} overlaps an earlier bucket on "
                f"{sorted(covered & members)}"
            )
            covered |= members
        assert covered == declared, (
            f"ObligationStatus members {sorted(declared - covered)} are in no "
            f"bucket and {sorted(covered - declared)} are in a bucket but not "
            f"in the vocabulary"
        )
        # ... and `summarize` agrees with the bucketing, one status at a time.
        for status in sorted(declared):
            s = summarize([self._obl(status)])
            assert s.tier1_verified == (1 if status in _TIER1_STATUSES else 0)
            assert s.tier3_runtime == (1 if status in _TIER3_STATUSES else 0)
            assert s.total == (0 if status in _UNCOUNTED_STATUSES else 1)


class TestSummaryDerivedOnRead:
    """The verifier's ``summary`` is a computed property over the obligation
    stream, never a stored field (#967, PR #974 review).

    A caller that drives verification piecemeal — ``register_program`` +
    ``_verify_fn`` per declaration, the ``VerificationSession`` pattern —
    must observe a summary that reflects the obligations recorded so far.
    A stored field assigned only at the end of ``verify_program`` reads as
    all-zero on this path.
    """

    def test_piecemeal_drive_summary_is_current(self) -> None:
        from vera import ast as A

        path = EXAMPLES_DIR / "increment.vera"
        source = path.read_text(encoding="utf-8")
        program = transform(parse(source, file=str(path)))
        verifier = ContractVerifier(source=source, file=str(path))
        verifier.register_program(program)
        assert verifier.summary == summarize(verifier.obligations)
        for tld in program.declarations:
            if isinstance(tld.decl, A.FnDecl):
                verifier._verify_fn(tld.decl)
                assert verifier.summary == summarize(verifier.obligations)
        assert verifier.obligations, "corpus program must record obligations"
        assert verifier.summary.total > 0, (
            "summary read after a piecemeal drive must reflect the recorded "
            "obligations, not a stale stored default"
        )


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
            "{ let @NonEmptyArray = mk(()); 0 }\n"
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

    def test_precondition_checked_inside_effect_op_argument(self) -> None:
        """A precondition-bearing call nested inside an effect-op
        argument (e.g. IO.print(need_pos(...))) must still be checked:
        the QualifiedCall is untranslatable (effects violate purity) but
        its args are walked for the E501 side effect (#776).  Pre-fix the
        QualifiedCall fell through to `return None` without recursing, so
        the nested call's requires(...) was never checked.
        """
        source = (
            "private fn need_pos(@Nat -> @String)\n"
            "  requires(@Nat.0 >= 1)\n"
            "  ensures(true)\n"
            "  effects(pure)\n"
            "{\n"
            '  "ok"\n'
            "}\n"
            "\n"
            "public fn caller(@Nat -> @Unit)\n"
            "  requires(true)\n"
            "  ensures(true)\n"
            "  effects(<IO>)\n"
            "{\n"
            "  IO.print(need_pos(@Nat.0));\n"
            "  ()\n"
            "}\n"
        )
        result = self._verify_source(source)
        e501s = [d for d in result.diagnostics if d.error_code == "E501"]
        assert len(e501s) == 1, e501s
        call_pres = [
            o for o in result.obligations if o.kind == "call_pre"
        ]
        assert len(call_pres) == 1

    def test_precondition_checked_in_every_effect_op_argument(self) -> None:
        """EVERY argument of an effect op is walked, not just the first.

        The single-argument `IO.print(need_pos(...))` case above stays green if
        the loop is degraded to `self.translate_expr(expr.args[0], env)`, so it
        cannot pin the iteration.  Two violating calls in one argument list must
        raise two independent `call_pre` obligations (#776).

        The two-argument op is a *user* effect: a built-in one cannot be
        redeclared (E152, #1149) and no built-in `IO` op takes two `String`s
        and returns `Unit`.
        """
        source = (
            "effect Audit {\n"
            "  op log(String, String -> Unit);\n"
            "}\n"
            "\n"
            "private fn need_pos(@Nat -> @String)\n"
            "  requires(@Nat.0 >= 1)\n"
            "  ensures(true)\n"
            "  effects(pure)\n"
            "{\n"
            '  "ok"\n'
            "}\n"
            "\n"
            "public fn caller(@Nat, @Nat -> @Unit)\n"
            "  requires(true)\n"
            "  ensures(true)\n"
            "  effects(<Audit>)\n"
            "{\n"
            "  Audit.log(need_pos(@Nat.1), need_pos(@Nat.0));\n"
            "  ()\n"
            "}\n"
        )
        result = self._verify_source(source)
        e501s = [d for d in result.diagnostics if d.error_code == "E501"]
        assert len(e501s) == 2, e501s
        # Distinct call sites, not one obligation reported twice.
        assert len({d.location.column for d in e501s}) == 2, e501s
        call_pres = [o for o in result.obligations if o.kind == "call_pre"]
        assert len(call_pres) == 2
        assert all(o.status == "violated" for o in call_pres), call_pres

    def test_effect_op_never_becomes_a_z3_term(self) -> None:
        """`translate_expr` must return None for a `QualifiedCall`.

        Walking the arguments is a *side effect*; the effect operation's own
        value is chosen by the handler at run time and is not a pure term, so it
        must never enter the solver.  Returning an argument's term instead
        (`return last`) is UNSOUND, and nothing else in the suite notices:

            effect Counter { op bump(Int -> Int); }
            public fn echo_bump(@Int -> @Int)
              ensures(@Int.result == @Int.0) effects(<Counter>)
            { Counter.bump(@Int.0) }

        With `return None` the postcondition is not entailed and `vera verify`
        honestly reports it as `tier3` — not proved, deferred to the runtime
        contract check.  With `return last` the body translates to `@Int.0`, so
        the verifier *proves* `@Int.result == @Int.0` and reports `verified`, for
        a claim only the handler could satisfy.  (Codegen never reads the tiers,
        so the runtime `contract_fail` guard survives either way; what breaks is
        `vera verify`'s claim.)  Mutating `return None` -> `return last` moves
        this obligation from `tier3` to `verified` and leaves all 371 other tests
        green (PR #953 review).
        """
        source = (
            "effect Counter {\n"
            "  op bump(Int -> Int);\n"
            "}\n"
            "\n"
            "public fn echo_bump(@Int -> @Int)\n"
            "  requires(true)\n"
            "  ensures(@Int.result == @Int.0)\n"
            "  effects(<Counter>)\n"
            "{\n"
            "  Counter.bump(@Int.0)\n"
            "}\n"
        )
        result = self._verify_source(source)
        posts = [o for o in result.obligations if o.kind == "ensures"]
        assert len(posts) == 1, posts
        assert posts[0].status == "tier3", (
            "the effect op's result is the handler's choice — proving "
            "`@Int.result == @Int.0` at Tier 1 is a false claim; "
            f"got status={posts[0].status!r}"
        )

    def test_effect_op_arg_assumption_does_not_escape_its_branch(self) -> None:
        """A callee postcondition assumed while walking an effect-op argument
        must not leak out of the `if` branch it was translated under.

        `_translate_call_with_info` assumes the callee's `ensures` with a bare
        `self.solver.add(z3_post)`, which lands on the solver's BASE assertion
        stack.  `check_valid` folds `_path_conditions` around the *goal* only, so
        the callee's `requires` is checked UNDER the branch guard while its
        `ensures` escapes it and becomes an unconditional fact about the caller's
        own slots (`_build_callee_env` binds the callee's params to the caller's
        terms).

        Here that fact is circular: `dec5`'s `ensures(@Nat.result == @Nat.0 - 5)`
        plus `@Nat`'s implicit `result >= 0` entails `@Nat.0 >= 5` — the very
        precondition that licensed the assumption.  Without `_guard_fact`,
        `main`'s FALSE `ensures(@Nat.0 >= 5)` proves at Tier 1, `vera verify`
        reports `ok=true` with no diagnostic, and `vera run main -- 0` traps.
        `main` (before #776) rejected this program correctly, so leaving the
        assumption unguarded would have been a soundness REGRESSION.

        `_translate_match` already guarded its injected facts this way; the call
        translator did not.  See `test_pure_call_postcondition_does_not_escape_its_branch`
        for the same leak with no effect operation anywhere — that one is
        reachable on `main` today (PR #953 review).
        """
        source = (
            "effect Slp {\n"
            "  op sleep(Nat -> Unit);\n"
            "}\n"
            "\n"
            "private fn dec5(@Nat -> @Nat)\n"
            "  requires(@Nat.0 >= 5)\n"
            "  ensures(@Nat.result == @Nat.0 - 5)\n"
            "  effects(pure)\n"
            "{\n"
            "  @Nat.0 - 5\n"
            "}\n"
            "\n"
            "public fn main(@Nat -> @Nat)\n"
            "  requires(true)\n"
            "  ensures(@Nat.0 >= 5)\n"
            "  effects(<Slp>)\n"
            "{\n"
            "  if @Nat.0 >= 5 then { Slp.sleep(dec5(@Nat.0)) } else { () };\n"
            "  @Nat.0\n"
            "}\n"
        )
        result = self._verify_source(source)
        caller_post = [
            o for o in result.obligations
            if o.fn_name == "main" and o.kind == "ensures"
        ]
        assert len(caller_post) == 1, caller_post
        assert caller_post[0].status == "violated", (
            "`ensures(@Nat.0 >= 5)` is false for @Nat.0 = 0; proving it at Tier 1 "
            "means dec5's postcondition escaped its `if` guard.  "
            f"got status={caller_post[0].status!r}"
        )
        e500s = [d for d in result.diagnostics if d.error_code == "E500"]
        assert len(e500s) == 1, e500s
        # dec5's own precondition IS legitimately discharged under the guard.
        callee_pre = [
            o for o in result.obligations
            if o.fn_name == "dec5" and o.kind == "requires"
        ]
        assert callee_pre and all(o.status == "verified" for o in callee_pre)

    def test_pure_call_postcondition_does_not_escape_its_branch(self) -> None:
        """The same leak with NO effect operation anywhere — a false Tier-1 that
        `main` shipped with, reachable through the #730 statement-position walk.

        `_translate_call_with_info` assumed the callee's `ensures` onto the
        solver's base stack.  `_translate_match` already guarded its injected
        facts (`solver.add(z3.Implies(cond, f))`); the call translator did not, so
        a fact learned under an `if` outlived the branch.

        Before `_guard_fact`, `vera verify` printed "6 verified (Tier 1)" and no
        diagnostic for this program, and `vera run main -- 0` trapped on the
        postcondition it had just "proved".  A verifier that reports MORE
        successes and FEWER diagnostics than a correct one is failing open — the
        one outcome this language cannot afford.

        Two calls in mutually-exclusive arms inject contradictory facts, the base
        solver goes UNSAT, and every obligation discharges vacuously — which is
        how this bug silently swallowed the very `E501` that #776 adds.
        """
        source = (
            "private fn dec5(@Nat -> @Nat)\n"
            "  requires(@Nat.0 >= 5)\n"
            "  ensures(@Nat.result == @Nat.0 - 5)\n"
            "  effects(pure)\n"
            "{\n"
            "  @Nat.0 - 5\n"
            "}\n"
            "\n"
            "public fn main(@Nat -> @Nat)\n"
            "  requires(true)\n"
            "  ensures(@Nat.0 >= 5)\n"
            "  effects(pure)\n"
            "{\n"
            "  if @Nat.0 >= 5 then { let @Nat = dec5(@Nat.0); () } else { () };\n"
            "  @Nat.0\n"
            "}\n"
        )
        result = self._verify_source(source)
        caller_post = [
            o for o in result.obligations
            if o.fn_name == "main" and o.kind == "ensures"
        ]
        assert len(caller_post) == 1, caller_post
        assert caller_post[0].status == "violated", (
            "`ensures(@Nat.0 >= 5)` is false for @Nat.0 = 0; proving it at Tier 1 "
            "means dec5's postcondition escaped its `if` guard.  "
            f"got status={caller_post[0].status!r}"
        )
        assert [d.error_code for d in result.diagnostics] == ["E500"], (
            result.diagnostics
        )
        # The callee's own precondition IS legitimately discharged under the guard,
        # so the guard must not over-reject.
        callee_pre = [
            o for o in result.obligations
            if o.fn_name == "dec5" and o.kind == "requires"
        ]
        assert callee_pre and all(o.status == "verified" for o in callee_pre)

    def test_guard_fact_conjoins_every_path_condition(self) -> None:
        """`_guard_fact` must conjoin ALL live path conditions, not any one of them.

        With a single path condition `And(c)` and `Or(c)` are the same formula, so
        no program with one `if` can distinguish them — mutating `z3.And` to
        `z3.Or` survives the whole behavioural suite.  A nested `if` gives two,
        and `Or` is then a strictly weaker premise, asserting the callee's fact on
        paths where it was never established.

        Checked semantically (Z3 equivalence), not by matching the formula's
        printed shape.
        """
        import z3

        from vera.smt import SmtContext

        ctx = SmtContext()
        fact = z3.Bool("fact")
        # No path conditions: the fact is unconditional, returned untouched.
        assert ctx._guard_fact(fact) is fact

        c1, c2 = z3.Bool("c1"), z3.Bool("c2")
        ctx._path_conditions.extend([c1, c2])
        guarded = ctx._guard_fact(fact)

        solver = z3.Solver()
        solver.add(z3.Not(guarded == z3.Implies(z3.And(c1, c2), fact)))
        assert solver.check() == z3.unsat, (
            f"_guard_fact must be Implies(And(*path_conditions), fact); got {guarded}"
        )

        solver = z3.Solver()
        solver.add(z3.Not(guarded == z3.Implies(z3.Or(c1, c2), fact)))
        assert solver.check() == z3.sat, (
            "_guard_fact collapsed to the Or form — the premise is too weak and "
            "the callee's fact escapes onto paths that never established it"
        )

    def test_injected_callee_facts_route_through_guard_fact(self) -> None:
        """Both facts `_translate_call_with_info` injects must be guarded.

        A wiring test, deliberately.  The callee `ensures` has a behavioural probe
        (`test_pure_call_postcondition_does_not_escape_its_branch`), but the
        refined-return predicate constrains only the call's *fresh* result
        variable, so removing its guard changes no observable verdict — un-guarding
        it survives every behavioural test in this module.  It is still wrong: an
        unsatisfiable predicate asserted at base level makes the solver UNSAT and
        discharges every obligation vacuously.  Pin the wiring instead.
        """
        import pathlib as _pathlib

        import vera.smt

        src = _pathlib.Path(vera.smt.__file__).read_text(encoding="utf-8")
        assert "self.solver.add(self._guard_fact(z3_post))" in src, (
            "the callee postcondition must be guarded by the path conditions"
        )
        assert "self.solver.add(self._guard_fact(z3_pred))" in src, (
            "the refined-return predicate must be guarded by the path conditions"
        )
        assert "self.solver.add(z3_post)" not in src, "bare, unguarded postcondition assumption"
        assert "self.solver.add(z3_pred)" not in src, "bare, unguarded refined-return assumption"

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
        # Uses string_starts_with (a Tier-1 string predicate) rather than
        # string_length, which now defers to Tier 3 (#802) and so would not
        # produce a static call-site E501 — the test is about E501 *rendering*,
        # not string_length specifically.
        source = (
            "private fn need_pos(@String -> @String)\n"
            '  requires(string_starts_with(@String.0, "x"))\n'
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
        assert 'At this call site: string_starts_with("", "x")' in d.description
        assert d.fix is not None
        assert (
            'if string_starts_with("", "x") then { need_pos("") } else { ... }'
            in d.fix
        )
        assert 'requires(string_starts_with("", "x"))' in d.fix

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

    def test_e501_substitutes_a_parameterised_slot_reference(self) -> None:
        """A PARAMETERISED callee slot substitutes too (#1208).

        The slot table is keyed by the rendered name (``Wrap<Int>``); the
        lookup used to be by the reference's bare HEAD (``Wrap``), so every
        parameterised reference missed and the whole substitution was
        abandoned — E501 silently fell back to its generic wording on exactly
        the signatures where the concrete rendering helps most.  Keying with
        :func:`vera.naming.slot_ref_key` renders the reference the same way
        the binding was rendered.

        ``type Wrap<T> = T`` keeps the parameter SMT-translatable (it resolves
        to ``Int``), which is what makes the call site reach E501 at all
        rather than the E532 Tier-3 demotion an opaque container would take.
        """
        source = (
            "type Wrap<T> = T;\n"
            "\n"
            "private fn need_pos(@Wrap<Int> -> @Int)\n"
            "  requires(@Wrap<Int>.0 > 0)\n"
            "  ensures(true)\n"
            "  effects(pure)\n"
            "{\n"
            "  0\n"
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
        e501 = [d for d in result.diagnostics if d.error_code == "E501"]
        assert len(e501) == 1
        d = e501[0]
        assert "At this call site: 0 > 0" in d.description
        assert d.fix is not None
        assert "if 0 > 0 then { need_pos(0) } else { ... }" in d.fix

    def test_e501_unmappable_slot_keeps_generic_fix(self) -> None:
        """When a precondition slot cannot be mapped to an argument,
        the message keeps the generic wording instead of guessing."""
        from vera import ast as A
        from vera.naming import EMPTY_ALIAS_ENV
        from vera.verifier import ContractVerifier

        v = ContractVerifier.__new__(ContractVerifier)
        # #1208: `slot_table` is named against the verifier's alias env; this
        # fixture bypasses `__init__`, so supply the empty one it declares no
        # aliases against.  `_decl_alias_env` too: the call site reads
        # `_current_alias_env`, which consults it (PR #1224 review) — without
        # it the fixture raises `AttributeError` instead of exercising the
        # unmappable-slot branch.
        v._alias_env = EMPTY_ALIAS_ENV
        v._decl_alias_env = None
        pre = A.Requires(
            expr=A.SlotRef(
                type_name="String", type_args=None, index=5, span=None,
            ),
            span=None,
        )
        call = A.FnCall(name="f", args=(), span=None)
        out = v._pre_at_call_site((), None, call, pre)
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

    def _cold(self, source: str, file: str | None = None) -> VerifyResult:
        """The cold twin of the session runs below, driven with the SAME
        *file* they are.

        An obligation carries the file its line number belongs to (#1220), and
        that is part of its identity, so a warm run given a file compared
        against a cold run given none is comparing two different questions —
        the fingerprint below would report a mismatch that is entirely the
        harness's.
        """
        program = transform(parse(source, file=file))
        diags = typecheck(program, source, file=file)
        assert not [d for d in diags if d.severity == "error"]
        return verify(program, source, file=file)

    def _assert_matches_cold(
        self, source: str, warm: object, file: str | None = None,
    ) -> None:
        cold = self._cold(source, file)
        assert _diag_fingerprint(
            warm.verify_diagnostics,  # type: ignore[attr-defined]
        ) == _diag_fingerprint(cold.diagnostics)
        assert warm.summary == cold.summary  # type: ignore[attr-defined]
        assert _obligation_fingerprint(
            warm.obligations,  # type: ignore[attr-defined]
        ) == _obligation_fingerprint(cold.obligations)

    def test_generic_instantiation_change_invalidates_cache(self) -> None:
        """#732: a generic's verification depends on its CALLERS' concrete
        instantiations — not on its own subtree, callees, or non-fn context,
        which is all `fn_cache_key` digests.  An edit that adds the first
        instantiation (or removes the last) must invalidate the generic's
        discharge cache, or the warm session replays a stale per-monomorphization
        result — a false Tier-1 when a now-instantiated generic's body violates.
        Regression for the PR #767 review finding."""
        uninst = (
            "private forall<T>\n"
            "fn bad(@Int, @T -> @Int)\n"
            "  requires(true)\n"
            "  ensures(@Int.result == @Int.0)\n"
            "  effects(pure)\n"
            "{ @Int.0 + 1 }\n"
        )
        inst = uninst + (
            "\n"
            "private fn caller(@Int -> @Int)\n"
            "  requires(true)\n"
            "  ensures(true)\n"
            "  effects(pure)\n"
            "{ bad(@Int.0, true) }\n"
        )
        # Uninstantiated `bad` is Tier-3 (E520); the edit instantiates it at
        # Bool, where its body violates `ensures` (E500).  The warm result must
        # match a cold verify of the edited program, not replay the stale pass.
        session = VerificationSession()
        session.verify_source(uninst, file="m.vera")
        warm = session.verify_source(inst, file="m.vera")
        self._assert_matches_cold(inst, warm, file="m.vera")
        # Reverse: removing the last instantiation flips `bad` back to Tier-3
        # rather than replaying its cached Tier-1.
        warm_back = session.verify_source(uninst, file="m.vera")
        self._assert_matches_cold(uninst, warm_back, file="m.vera")

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
        entry = FnCacheEntry([], [])
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
        assert result.ok is False  # is-False, not merely falsy — kills ok=None
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

    def test_verify_error_sets_ok_false(self) -> None:
        # A violated ensures is a Tier-1 verify error; ok must be the bool
        # False (kills ok=None / verify_errors=None / "error"-literal mutants
        # in the ok computation).
        session = VerificationSession()
        result = session.verify_source(
            "public fn f(@Int -> @Int)\n"
            "  requires(true)\n"
            "  ensures(@Int.result > @Int.0 + 1)\n"
            "  effects(pure)\n"
            "{\n"
            "  @Int.0\n"
            "}\n"
        )
        assert result.ok is False
        assert any(d.severity == "error" for d in result.verify_diagnostics)

    def test_diagnostics_carry_the_source_file(self) -> None:
        # `file` flows parse -> typecheck -> diagnostic locations; the
        # file=None mutants drop it.
        session = VerificationSession()
        result = session.verify_source(
            "public fn f(@Int -> @Int)\n"
            "  requires(true)\n"
            "  ensures(true)\n"
            "  effects(pure)\n"
            "{\n"
            '  "not an int"\n'
            "}\n",
            file="m.vera",
        )
        assert result.ok is False
        located = {
            d.location.file for d in result.check_diagnostics if d.location
        }
        assert located == {"m.vera"}

    def test_uninstantiated_generic_verifies_without_crash(self) -> None:
        # Smoke test: an uninstantiated forall<T> takes the #732
        # instantiation-key branch with an empty instance set and verifies
        # without crashing.  (Not a targeted mutant kill — the
        # _instances.get(name, set()) default is unreachable, because
        # _collect_instantiations pre-seeds a set() for every generic, so
        # that default is an equivalent mutant rather than a coverage gap.)
        session = VerificationSession()
        result = session.verify_source(
            "private forall<T>\n"
            "fn g(@T -> @T)\n"
            "  requires(true)\n"
            "  ensures(true)\n"
            "  effects(pure)\n"
            "{ @T.0 }\n"
        )
        assert result.ok is True


class TestLazyExports:
    """The PEP-562 lazy-export shim in ``vera/obligations/__init__.py``.

    Session symbols are exported lazily (via ``__getattr__``) to break
    the import cycle — ``vera.verifier`` imports ``obligations.core``,
    and ``session`` imports ``vera.verifier``.  These pin that the shim
    resolves each lazy name to the real session object and raises a
    named ``AttributeError`` for an unknown one.
    """

    def test_lazy_exports_resolve_to_session_objects(self) -> None:
        # Accessed via the *package* attribute, so each lookup goes
        # through __getattr__ (none is a direct module attribute) and
        # must BE the object defined in the session module.
        import vera.obligations as obl
        from vera.obligations import session

        assert obl.VerificationSession is session.VerificationSession
        assert obl.SessionVerifyResult is session.SessionVerifyResult
        assert obl.SessionRunStats is session.SessionRunStats

    def test_unknown_attribute_raises_named_attributeerror(self) -> None:
        import vera.obligations as obl

        with pytest.raises(
            AttributeError, match="has no attribute 'NoSuchThing'"
        ):
            _ = obl.NoSuchThing


# =====================================================================
# The disclosed path (#1363), which NO corpus program reaches
# =====================================================================

# The corpus proves nothing about disclosure: with `nat_to_int` guarded, every
# example and conformance narrowing is covered by an emitted guard, so
# `tier3_unguarded` is zero across it (pinned in
# `test_verifier_adt_decreases.py::test_overall_tier_counts`).  That is the
# desired state for the corpus and a blind spot for the differential above,
# whose whole value is running the warm and cold paths over the SAME programs.
# These shapes put the disclosed path back under it.
_DISCLOSED_SHAPE = """\
public fn mk(@Int -> @Option<Nat>)
  requires(true)
  ensures(true)
  effects(pure)
{
  int_to_nat(handle[Exn<Int>] {
    throw(@Nat) -> { nat_to_int(@Nat.0) }
  } in {
    throw(@Int.0)
  })
}

public fn use_it(@Int -> @Int)
  requires(true)
  ensures(@Int.result >= 0)
  effects(pure)
{
  match mk(@Int.0) {
    Some(@Nat) -> nat_to_int(@Nat.0),
    None -> 0
  }
}
"""

# The same program with nothing disclosed: `mk` takes a `@Nat` directly, so no
# narrowing is unguarded, and `use_it`'s postcondition is a plain Tier-1 proof.
# Paired with the shape above it separates "warm agrees with cold" from "warm
# agrees with cold because neither reached the path".
_UNDISCLOSED_CONTROL = """\
public fn mk(@Nat -> @Option<Nat>)
  requires(true)
  ensures(true)
  effects(pure)
{
  Some(@Nat.0)
}

public fn use_it(@Nat -> @Int)
  requires(true)
  ensures(@Int.result >= 0)
  effects(pure)
{
  match mk(@Nat.0) {
    Some(@Nat) -> nat_to_int(@Nat.0),
    None -> 0
  }
}
"""


def _cold_verify_source(source: str, tmp_path: Path) -> VerifyResult:
    """`_cold_verify` for a source string rather than a corpus path."""
    path = tmp_path / "d.vera"
    path.write_text(source, encoding="utf-8")
    return _cold_verify(path)[0]


class TestDisclosedDifferential:
    """Warm session == cold verify on the path the corpus does not reach."""

    def test_the_shape_actually_discloses(self, tmp_path: Path) -> None:
        """The premise, asserted before anything is compared against it.

        Without this the two differentials below would still pass if the
        shape stopped disclosing — comparing warm and cold agreement on a
        path neither one takes.
        """
        cold = _cold_verify_source(_DISCLOSED_SHAPE, tmp_path)
        statuses = [(o.kind, o.status, o.error_code) for o in cold.obligations]
        assert ("nat_bind", "tier3_unguarded", "E504") in statuses, statuses
        assert ("ensures", "tier3", "E534") in statuses, statuses

        control = _cold_verify_source(_UNDISCLOSED_CONTROL, tmp_path)
        assert not [o for o in control.obligations
                    if o.status == "tier3_unguarded"], (
            "the control discloses too, so it controls for nothing"
        )

    @pytest.mark.parametrize(
        "source", [_DISCLOSED_SHAPE, _UNDISCLOSED_CONTROL],
        ids=["disclosed", "control"],
    )
    def test_warm_equals_cold_on_the_disclosed_path(
        self, source: str, tmp_path: Path,
    ) -> None:
        """The warm path assembles its stream from cached per-function slices
        and so never called the shared disclosure rule at all: it answered
        "nothing disclosed", proved at Tier 1 from facts cold withholds, and
        diverged in the generous direction.  Divergence toward MORE proof is
        the one that matters, which is why this is asserted rather than left
        to the corpus.
        """
        path = tmp_path / "d.vera"
        path.write_text(source, encoding="utf-8")
        cold = _cold_verify(path)[0]

        session = VerificationSession()
        warm1 = session.verify_source(source, file=str(path))
        warm2 = session.verify_source(source, file=str(path))

        assert warm1.summary == cold.summary, (
            f"warm summary {warm1.summary} != cold {cold.summary}"
        )
        assert _obligation_fingerprint(warm1.obligations) == \
            _obligation_fingerprint(cold.obligations), (
                "warm obligations diverge from cold on the disclosed path"
            )
        assert _diag_fingerprint(warm1.verify_diagnostics) == \
            _diag_fingerprint(cold.diagnostics)
        # Re-running on the warm session must not drift: the disclosed set is
        # carried across runs AND folded into the cache key, so a second run
        # replays slices only if they were proved under the same set.
        assert _obligation_fingerprint(warm2.obligations) == \
            _obligation_fingerprint(warm1.obligations)
        assert warm2.summary == warm1.summary
        # Diagnostics are assembled SEPARATELY from obligations, so a
        # replay-ordering regression that leaves the stream and the summary
        # intact shows up only here (CR PR-review).
        assert _diag_fingerprint(warm2.verify_diagnostics) == \
            _diag_fingerprint(warm1.verify_diagnostics)

    def test_a_session_does_not_carry_disclosure_into_the_next_program(
        self, tmp_path: Path,
    ) -> None:
        """The disclosed set is per-run state on a session that outlives it.

        A session that has just verified a disclosing program must not demote
        the NEXT program's contracts on the strength of the previous one's
        disclosures — the names are unrelated, and an editor session verifies
        file after file on one warm session.  Checked against cold on the
        control, which is the verdict a fresh process gives.
        """
        session = VerificationSession()
        disclosing = tmp_path / "a.vera"
        disclosing.write_text(_DISCLOSED_SHAPE, encoding="utf-8")
        session.verify_source(_DISCLOSED_SHAPE, file=str(disclosing))

        control_path = tmp_path / "b.vera"
        control_path.write_text(_UNDISCLOSED_CONTROL, encoding="utf-8")
        after = session.verify_source(
            _UNDISCLOSED_CONTROL, file=str(control_path),
        )
        cold = _cold_verify(control_path)[0]
        assert after.summary == cold.summary, (
            f"a prior program's disclosures changed this one's verdict: "
            f"{after.summary} != cold {cold.summary}"
        )
        assert _obligation_fingerprint(after.obligations) == \
            _obligation_fingerprint(cold.obligations)
        assert _diag_fingerprint(after.verify_diagnostics) == \
            _diag_fingerprint(cold.diagnostics), (
                "the control's DIAGNOSTICS differ from cold after a prior "
                "program disclosed, even though its obligations match"
            )
        assert not [o for o in after.obligations
                    if o.error_code == "E534"], (
            "the control's contracts were demoted by another program's "
            "disclosures"
        )
