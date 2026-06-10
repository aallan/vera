"""Warm incremental verification session — the #222 daemon object.

A :class:`VerificationSession` owns one long-lived Z3 solver (inside a
:class:`~vera.smt.SmtContext`) and re-verifies full programs through it,
calling :meth:`SmtContext.reset` between functions instead of paying the
fresh-``z3.Solver()`` construction cost per function that the cold
:func:`vera.verifier.verify` path pays.

Phase A established the API and the warm re-verify-everything path.
Phase B adds the discharge cache behind that same API: each top-level
function's verification output (obligations, diagnostics, summary
deltas) is cached under an invalidation key covering everything its
verification reads (see :mod:`vera.obligations.cache` for the soundness
model), and functions whose key is unchanged replay their cached output
in declaration order instead of re-entering Z3.  The differential
oracle in ``tests/test_obligations.py`` pins replay == re-verify ==
cold on the full corpus.

Scope notes (matching the #222 plan):

- Single-file project model: imports resolve from disk via
  :class:`~vera.resolver.ModuleResolver` when *file* is given.  Buffer-
  aware resolution (unsaved editor buffers for imported modules) is a
  Phase C concern, wired in when the LSP document store exists.
- The session is not thread-safe — Z3 contexts are not thread-safe, so
  the LSP layer (Phase D) serialises all verification through a single
  session-owning worker.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from pathlib import Path

from vera import ast
from vera.errors import Diagnostic
from vera.obligations.cache import (
    DischargeCache,
    FnCacheEntry,
    fn_cache_key,
    program_context_hash,
)
from vera.obligations.core import ProofObligation
from vera.parser import parse
from vera.resolver import ModuleResolver, ResolvedModule
from vera.smt import SmtContext
from vera.transform import transform
from vera.verifier import ContractVerifier, VerifySummary


@dataclass
class SessionVerifyResult:
    """Outcome of one ``verify_source`` call.

    ``check_diagnostics`` holds parse/type-check output;
    ``verify_diagnostics`` holds the contract-verification output and is
    field-for-field comparable with ``vera.verifier.VerifyResult
    .diagnostics`` for the same source (the differential-oracle
    contract).  ``ok`` is False when any error-severity diagnostic is
    present in either list.
    """

    ok: bool
    check_diagnostics: list[Diagnostic] = field(default_factory=list)
    verify_diagnostics: list[Diagnostic] = field(default_factory=list)
    summary: VerifySummary = field(default_factory=VerifySummary)
    obligations: list[ProofObligation] = field(default_factory=list)

    @property
    def diagnostics(self) -> list[Diagnostic]:
        """All diagnostics in pipeline order (check first, then verify)."""
        return self.check_diagnostics + self.verify_diagnostics


@dataclass
class SessionRunStats:
    """Per-run cache observability (#222 Phase B).

    Additive diagnostics surface: lets tests assert the cache actually
    replayed (the differential oracle alone would pass trivially if
    every lookup missed) and gives the LSP layer a hit-rate signal.
    """

    replayed_fns: int = 0
    verified_fns: int = 0


class VerificationSession:
    """Long-lived warm-Z3 verification daemon (#222 Phase A).

    One ``SmtContext`` (one ``z3.Solver``) is created lazily on first
    use and reused for every subsequent verification; per-function and
    per-program state is cleared via ``reset()`` and explicit registry
    resync rather than reconstruction.
    """

    def __init__(self, timeout_ms: int = 10_000) -> None:
        self._timeout_ms = timeout_ms
        self._smt: SmtContext | None = None
        # Phase B: per-function discharge cache (see cache.py for the
        # invalidation-key soundness model).
        self._cache = DischargeCache()
        # Cached AST of the last successfully verified program.
        self.last_program: ast.Program | None = None
        # Cache observability for the most recent verify_source call.
        self.last_run_stats = SessionRunStats()

    def _acquire_smt(self) -> SmtContext:
        """Return the session's warm context, creating it on first use.

        Cross-*program* hygiene happens here: the ADT registry persists
        across functions of one program by design (reset() keeps it),
        but a new program may have removed or changed ADTs, so the
        registry is cleared before each program and repopulated by the
        verifier's per-function registration loop.  The function
        lookups are rebound per function by the verifier itself.
        """
        if self._smt is None:
            self._smt = SmtContext(timeout_ms=self._timeout_ms)
        self._smt._adt_registry.clear()
        self._smt._ctor_to_adt.clear()
        return self._smt

    def verify_source(
        self,
        source: str,
        file: str | None = None,
        resolved_modules: list[ResolvedModule] | None = None,
    ) -> SessionVerifyResult:
        """Parse, type-check, and verify *source* on the warm session.

        Mirrors the ``vera verify`` CLI pipeline (cmd_verify): imports
        are resolved from disk relative to *file* when given (and
        *resolved_modules* not supplied); type errors short-circuit
        verification exactly as the CLI does.  Parse and transform
        errors propagate as their usual exceptions (``ParseError`` /
        ``TransformError``) — the LSP layer maps those to diagnostics
        at the transport boundary (Phase D).
        """
        tree = parse(source, file=file)
        program = transform(tree)

        resolver_errors: list[Diagnostic] = []
        if resolved_modules is None and file is not None:
            path = Path(file)
            resolver = ModuleResolver(_root=path.parent)
            resolved_modules = resolver.resolve_imports(program, path)
            resolver_errors = resolver.errors

        from vera.checker import typecheck
        check_diags = resolver_errors + typecheck(
            program, source, file=file, resolved_modules=resolved_modules,
        )
        if any(d.severity == "error" for d in check_diags):
            # Type errors: skip verification, matching cmd_verify.
            return SessionVerifyResult(
                ok=False, check_diagnostics=check_diags,
            )

        smt = self._acquire_smt()
        verifier = ContractVerifier(
            source=source,
            file=file,
            timeout_ms=self._timeout_ms,
            resolved_modules=resolved_modules,
            shared_smt=smt,
        )
        verifier.register_program(program)

        # Phase B incremental drive: walk declarations in order,
        # replaying cached output for functions whose invalidation key
        # is unchanged and re-verifying the rest.  Declaration order is
        # what the cold path produces, so interleaving replayed and
        # fresh slices in this order keeps the output stream identical.
        context_hash = program_context_hash(
            program,
            self._timeout_ms,
            file,
            tuple(
                repr(m) for m in (resolved_modules or [])
            ),
        )
        fn_map: dict[str, ast.FnDecl] = {
            tld.decl.name: tld.decl
            for tld in program.declarations
            if isinstance(tld.decl, ast.FnDecl)
        }

        stats = SessionRunStats()
        out_diags: list[Diagnostic] = list(verifier.errors)
        out_obls: list[ProofObligation] = list(verifier.obligations)
        summary = VerifySummary()

        for tld in program.declarations:
            if not isinstance(tld.decl, ast.FnDecl):
                continue
            decl = tld.decl
            key = fn_cache_key(decl, fn_map, context_hash)
            cached = self._cache.get(key)
            if cached is not None:
                out_diags.extend(cached.diagnostics)
                out_obls.extend(cached.obligations)
                summary.tier1_verified += cached.tier1_delta
                summary.tier3_runtime += cached.tier3_delta
                summary.total += cached.total_delta
                stats.replayed_fns += 1
                continue

            d0 = len(verifier.errors)
            o0 = len(verifier.obligations)
            t1_0 = verifier.summary.tier1_verified
            t3_0 = verifier.summary.tier3_runtime
            tot_0 = verifier.summary.total
            verifier._verify_fn(decl)
            entry = FnCacheEntry(
                diagnostics=list(verifier.errors[d0:]),
                obligations=list(verifier.obligations[o0:]),
                tier1_delta=verifier.summary.tier1_verified - t1_0,
                tier3_delta=verifier.summary.tier3_runtime - t3_0,
                total_delta=verifier.summary.total - tot_0,
            )
            self._cache.put(key, entry)
            out_diags.extend(entry.diagnostics)
            out_obls.extend(entry.obligations)
            summary.tier1_verified += entry.tier1_delta
            summary.tier3_runtime += entry.tier3_delta
            summary.total += entry.total_delta
            stats.verified_fns += 1

        self.last_program = program
        self.last_run_stats = stats

        verify_errors = any(
            d.severity == "error" for d in out_diags
        )
        return SessionVerifyResult(
            ok=not verify_errors,
            check_diagnostics=check_diags,
            verify_diagnostics=out_diags,
            summary=summary,
            obligations=out_obls,
        )
