"""Proof obligation reification — first-class verification units (#222 Phase A).

The verifier historically discharged contract obligations *inline*: each
``requires`` / ``ensures`` / ``decreases`` clause, ``@Nat`` subtraction
site, and call-site precondition was translated and checked at the point
it was encountered, leaving behind only summary counters and diagnostics.
That shape makes incremental re-verification (#222 Phase B) and proof
deltas (`vera/speculativeEdit`, Phase E) impossible to express cleanly —
there is nothing to diff or cache.

This module reifies each obligation as a :class:`ProofObligation` record:
a stable identity (owning function, kind, source span, expression text,
content hash) plus the discharge outcome (status, counterexample, error
code).  ``ContractVerifier`` constructs one record per obligation at the
existing discharge sites, preserving discharge order and solver-state
interleaving exactly — reification is observational, never behavioural.

Identity vs. outcome:

- *Identity* fields (``fn_name``, ``kind``, ``expr_text``, span) name the
  obligation across runs.  ``content_key()`` digests them into the hash
  Phase B's discharge cache will key on (extended there with assumption
  and ADT-context hashes).
- *Outcome* fields record what discharging produced this run.  The
  ``status`` vocabulary mirrors the verifier's summary bookkeeping:
  ``verified`` ↔ ``tier1_verified``; ``tier3`` and ``timeout`` ↔
  ``tier3_runtime``; ``violated`` ↔ an error diagnostic and
  ``tier3_unguarded`` ↔ a warning diagnostic (both excluded from the
  summary totals: ``summarize()`` counts only ``verified`` / ``tier3``
  / ``timeout``, #967).
"""

from __future__ import annotations

import hashlib

from dataclasses import dataclass
from typing import Literal

from vera import ast

ObligationKind = Literal[
    "requires",   # precondition clause (assumed for the body; counted
                  # tier-1 when translatable, per verifier bookkeeping)
    "ensures",    # postcondition clause (checked against the body)
    "decreases",  # termination measure (one record per clause; the
                  # per-recursive-call-site checks inside
                  # _verify_decreases aggregate into this record)
    "nat_sub",    # @Nat - @Nat underflow obligation at one site (#520)
    "nat_bind",   # @Int value narrowing into a @Nat slot at a binding
                  # site — let / call-arg / effect-op-arg / ctor-field /
                  # match-bind / destructure (#552, generalising #520)
    "refine_bind",  # a value narrowing into a user RefinedType slot at a
                    # binding site or return position — the predicate must
                    # hold (#746, generalising nat_bind from the baked-in
                    # `>= 0` to an arbitrary translated predicate)
    "call_pre",   # callee precondition at a call site (#C7d); recorded
                  # only on violation in Phase A — successful call-site
                  # checks discharge silently inside the SMT layer and
                  # are not yet enumerated (Phase B extends this)
    "div_zero",   # division/modulo by-zero obligation `b != 0` at one
                  # `/`/`%` site (#680).  Tier-1-decidable (concrete
                  # integer arithmetic), so it mirrors nat_sub: verified
                  # -> tier-1, violated -> loud E526, unknown -> tier3.
    "index_bounds",  # array index obligation `0 <= i < length` at one
                     # IndexExpr site (#680; String indexing is a type error,
                     # so this is Array-only).  Tier-1 where the length
                     # is statically known (literal / refinement /
                     # precondition / path condition); loud E527 when the
                     # index is provably out of bounds; else honest tier3
                     # (length is uninterpreted — beyond Tier 1, see #427 —
                     # and codegen's `out_of_bounds` trap is the guard).
    "int_overflow",  # @Int/@Nat `+`/`-`/`*` range obligation at one site
                     # (#798).  Two-check like index_bounds: result provably in
                     # i64 (@Int) / u64 (@Nat) range -> tier-1; provably out of
                     # range -> loud E528; else honest tier3 (the codegen
                     # overflow trap is the guard).  @Nat `-` is underflow
                     # (nat_sub), not high-overflow, so it is excluded here.
    "assert",     # a body `assert(P)` predicate (#800, spec §6.2.5).  Two-
                  # check like index_bounds: prove P -> tier-1, prove ¬P ->
                  # loud E507 (always traps at runtime), else tier3 (the
                  # §11.14.1 `unreachable` trap is the guard).
    "float_to_int_domain",  # float_to_int(x) domain obligation at one site
                  # (#807).  `i64.trunc_f64_s` traps on NaN / +/-Inf /
                  # out-of-i64-range.  Concrete-gated: a concrete finite
                  # in-range arg -> tier-1; a concrete NaN/Inf/out-of-range arg
                  # -> loud E529; a symbolic arg -> honest tier3 (Z3's FP<->Real
                  # reasoning is unreliable; the codegen trunc trap is the
                  # guard).
    "nat_to_int_coerce",  # @Nat value widening into an @Int slot at one
                  # coercion site (#813) — the dual of `nat_bind`.  @Nat is u64
                  # and @Int is i64, so a @Nat in (i64.MAX, u64.MAX] reinterprets
                  # its bits when widened (u64.MAX -> -1).  Two-check like
                  # `int_overflow`: provably `<= i64.MAX` -> tier-1; provably
                  # `> i64.MAX` -> loud E530; else honest tier3 (the codegen
                  # coercion trap is the guard, so the postcondition stays
                  # sound).
    "decreases_bound",  # a @Nat `decreases` measure component fitting the
                  # i64 the runtime termination guard compares in (#1222).  The
                  # proof reasons over unbounded integers and the guard uses
                  # `i64.lt_s` / `i64.ge_s`, so the two agree only while the
                  # measure IS an i64 — above i64.MAX a @Nat reads negative and
                  # a Tier-1-proved termination aborts as "failed to decrease".
                  # Two-check like `nat_to_int_coerce`: provably `<= i64.MAX` ->
                  # tier-1; provably `> i64.MAX` -> loud E536; else tier3, with
                  # `_dec_measure_bound_check` as the guard so the failure names
                  # the range rather than borrowing the termination rule's
                  # message.  Recorded only for a @Nat component: an @Int one IS
                  # the i64, an ADT one is ranked by a heap-bounded size.
    "state_decl",  # a generic handler's declared state type diverging from
                  # the instantiated State<T> cell (#1206's E336 defers on a
                  # TypeVar cell; the monomorphized clone re-checks it and a
                  # divergence records violated/E533 — PR #1202 adversarial
                  # round, F3).  Always violated-or-absent: equality holds ->
                  # no record.
]

ObligationStatus = Literal[
    "verified",  # discharged statically (Tier 1) or trivially true
    "violated",  # Z3 produced a counterexample; an error was emitted
    "tier3",     # outside the decidable fragment; runtime check emitted
    "timeout",   # solver returned unknown; falls back to runtime check
    "tier3_unguarded",  # untranslatable/timeout/unbounded at a coercion site
                        # with no runtime guard, excluded from totals — surfaced
                        # as an E504 warning for an unguarded @Nat narrowing
                        # (nat_bind, #552/#747), an E506 warning for an
                        # *internal* refinement narrowing (refine_bind, #746:
                        # let / field / match / destructure — boundary sites
                        # ARE runtime-guarded and recorded `tier3` instead), or
                        # an E531 warning for an unguarded @Nat->@Int widening
                        # (nat_to_int_coerce, #813: the tuple / array /
                        # generic-ADT component coercions codegen cannot guard)
]


@dataclass
class ProofObligation:
    """One reified verification obligation and its discharge outcome."""

    fn_name: str
    kind: ObligationKind
    expr_text: str
    status: ObligationStatus
    line: int = 0
    column: int = 0
    error_code: str = ""
    counterexample: dict[str, str] | None = None
    #: The file ``line``/``column`` number lines in — the module that DECLARED
    #: what this obligation is about, which is not the entry program once an
    #: imported generic's clone is verified (#1220, PR #1239 review).  Without
    #: it a consumer joining an obligation to its diagnostic on
    #: ``(file, line, column)`` — the join ``verify --json`` documents — had
    #: to assume every obligation belonged to the entry file, and read a line
    #: number past its end.  ``None`` only for an obligation built outside a
    #: verifier run (a hand-constructed record in a unit test); every
    #: obligation ``_record_obligation`` reifies carries one whenever the
    #: verifier was given a file at all.
    file: str | None = None

    def content_key(self) -> str:
        """Stable identity digest for this obligation.

        Hashes the identity fields only (never the outcome), so two runs
        over the same source produce identical keys for the same
        obligation regardless of discharge result.  Spans are included
        because textually identical obligations can occur at multiple
        sites (e.g. the same ``@Nat.0 - @Nat.1`` subtraction in two
        branches) and must remain distinct cache entries — and the FILE with
        them, since a span is only unique within one, so two identical
        obligations in an importer and an imported module would otherwise
        share a cache entry.  Adding it can only SPLIT entries, never merge
        them, which is the safe direction for a cache.

        The cache is not the only consumer, and the second one does not
        tolerate a split the way a cache does:
        :func:`vera.lsp.extensions.proof_delta` diffs two obligation streams
        BY this key, so a stream keyed under a different ``file`` reports
        every obligation as removed and every one recreated rather than as
        unchanged.  The precondition is therefore stronger there — both
        streams must derive ``file`` identically — and it is met by both
        sides going through :func:`vera.lsp.convert.uri_to_path`:
        ``features.analyze`` for the baseline, ``extensions.speculative_edit``
        for the speculative stream (#1246).  A future caller that hands the
        session a raw URI, or an un-normalised path, breaks the delta without
        breaking anything the cache would notice (PR #1283 review).
        """
        ident = (
            f"{self.fn_name}\x1f{self.kind}\x1f{self.expr_text}"
            f"\x1f{self.line}\x1f{self.column}\x1f{self.file or ''}"
        )
        return hashlib.sha256(ident.encode("utf-8")).hexdigest()


def expr_text_for(node: ast.Expr | ast.Contract) -> str:
    """Render the obligation's expression for identity / display.

    Contracts wrap their predicate expression(s); bare expressions
    (subtraction sites) format directly.  ``format_expr`` is total —
    it ends in a ``"<expr>"`` fallback — so no defensive guard is
    needed; the class-name fallback below covers only non-Expr
    contract shapes (``Invariant``, which never reaches the verifier's
    function-contract path today).
    """
    if isinstance(node, ast.Requires | ast.Ensures):
        return ast.format_expr(node.expr)
    if isinstance(node, ast.Decreases):
        return ", ".join(ast.format_expr(e) for e in node.exprs)
    if isinstance(node, ast.Expr):
        return ast.format_expr(node)
    return type(node).__name__  # pragma: no cover — Invariant-only path
