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
  summary totals, matching the existing ``summary.total -= 1``
  convention at those sites).
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
]

ObligationStatus = Literal[
    "verified",  # discharged statically (Tier 1) or trivially true
    "violated",  # Z3 produced a counterexample; an error was emitted
    "tier3",     # outside the decidable fragment; runtime check emitted
    "timeout",   # solver returned unknown; falls back to runtime check
    "tier3_unguarded",  # untranslatable/timeout at a narrowing site with no
                        # runtime guard, excluded from totals — surfaced as an
                        # E504 warning for an unguarded @Nat narrowing
                        # (nat_bind, #552/#747) or an E506 warning for any
                        # refinement narrowing (refine_bind, #746, which has no
                        # runtime guard yet)
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

    def content_key(self) -> str:
        """Stable identity digest for this obligation.

        Hashes the identity fields only (never the outcome), so two runs
        over the same source produce identical keys for the same
        obligation regardless of discharge result.  Spans are included
        because textually identical obligations can occur at multiple
        sites (e.g. the same ``@Nat.0 - @Nat.1`` subtraction in two
        branches) and must remain distinct cache entries.
        """
        ident = (
            f"{self.fn_name}\x1f{self.kind}\x1f{self.expr_text}"
            f"\x1f{self.line}\x1f{self.column}"
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
