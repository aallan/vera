"""Reified proof obligations and the warm verification session (#222).

Phase A of the LSP / obligation-core plan: obligations become
first-class :class:`ProofObligation` records (see ``core``), and
:class:`VerificationSession` (see ``session``) re-verifies full programs
on one long-lived Z3 solver.  Phase B adds incremental invalidation and
the discharge cache behind the same API.

Import shape: ``vera.verifier`` imports ``vera.obligations.core`` at
module level (running this ``__init__`` first), while ``session``
imports ``vera.verifier`` — a cycle if both were eager here.  The
session symbols are therefore exported lazily (PEP 562): by the time
anything accesses ``vera.obligations.VerificationSession``, the verifier
module is fully initialized.
"""

from __future__ import annotations

from typing import TYPE_CHECKING, Any

from vera.obligations.core import (
    ObligationKind,
    ObligationStatus,
    ProofObligation,
    expr_text_for,
)

if TYPE_CHECKING:
    from vera.obligations.session import (
        SessionRunStats,
        SessionVerifyResult,
        VerificationSession,
    )

__all__ = [
    "ObligationKind",
    "ObligationStatus",
    "ProofObligation",
    "SessionRunStats",
    "SessionVerifyResult",
    "VerificationSession",
    "expr_text_for",
]

_LAZY_SESSION_EXPORTS = frozenset(
    {"SessionRunStats", "SessionVerifyResult", "VerificationSession"},
)


def __getattr__(name: str) -> Any:
    if name in _LAZY_SESSION_EXPORTS:
        from vera.obligations import session

        return getattr(session, name)
    raise AttributeError(
        f"module {__name__!r} has no attribute {name!r}",
    )
