"""``vera/speculativeEdit`` — the proof-delta extension (#222 Phase E).

The one custom (non-LSP-3.17) method, and the reason the obligation
core was built first: apply an edit *in memory*, re-verify on the warm
incremental session, and report which proof obligations changed state —
without touching the canonical document, its published diagnostics, or
the editor's view of the world.

This is the signal no generic language server can produce: an agent
proposing an edit learns, before committing it, whether the change
*keeps* the program's proofs (everything still discharges), *breaks*
them (obligations become violated or fall to runtime checks), or
*strengthens* them (previously-runtime obligations now prove) — the
"latency-to-confidence" loop from the #222 design notes.

Request params (plain JSON):
    {"uri": "<document uri>", "text": "<full proposed source>"}

Response (plain JSON)::

    {
      "ok": true,                # speculative source parsed + checked
      "proof_delta": {
        "newly_discharged":  [<obligation>...],  # → verified
        "newly_undischarged":[<obligation>...],  # verified → violated/tier3
        "timed_out":         [<obligation>...],  # solver unknown
        "removed":           [<obligation>...],  # obligation no longer exists
        "unchanged": <count>,
      },
      "diagnostics": <count of error diagnostics in the speculative state>,
    }

Each ``<obligation>`` carries ``fn`` / ``kind`` / ``expr`` / ``line`` /
``column`` / ``status_before`` / ``status_after`` (``status_before`` is
null for obligations the edit introduces).  Obligation identity is the
Phase A ``content_key`` — span-sensitive by design, so a moved-but-
identical obligation reports as removed+discharged rather than silently
matching across positions (consistent with the discharge cache).

Isolation: the speculative run goes through the SAME warm session (and
therefore the same discharge cache — deliberately: a speculative state
that later becomes real replays from cache), but the per-URI analysis
table and published diagnostics are never updated, so the editor's
canonical state is untouched.
"""

from __future__ import annotations

from typing import Any

from vera.errors import ParseError, TransformError
from vera.obligations.core import ProofObligation
from vera.obligations.session import VerificationSession


def _item(
    before: ProofObligation | None, after: ProofObligation | None,
) -> dict[str, Any]:
    ob = after if after is not None else before
    if ob is None:  # pragma: no cover — callers always pass one side
        raise ValueError("obligation delta item needs before or after")
    return {
        "fn": ob.fn_name,
        "kind": ob.kind,
        "expr": ob.expr_text,
        "line": ob.line,
        "column": ob.column,
        "status_before": before.status if before is not None else None,
        "status_after": after.status if after is not None else None,
    }


def proof_delta(
    baseline: list[ProofObligation],
    speculative: list[ProofObligation],
) -> dict[str, Any]:
    """Set-difference two obligation streams by Phase A identity."""
    old = {o.content_key(): o for o in baseline}
    new = {o.content_key(): o for o in speculative}

    newly_discharged: list[dict[str, Any]] = []
    newly_undischarged: list[dict[str, Any]] = []
    timed_out: list[dict[str, Any]] = []
    removed: list[dict[str, Any]] = []
    unchanged = 0

    for key, ob in new.items():
        before = old.get(key)
        if before is not None and before.status == ob.status:
            unchanged += 1
        elif ob.status == "verified":
            newly_discharged.append(_item(before, ob))
        elif ob.status == "timeout":
            timed_out.append(_item(before, ob))
        else:  # violated / tier3
            newly_undischarged.append(_item(before, ob))
    for key, ob in old.items():
        if key not in new:
            removed.append(_item(ob, None))

    return {
        "newly_discharged": newly_discharged,
        "newly_undischarged": newly_undischarged,
        "timed_out": timed_out,
        "removed": removed,
        "unchanged": unchanged,
    }


def speculative_edit(
    session: VerificationSession,
    baseline: list[ProofObligation],
    uri: str,
    text: str,
) -> dict[str, Any]:
    """Verify *text* speculatively and diff against *baseline*.

    Parse/transform/type errors mean the speculative state has no
    obligation stream to diff — the response says so (``ok: false``)
    and reports the error count, which is itself the answer an agent
    needs ("this edit doesn't even compile").
    """
    try:
        result = session.verify_source(text, file=uri)
    except (ParseError, TransformError):
        return {
            "ok": False,
            "proof_delta": None,
            "diagnostics": 1,
        }
    if not result.ok and not result.obligations:
        # Type errors short-circuited verification.
        return {
            "ok": False,
            "proof_delta": None,
            "diagnostics": sum(
                1 for d in result.diagnostics if d.severity == "error"
            ),
        }
    return {
        "ok": result.ok,
        "proof_delta": proof_delta(baseline, result.obligations),
        "diagnostics": sum(
            1 for d in result.diagnostics if d.severity == "error"
        ),
    }
