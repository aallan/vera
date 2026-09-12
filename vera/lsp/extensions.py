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
        "proof_regressions": [<obligation>...],  # verified → anything else,
                                                 #   span-insensitively, and
                                                 #   with `line_before` /
                                                 #   `column_before` added
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
from vera.lsp.convert import uri_to_path
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


def _regression_item(
    before: ProofObligation, after: ProofObligation,
) -> dict[str, Any]:
    """A ``proof_regressions`` entry, which names BOTH spans.

    The obligation may have moved (see :func:`_relocation_key`), so
    ``line`` / ``column`` -- which :func:`_item` takes from the AFTER
    side -- are not enough to point an agent at what it broke.
    """
    item = _item(before, after)
    item["line_before"] = before.line
    item["column_before"] = before.column
    return item


def _relocation_key(ob: ProofObligation) -> tuple[str, str, str, str]:
    """Span-INSENSITIVE identity, for the regression predicate only.

    :meth:`~vera.obligations.core.ProofObligation.content_key` hashes the
    span, which is right for the presentation categories -- two textually
    identical obligations at two sites are two obligations -- and wrong
    for "did this edit take a proof away?": inserting ONE line above a
    proved obligation gives it a new key, so it presents as a removal
    plus a rediscovery and the span-keyed pass has no transition to
    judge.  An edit that shifts a line and costs a proof further down
    the file therefore walked the gate (#1443 review).

    Whitespace inside ``expr_text`` is normalised because a reformatted
    expression is the same obligation.  The key is deliberately NOT
    unique -- two identical asserts in one function share it -- so the
    caller pairs within a group positionally, in source order.

    What the key does NOT deliver, by construction: renaming the
    function, changing the obligation's kind, rewriting the predicate
    text, or moving the code to another file all make it a different
    obligation to the gate -- a deletion and an addition, judged as
    those.  The division of labour is the point: the GATE reasons about
    identity, the presentation categories report positions.
    """
    return (
        ob.file or "", ob.fn_name, ob.kind,
        " ".join(ob.expr_text.split()),
    )


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
    # #1443 — the PROOF-PRESERVATION question, asked over the whole
    # status vocabulary instead of inferred from the categories beside
    # it.  Those categories sort by the AFTER status, which makes them a
    # presentation of the delta and not a statement about what was lost:
    # `verified -> timeout` lands in `timed_out` and `verified ->
    # violated` in `newly_undischarged`, so a consumer asking "did this
    # edit take a proof away?" by reading one list gets a different
    # answer depending on which way the proof was lost.  The apply gate
    # asked exactly that, of exactly one list, and let a `verified ->
    # timeout` edit through.
    #
    # Enumerated as "was verified, is not verified" rather than as a
    # list of losing statuses, so a status added to `ObligationStatus`
    # later joins the refusal by default rather than by being
    # remembered here.
    proof_regressions: list[dict[str, Any]] = []
    unchanged = 0

    # #1443 review -- pair the LEFTOVERS before categorising anything.
    # `content_key` hashes the span, so an obligation that merely MOVED
    # arrives under a new key: it looks like a removal plus a brand-new
    # obligation, and neither gate input could see what actually
    # happened to it.  An old key with no new twin and a new key with no
    # old twin that agree on `_relocation_key` are one obligation that
    # relocated.  Within a group they pair positionally in source order,
    # so two identical asserts in one function still pair
    # deterministically.
    #
    # An old leftover with no counterpart is a DELETION, deliberately
    # not a regression: the gate protects proofs, not contracts, a
    # removed contract is visible in the edit itself, and nothing
    # unproved is left behind.  It is reported under `removed` with the
    # status it had.
    relocated: dict[str, ProofObligation] = {}
    new_leftovers: dict[tuple[str, str, str, str], list[ProofObligation]] = {}
    for nkey, ob in new.items():
        if nkey not in old:
            new_leftovers.setdefault(_relocation_key(ob), []).append(ob)
    taken: dict[tuple[str, str, str, str], int] = {}
    for okey, before_ob in old.items():
        if okey in new:
            continue
        rkey = _relocation_key(before_ob)
        i = taken.get(rkey, 0)
        candidates = new_leftovers.get(rkey, [])
        if i >= len(candidates):
            continue  # deletion: nothing on the new side to pair with
        taken[rkey] = i + 1
        relocated[candidates[i].content_key()] = before_ob

    for key, ob in new.items():
        before = old.get(key)
        moved_from = relocated.get(key)
        was = before if before is not None else moved_from
        if (
            was is not None
            and was.status == "verified"
            and ob.status != "verified"
        ):
            proof_regressions.append(_regression_item(was, ob))
        if before is not None and before.status == ob.status:
            unchanged += 1
        elif ob.status == "verified":
            newly_discharged.append(_item(before, ob))
        elif ob.status == "timeout":
            timed_out.append(_item(before, ob))
        elif moved_from is None or moved_from.status != ob.status:
            # violated / tier3 / tier3_unguarded.  This list is the
            # gate's other input, so relocation is INVISIBLE to it: a
            # pair is judged exactly as the same pair at a fixed span
            # would be.  Unchanged across the pair, the obligation is
            # not an addition and drops out -- which is what stopped a
            # harmless shift being refused in any program carrying a
            # Tier-3 obligation (#1461 review, case A2b).  Worsened
            # across it (`tier3 -> violated`, `timeout -> tier3`), it
            # stays, because dropping it would let an edit that moved a
            # line do what the identical unmoved edit is refused for.
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
        "proof_regressions": proof_regressions,
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
        # The pipeline is driven with the PATH, as `analyze` is (#1246):
        # a document URI is not a path, and handing one to the resolver
        # roots it at a directory named `file:` — or, for a path-less
        # document, at the process CWD.  Speculating on an edit has to
        # see the same module namespace the document's own analysis did,
        # or the delta compares two different programs.
        result = session.verify_source(text, file=uri_to_path(uri))
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
