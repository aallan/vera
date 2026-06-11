"""``vera/proposeEdit`` — the enforced edit workflow (#222 Phase F1).

The skill layer's foundation, applying the 2026-04-20 design notes'
observation that *"agents ignore raw tool primitives and call them out
of sequence"*: instead of exposing verify and apply as separate steps
an agent could skip or reorder, this method runs the whole
edit → verify → apply sequence server-side.  An agent cannot apply an
unverified edit, because applying *is* the final step of verifying —
the mandatory-contracts philosophy applied to tooling.

Request params (plain JSON)::

    {"uri": "<document uri>", "text": "<full proposed source>",
     "force": false}

Response (plain JSON)::

    {
      "applied": true,           # the edit passed the gate (or force)
      "ok": true,                # proposed source parsed + checked
      "proof_delta": {...},      # Phase E shape; null if not compiled
      "diagnostics": <count of error diagnostics in the proposed state>,
    }

The gate: apply iff the proof delta has no ``newly_undischarged``
obligations AND the proposed state has no error diagnostics.
``force: true`` overrides both — "this edit knowingly weakens a proof"
(or doesn't compile yet) is sometimes the intent, but it must be said
out loud; the default is the enforced gate.

On apply, three things happen, in order: a ``workspace/applyEdit``
request (the LSP-native mechanism — the *client* owns the buffer, so
the server must round-trip the edit rather than silently diverge), the
canonical :class:`~vera.lsp.documents.DocumentStore` text updates, and
the document re-analyzes + republishes diagnostics.  The client's
echoed ``didChange`` then replays as a no-op from the warm session's
discharge cache — the pre-warming Phase E was designed around.  The
``applyEdit`` request is fire-and-forget: the response's ``applied``
reports the *gate* verdict, not the client's asynchronous answer, and
canonical state is not rolled back if the client declines — a
declining client's buffer re-converges on its next full-sync
``didChange``, and blocking the handler on the client round-trip
would serialise every proposal on editor latency.  On refuse,
canonical state is untouched: same isolation guarantee as
``vera/speculativeEdit``.
"""

from __future__ import annotations

from typing import TYPE_CHECKING, Any

from lsprotocol import types as lsp

from vera.lsp.documents import Document
from vera.lsp.extensions import speculative_edit
from vera.obligations.core import ProofObligation
from vera.obligations.session import VerificationSession

if TYPE_CHECKING:
    from vera.lsp.server import VeraLanguageServer


def propose_edit(
    session: VerificationSession,
    baseline: list[ProofObligation],
    uri: str,
    text: str,
    force: bool = False,
) -> tuple[bool, dict[str, Any]]:
    """Pure decision: speculative verify *text*, then the apply gate.

    Returns ``(should_apply, response)``.  The caller owns the side
    effects of applying; this function only verifies and decides, so
    the gate logic is testable without a server.
    """
    speculative = speculative_edit(session, baseline, uri, text)
    delta = speculative["proof_delta"]
    clean = (
        delta is not None
        and not delta["newly_undischarged"]
        and speculative["diagnostics"] == 0
    )
    should_apply = force or clean
    return should_apply, {
        "applied": should_apply,
        "ok": speculative["ok"],
        "proof_delta": delta,
        "diagnostics": speculative["diagnostics"],
    }


def full_document_range(doc: Document | None) -> lsp.Range:
    """The whole-document replacement range for a full-text edit.

    With an open document the end position is computed exactly (last
    line, UTF-16 end column, via the document's cached line index).
    Without one — ``proposeEdit`` on a URI the client never opened —
    fall back to the maximum LSP line number; the spec requires clients
    to clamp out-of-range positions to the document end, which makes
    the sentinel a correct whole-file range over unknown content.
    """
    if doc is None:
        return lsp.Range(
            start=lsp.Position(line=0, character=0),
            end=lsp.Position(line=2**31 - 1, character=0),
        )
    end_line0 = doc.text.count("\n")
    last_segment = doc.text.rsplit("\n", 1)[-1]
    return lsp.Range(
        start=lsp.Position(line=0, character=0),
        end=lsp.Position(
            line=end_line0,
            character=doc.index.cp_to_utf16(end_line0, len(last_segment)),
        ),
    )


def apply_propose_edit(
    server: VeraLanguageServer,
    uri: str,
    text: str,
    force: bool = False,
) -> dict[str, Any]:
    """Run the full proposeEdit workflow against *server* state.

    The decision runs under ``analysis_lock`` (one Z3 session, strictly
    serialised).  The apply path then releases the lock before
    ``analyze_and_publish`` re-acquires it — the re-analysis replays
    the just-verified state from the discharge cache, so the second
    pass is cheap by construction.
    """
    with server.analysis_lock:
        baseline_analysis = server.analyses.get(uri)
        baseline = (
            baseline_analysis.obligations
            if baseline_analysis is not None
            else []
        )
        should_apply, response = propose_edit(
            server.session, baseline, uri, text, force,
        )
    if not should_apply:
        return response

    doc = server.store.get(uri)
    server.workspace_apply_edit(
        lsp.ApplyWorkspaceEditParams(
            edit=lsp.WorkspaceEdit(
                changes={
                    uri: [
                        lsp.TextEdit(
                            range=full_document_range(doc),
                            new_text=text,
                        ),
                    ],
                },
            ),
        ),
    )
    server.store.change(
        uri, text, version=(doc.version + 1) if doc is not None else 0,
    )
    server.analyze_and_publish(uri, text)
    return response
