"""Skill-layer workflows: enforced edit sequences (#222 Phase F).

The skill layer applies the 2026-04-20 design notes' observation that
*"agents ignore raw tool primitives and call them out of sequence"*:
instead of exposing verify and apply as separate steps an agent could
skip or reorder, each method here runs a whole edit → verify → apply
sequence server-side.  An agent cannot apply an unverified edit,
because applying *is* the final step of verifying — the
mandatory-contracts philosophy applied to tooling.

``vera/proposeEdit`` (Phase F1) — request params (plain JSON)::

    {"uri": "<document uri>", "text": "<full proposed source>",
     "force": false, "version": <optional: the version it was made from>}

Response (plain JSON)::

    {
      "applied": true,           # the gate passed (or force) AND the
                                 #   client applied the edit
      "ok": true,                # proposed source parsed + checked
      "proof_delta": {...},      # Phase E shape; null if not compiled
      "diagnostics": <count of error diagnostics in the proposed state>,
      "client": "applied",       # the client's side: see below
    }

The gate: apply iff the proof delta has no ``proof_regressions`` (no
obligation that was ``verified`` is anything else now — whatever it
lost its proof to, and wherever in the file it now sits), no
``newly_undischarged`` obligations (the only conjunct that can see an
obligation the edit INTRODUCES, which has no ``before`` to regress
from, so neither list subsumes the other), AND the proposed state has
no error diagnostics.  ``force: true`` overrides
all three — "this edit knowingly weakens a proof" (or doesn't compile
yet) is sometimes the intent, but it must be said out loud; the default
is the enforced gate.

The client owns the buffer, so an edit that passes the gate goes to it
as a ``workspace/applyEdit`` request, and nothing on the server's side
changes until the client says its buffer did (#1444).  The canonical
:class:`~vera.lsp.documents.DocumentStore` describes the client's open
buffer, so it is written by the client's own ``didOpen`` /
``didChange`` / ``didClose`` and by nothing else — this module included;
the analysis table and the published diagnostics follow the store.  So
the request is:

* **Version-guarded.**  One whole-document ``TextDocumentEdit`` naming
  the document version whose text the gate verified against.  A client
  must refuse an edit whose version its buffer has moved past, so a
  ``didChange`` that lands while the edit is pending — the user typed,
  or another proposal was applied first — is never overwritten by a
  replacement computed from the text before it.  ``documentChanges`` is
  the only ``WorkspaceEdit`` form that can carry a version, so a client
  that does not advertise it (with ``workspace.applyEdit``) is sent
  nothing, rather than an edit that lands on whatever the buffer holds.
  The guard protects the newer text only if the edit was made from, and
  judged against, the text AT that version, so every workflow first
  checks that the analysis it reads is the open document's (an analysis
  that raises leaves the table behind the store) and, for a candidate
  built from the document, that its source text still is — and refuses
  with ``InvalidParams`` otherwise (:func:`require_current`).  The
  optional ``version`` param, on all three methods, lets the client say
  which version it made the request from; any other open version is
  refused the same way.  Without it, a proposal written against an
  older text replaces newer text the server has seen -- the risk a
  client that cannot send it accepts.
* **Awaited.**  The workflows are coroutines: the server waits for the
  client's answer, and ``analysis_lock`` is not held while it does, so
  the notifications that arrive meanwhile are analysed as they come.
  Z3 work stays serialised; waiting on an editor does not.
* **Reconciled by the client.**  An applied edit reaches the server as
  the client's own ``didChange``: at the client's actual version, and
  analysed and published like any other change — replayed from the warm
  session's discharge cache, which the gate's speculative run just
  filled (the pre-warming Phase E was designed around).  That
  notification may arrive before the answer or after it; either way
  the server publishes nothing for the new text until it does.

``applied`` is true only when the client applied the edit, and
``client`` says what became of it on the client's side: ``null`` (the
gate refused; nothing was sent), ``"applied"``, ``"declined"`` (the
client answered ``applied: false`` — typically because its buffer is no
longer at the verified version), ``"failed"`` (an error answer, or the
request could not be sent), ``"cancelled"`` (the request was cancelled
unanswered), or ``"unsupported"`` (the client cannot take a
version-guarded edit, so none was sent).  If the proposal request
itself is cancelled while the edit is pending, it ends as cancelled —
an error response, never ``applied`` — and the edit request is left for
the client to answer.  Whatever the answer, the workflow itself writes
no canonical state — the same isolation guarantee as
``vera/speculativeEdit`` — so an applied edit arrives only as the
client's ``didChange``, and any other outcome leaves the text, version
and published analysis exactly as they were.

``vera/addEffect`` (Phase F3) — request params::

    {"uri": "<document uri>", "fn": "<top-level function name>",
     "effect": "<effect ref, e.g. IO or State<Int>>"}

The genuinely multi-site workflow: adding an effect to a function's
row invalidates the row of every **transitive caller** (each call
site would otherwise fail effect checking), so the inverse call graph
— built from the Phase B ``direct_callee_names`` walker — determines
the propagation set, every affected ``effects(...)`` clause is
rewritten by span (``pure`` → ``<E>``, ``<A>`` → ``<A, E>``,
functions already naming the effect are skipped), and ONE multi-site
candidate runs through the proposeEdit pipeline.  The response adds
``rewritten``: the affected functions in declaration order; if it is
empty the row state was already satisfied and nothing ran
(``applied: false, ok: true, proof_delta: null, client: null`` — the
no-op shape).
Propagation is bounded at handlers (#725): a call site inside a
``handle[E]`` body contributes no edge, so a caller that discharges
the effect around every one of its call sites is left unrewritten.  A
caller that also reaches the callee on an unhandled path is still
rewritten — the effect genuinely escapes along that path.  A call in a
handler *clause* is not discharged by that handler (clause bodies run
outside it), so it propagates; nor is a call in the handler's *state
initialiser*, which is evaluated in the enclosing scope before the
handler is installed.  A handler bounds the propagation only when
its ``handle[...]`` head is SPELLED the way the request is: type
arguments included, and compared as written rather than as resolved.
So ``handle[State<Nat>]`` does not bound a ``State<Int>``
propagation — which it must not, the checker discharging against
effect-instance equality — and an alias spelling of the *same*
instance (``handle[State<MyAlias>]``, ``type MyAlias = Int``) does not
bound it either, though the checker discharges that one.  Every
non-match keeps the edge, so the comparison under-prunes rather than
over-prunes: a surviving edge writes a row the program may not need,
which still type-checks (#1292).
Propagation remains single-file (module-qualified calls do not
propagate across the file boundary).  Row identity, separately, is the
base name before any type arguments, so ``State<Int>`` will not be
added next to an existing ``State<Bool>``.

``vera/strengthenContract`` (Phase F2) — request params::

    {"uri": "<document uri>", "fn": "<top-level function name>",
     "kind": "requires" | "ensures", "expr": "<new contract expr>"}

Locates the first *kind* clause of the named top-level function in the
canonical document, splices *expr* over that clause's expression by
span, and runs the candidate through the proposeEdit pipeline — same
response shape, no ``force`` (an agent that wants to push through a
breaking contract change can construct the full text and call
``vera/proposeEdit`` with ``force`` explicitly; the dedicated workflow
exists to make the *audited* path the easy one).  The call-site audit
IS the proof delta: a tightened precondition some caller no longer
satisfies surfaces as ``newly_undischarged`` ``call_pre`` items at the
call sites (Phase A keys obligations by call-site span precisely for
this), and the gate refuses.  Functions nested in ``where`` blocks are
not addressable — top-level names only, matching the single-file
project model.
"""

from __future__ import annotations

import asyncio

from typing import TYPE_CHECKING, Any

from lsprotocol import types as lsp

from vera import ast
from vera.lsp.documents import Document
from vera.lsp.extensions import speculative_edit
from vera.obligations.cache import direct_callee_names, walk_nodes
from vera.obligations.core import ProofObligation
from vera.obligations.session import VerificationSession

if TYPE_CHECKING:
    from vera.lsp.features import Analysis
    from vera.lsp.server import VeraLanguageServer


class StaleDocumentError(ValueError):
    """The server's analysis does not describe the open document, so no
    edit may be verified against it or built from it (#1444).

    A ``ValueError``, so the edit handlers refuse it as JSON-RPC
    ``InvalidParams`` alongside the other requests that cannot be served
    against the document as it stands (no analysis, does not parse).
    """


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
    the gate logic is testable without a server.  The response's
    ``applied`` is therefore the GATE's verdict here, and
    :func:`apply_propose_edit` settles it from the client's answer.
    """
    speculative = speculative_edit(session, baseline, uri, text)
    delta = speculative["proof_delta"]
    clean = (
        delta is not None
        # #1443 — the proof-preservation question, asked once, of the
        # whole status vocabulary.  `newly_undischarged` cannot stand in
        # for it: `proof_delta` sorts by the AFTER status, so an
        # obligation that went `verified -> timeout` is filed under
        # `timed_out` and an edit that destroyed a proof looked clean
        # here.  The verifier records a postcondition timeout as a
        # warning with `ok=True`, so the diagnostics count did not catch
        # it either, and `applied` came back True on an edit that lost a
        # proof.  The categories remain what they are for presentation;
        # their separation was never permission to apply.
        and not delta["proof_regressions"]
        # Kept beside it, and NOT subsumed by it: it is the only
        # conjunct that can see an obligation the edit INTRODUCES, which
        # has no `before` for the predicate above to regress from.  (It
        # is not only that: a same-span `verified -> violated` lands
        # here too.  What it uniquely covers is the introduced one.)
        #
        # Entries whose status did not move are skipped.  They exist
        # only because `proof_delta` keys its categories on the span:
        # an obligation that RELOCATED is listed here against the
        # `before` it was paired with, and one that is undischarged at
        # both ends of that pair introduced nothing and took nothing
        # away.  Refusing it made a harmless comment insertion into any
        # program carrying a Tier-3 obligation need `force` (#1461
        # review, case A2b).  A pair that WORSENED still has
        # `status_before != status_after` and is still refused, exactly
        # as the identical unmoved edit is.
        and not [
            item for item in delta["newly_undischarged"]
            if item["status_before"] != item["status_after"]
        ]
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


def supports_versioned_edits(
    capabilities: lsp.ClientCapabilities | None,
) -> bool:
    """Whether a client with *capabilities* can take a version-guarded
    whole-document edit.

    Two capabilities, both required: ``workspace.applyEdit`` (the client
    answers the request at all) and ``workspace.workspaceEdit.
    documentChanges`` — the only ``WorkspaceEdit`` form whose text edits
    name the document version they apply to.  The other form,
    ``changes``, is unversioned: an edit sent that way lands on whatever
    the buffer holds when it arrives, including typing that came after
    the text it was verified against.  *capabilities* is ``None`` before
    the client has initialised.
    """
    workspace = capabilities.workspace if capabilities is not None else None
    if workspace is None or workspace.apply_edit is not True:
        return False
    edit = workspace.workspace_edit
    return edit is not None and edit.document_changes is True


def versioned_edit(
    uri: str, doc: Document | None, text: str,
) -> lsp.ApplyWorkspaceEditParams:
    """The request replacing *uri*'s whole text with *text*, guarded by
    the version of the text it replaces.

    With the document open, that is *doc*'s version, and a client whose
    buffer has moved past it must refuse the edit (LSP 3.17,
    ``TextDocumentEdit``).  Unopened, the version is ``null``, the
    protocol's spelling for "the file on disk is the master", over the
    clamp-sentinel range :func:`full_document_range` gives.
    """
    return lsp.ApplyWorkspaceEditParams(
        edit=lsp.WorkspaceEdit(
            document_changes=[
                lsp.TextDocumentEdit(
                    text_document=lsp.OptionalVersionedTextDocumentIdentifier(
                        uri=uri,
                        version=doc.version if doc is not None else None,
                    ),
                    edits=[
                        lsp.TextEdit(
                            range=full_document_range(doc), new_text=text,
                        ),
                    ],
                ),
            ],
        ),
    )


def _retrieve(answer: asyncio.Future[Any]) -> None:
    """Mark a settled answer's outcome as retrieved.

    Matters only when the workflow was cancelled while it waited: the
    answer then settles with nobody awaiting it, and asyncio would log an
    error it "never retrieved" for an outcome that is no longer anyone's
    concern.
    """
    if not answer.cancelled():
        answer.exception()


async def client_outcome(
    server: VeraLanguageServer, request: lsp.ApplyWorkspaceEditParams,
) -> str:
    """Send *request* as ``workspace/applyEdit`` and wait for the answer.

    Returns ``"applied"``, ``"declined"``, ``"failed"`` or
    ``"cancelled"``.  The caller must hold no lock: the answer, and every
    notification the client sends before it, arrive through the same
    event loop this coroutine is suspended on.

    The wait is SHIELDED.  Cancelling this coroutine — the client
    cancelling the proposal request — must not cancel the edit request
    underneath it: pygls would then fail the client's late answer with
    ``InvalidStateError`` inside its reader, and the client may apply the
    edit anyway.  Own cancellation propagates; the edit request's
    cancellation (pygls cancels every outstanding request at shutdown) is
    an outcome, reported like any other.
    """
    try:
        pending = server.workspace_apply_edit(request)
    except Exception:  # noqa: BLE001 — any failure to SEND is "not applied", which is the one thing this reports
        return "failed"
    answer = asyncio.wrap_future(pending)
    answer.add_done_callback(_retrieve)
    try:
        result = await asyncio.shield(answer)
    except asyncio.CancelledError:
        task = asyncio.current_task()
        if task is not None and task.cancelling():
            raise
        return "cancelled"
    except Exception:  # noqa: BLE001 — an error answer, of whatever type, is an edit the client did not apply
        return "failed"
    return "applied" if getattr(result, "applied", None) is True else "declined"


def require_current(
    uri: str,
    doc: Document | None,
    analysis: Analysis | None,
    base_text: str | None,
    base_version: int | None,
) -> None:
    """Refuse unless the edit's inputs describe the open document.

    Every input an edit is made from, or judged against, must be the
    open buffer's text, because the edit is guarded by the open
    document's version and that guard protects the client's newer text
    only if the edit is about the text AT that version:

    * the ANALYSIS the gate judges the edit against -- *analysis* comes
      from :func:`~vera.lsp.features.current_analysis`, so it is
      ``None`` exactly when the open document has no analysis of its
      current text (its latest analysis raised).  A candidate spliced
      from an older analysis would pass the client's version check and
      overwrite the newer text; a proposal gated against one would be
      judged against a text the client no longer has.  ``force`` changes
      neither: it overrides the gate's verdict, not the question of
      which text the edit is about;
    * for a candidate built from the document, as
      ``vera/strengthenContract`` and ``vera/addEffect`` build theirs,
      the text it was built from (*base_text*);
    * when the CLIENT says which version it made the request from
      (*base_version*, the optional ``version`` param), that version: a
      proposal made from an older text would otherwise replace newer
      text the server has already seen.

    A document the client never opened has no buffer to be stale
    against, and no analysis either; it is refused only when the edit
    claims a text or a version of it, which then are not the client's.
    """
    if base_version is not None and (
        doc is None or doc.version != base_version
    ):
        where = (
            "is not open" if doc is None
            else f"is at version {doc.version}"
        )
        raise StaleDocumentError(
            f"the request was made from version {base_version} of "
            f"{uri!r}, but the open document {where}; read the current "
            "text, then make the request again",
        )
    if doc is None:
        if base_text is not None:
            raise StaleDocumentError(
                f"{uri!r} is not open, so an edit built from its text "
                "has no buffer to apply to; open the document, then retry",
            )
        return
    if analysis is None:
        raise StaleDocumentError(
            f"the server's analysis of {uri!r} does not describe the open "
            f"document (version {doc.version}): its latest text could not "
            "be analysed, so no edit can be verified against it; change "
            "the document so it is analysed again, then retry",
        )
    if base_text is not None and base_text != doc.text:
        raise StaleDocumentError(
            f"the edit was built from a text of {uri!r} that is no longer "
            f"the open document (version {doc.version}); build it again "
            "from the current text",
        )


async def apply_propose_edit(
    server: VeraLanguageServer,
    uri: str,
    text: str,
    force: bool = False,
    base_text: str | None = None,
    version: int | None = None,
) -> dict[str, Any]:
    """Run the full proposeEdit workflow against *server* state.

    The decision runs under ``analysis_lock`` (one Z3 session, strictly
    serialised), and the edit it passes goes to the client guarded by
    the version of the open document (:func:`versioned_edit`) -- once
    :func:`require_current` has established that the analysis the gate
    reads, *base_text* when a caller built *text* from the document, and
    *version* when the client said which version it proposed from, are
    all that version's.  The lock is released before the wait for
    the client's answer (:func:`client_outcome`), and nothing here
    writes the document store, the analysis table or the published
    diagnostics: the client owns the buffer, so an applied edit reaches
    the server as the client's own ``didChange``, at the client's own
    version (#1444).

    Raises :class:`StaleDocumentError` when the analysis, *base_text* or
    *version* is not the open document's.
    """
    with server.analysis_lock:
        # Read together, with no await between them for a notification
        # to land in: the version below is the one the check vouches for.
        doc = server.store.get(uri)
        baseline_analysis = server.current_analysis(uri)
        require_current(uri, doc, baseline_analysis, base_text, version)
        baseline = (
            baseline_analysis.obligations
            if baseline_analysis is not None
            else []
        )
        should_apply, response = propose_edit(
            server.session, baseline, uri, text, force,
        )
        request = versioned_edit(uri, doc, text) if should_apply else None
    response["client"] = None
    if request is None:
        return response
    if not supports_versioned_edits(
        getattr(server, "client_capabilities", None),
    ):
        response["applied"] = False
        response["client"] = "unsupported"
        return response
    outcome = await client_outcome(server, request)
    response["applied"] = outcome == "applied"
    response["client"] = outcome
    return response


def span_offsets(text: str, span: ast.Span) -> tuple[int, int]:
    """``ast.Span`` (1-based line, 1-based code-point column,
    exclusive end) → ``[start, end)`` offsets into *text*.

    Columns count code points, which are exactly Python string
    indices, so no UTF-16 transcoding is involved — that wrinkle only
    exists at the LSP wire boundary.  Spans come from a program parsed
    from this very text, so they are in range by construction.
    """
    line_starts = [0]
    for i, ch in enumerate(text):
        if ch == "\n":
            line_starts.append(i + 1)
    start = line_starts[span.line - 1] + (span.column - 1)
    end = line_starts[span.end_line - 1] + (span.end_column - 1)
    return start, end


_CONTRACT_KINDS: dict[str, type[ast.Requires] | type[ast.Ensures]] = {
    "requires": ast.Requires,
    "ensures": ast.Ensures,
}


def splice_contract(
    program: ast.Program,
    text: str,
    fn_name: str,
    kind: str,
    expr: str,
) -> str | None:
    """Candidate text with *expr* replacing the first *kind* clause
    expression of top-level function *fn_name*; ``None`` if no such
    function/clause exists.

    Vera contracts are mandatory, so every function has at least one
    clause of each kind; with multiple clauses (they conjoin), the
    first is the deterministic splice target and the rest are
    untouched.
    """
    contract_type = _CONTRACT_KINDS[kind]
    for top in program.declarations:
        decl = top.decl  # TopLevelDecl wraps the declaration proper
        if not isinstance(decl, ast.FnDecl) or decl.name != fn_name:
            continue
        for contract in decl.contracts:
            if (
                isinstance(contract, contract_type)
                and contract.expr.span is not None
            ):
                start, end = span_offsets(text, contract.expr.span)
                return text[:start] + expr + text[end:]
        return None
    return None


async def strengthen_contract(
    server: VeraLanguageServer,
    uri: str,
    fn_name: str,
    kind: str,
    expr: str,
    version: int | None = None,
) -> dict[str, Any]:
    """Run the full strengthenContract workflow against *server* state.

    Splices against the canonical analysis (read under the lock), then
    delegates to :func:`apply_propose_edit` with the spliced text as
    *base_text* — which re-verifies the *candidate* from scratch, sends
    it only if that text is still the open document's, and guards it
    with the document's version, so a ``didChange`` that lands after it
    makes the client refuse the edit rather than lose the newer text to
    a candidate built without it.

    Raises ``ValueError`` for requests that cannot name a splice
    target (no analysis for the URI, an analysis that does not describe
    the open document, a document that does not parse, an unknown
    function); the handler maps these to JSON-RPC InvalidParams.
    """
    with server.analysis_lock:
        analysis = server.current_analysis(uri)
        # Before anything is read off the analysis -- the splice target,
        # or the answer that there is none -- it has to be the open
        # document's, at the version the client asked about.
        require_current(uri, server.store.get(uri), analysis, None, version)
    if analysis is None:
        raise ValueError(
            f"no analysis for {uri!r} — open the document first",
        )
    if analysis.program is None:
        raise ValueError(
            f"document {uri!r} does not parse; "
            "contracts cannot be located",
        )
    candidate = splice_contract(
        analysis.program, analysis.text, fn_name, kind, expr,
    )
    if candidate is None:
        raise ValueError(
            f"no top-level function {fn_name!r} with a {kind} clause",
        )
    return await apply_propose_edit(
        server, uri, candidate, force=False, base_text=analysis.text,
        version=version,
    )


def _top_level_fns(program: ast.Program) -> dict[str, ast.FnDecl]:
    """Top-level functions by name, in declaration order (dicts
    preserve insertion order)."""
    fns: dict[str, ast.FnDecl] = {}
    for top in program.declarations:
        decl = top.decl
        if isinstance(decl, ast.FnDecl):
            fns[decl.name] = decl
    return fns


def _effect_base(ref_text: str) -> str:
    """Effect identity: the reference text before any type arguments
    (``State<Int>`` → ``State``; ``Mod.IO`` → ``Mod.IO``)."""
    return ref_text.split("<", 1)[0].strip()


def _effect_instance_key(ref_text: str) -> str:
    """Full-instance effect identity: the reference text with all
    whitespace removed and type arguments **kept**
    (``State< Int >`` → ``State<Int>``).

    Deliberately not :func:`_effect_base`.  The row rewrite wants the
    base name, because appending ``State<Int>`` beside an existing
    ``State<Bool>`` would give one function two ``State`` rows — a
    same-base match there suppresses a duplicate, a harmless no-op.
    Handler discharge is the opposite direction: it *asserts* the
    effect is gone.  The checker discharges against
    :class:`~vera.types.EffectInstance`, whose equality includes
    ``type_args``, so ``handle[State<Nat>]`` leaves ``State<Int>``
    escaping and a caller around it still needs the row (#725).
    """
    return "".join(ref_text.split())


def _handled_effect_key(ref: ast.EffectRefNode) -> str:
    """The ``handle[...]`` head as SPELLED, in the same form
    :func:`_effect_instance_key` produces from a request string.

    A spelling, not a resolved effect instance: type names are
    compared as written, so an alias of the requested argument
    (``handle[State<MyAlias>]`` against a ``State<Int>`` request)
    reads as a different key even though the checker discharges it.
    That under-prunes — the caller keeps an edge it does not need —
    and is tracked as #1292, which will key the comparison on the
    resolved instance instead.

    Anything this cannot spell exactly is spelled *unmatchably* — a
    string no request can equal — so the call site is left unpruned.
    That is the safe direction: an unpruned edge writes a row the
    program may not strictly need, which still type-checks, while a
    wrongly pruned one leaves the caller on ``pure`` and the whole
    candidate dies on E125.  An almost-right spelling is the trap, so
    the refinement case below is pushed onto the unmatchable path
    rather than allowed to collide with a base-type request.
    """
    if isinstance(ref, ast.QualifiedEffectRef):
        base, args = f"{ref.module}.{ref.name}", ref.type_args
    elif isinstance(ref, ast.EffectRef):
        base, args = ref.name, ref.type_args
    else:  # pragma: no cover — the parser produces only those two
        return ""
    if not args:
        return base
    if any(
        isinstance(n, ast.RefinementType)
        for a in args
        for n in walk_nodes(a)
    ):
        # ``format_type_expr`` drops a refinement's predicate, so
        # ``Exn<{ @Int | p }>`` renders as ``Exn<Int>`` — the checker
        # keeps those two instances distinct (the call site fails E125
        # without its own row), so a collapsed key would prune an edge
        # the program needs.  The walk covers a refinement nested
        # inside an argument (``Exn<Array<{ @Int | p }>>``), which
        # collapses exactly the same way.
        return f"{base}<?>"
    # ``format_type_expr`` spells parameter position (``@Int``); an
    # effect argument is written bare.  A shape it cannot render comes
    # back as "@?", which survives as "?" — never a valid request.
    rendered = ",".join(
        _effect_instance_key(ast.format_type_expr(a)).replace("@", "")
        for a in args
    )
    return f"{base}<{rendered}>"


def _unhandled_callee_names(
    decl: ast.FnDecl, effect: str | None,
) -> frozenset[str]:
    """Direct callees of *decl*, minus those a ``handle[effect]``
    block in *decl* already discharges (#725).

    With *effect* ``None`` this is exactly
    :func:`direct_callee_names` — the handler-unaware call graph.

    Containment is structural (the handled sub-tree) rather than
    span-arithmetic: identical answers where both apply, and no
    special case for nodes carrying no span.  Only the handler's
    ``body`` is pruned; its clauses and its state initialiser each
    escape it for their **own** reason, not a shared one:

    * A clause body runs *outside* its own handler — that is what a
      clause is — so an effect performed there still escapes to the
      enclosing function.
    * The state initialiser escapes earlier still: it is evaluated in
      the ENCLOSING scope, before the handler is installed at all.
      ``ControlFlowMixin._check_handle`` (``vera/checker/control.py``)
      synths ``state.init_expr`` before it extends
      ``env.current_effect_row`` with the handled effect, and codegen
      matches that order (``_translate_handle_state`` step 1 in
      ``vera/wasm/calls_handlers.py`` evaluates the init expression
      *before* pushing the new cell, because the init expr belongs to
      the enclosing scope).  So an effectful call there is checked
      against the caller's own row — E125 if the caller is ``pure``.

    Handler identity is the ``handle[...]`` head's source spelling,
    type arguments included (:func:`_handled_effect_key`); any
    non-match keeps the edge.
    """
    if effect is None:
        return direct_callee_names(decl)
    want = _effect_instance_key(effect)
    # Identity by object, not by value: two structurally equal calls
    # at different sites are distinct nodes, and every node stays
    # reachable from *decl* for the duration of the comprehension.
    handled = {
        id(n)
        for h in walk_nodes(decl)
        if isinstance(h, ast.HandleExpr)
        and _handled_effect_key(h.effect) == want
        for n in walk_nodes(h.body)
    }
    return frozenset(
        n.name
        for n in walk_nodes(decl)
        if isinstance(n, ast.FnCall) and id(n) not in handled
    )


def transitive_callers(
    program: ast.Program, fn_name: str, effect: str | None = None,
) -> list[str] | None:
    """*fn_name* plus every top-level function that transitively calls
    it, in declaration order; ``None`` if no such top-level function.

    The inverse closure over the Phase B call walker: plain ``FnCall``
    names only, so module-qualified calls never propagate across the
    file boundary, and calls inside ``where`` blocks attribute to
    their containing top-level function.

    *effect* bounds the closure at handlers (#725): a call site inside
    a ``handle[effect]`` body contributes no edge, because the handler
    discharges the effect and the caller needs no row of its own.  A
    caller that reaches the callee on *any* unhandled path keeps its
    edge — the deliberately conservative reading, since the effect
    genuinely escapes along that path.

    Handler identity is the ``handle[...]`` head's source SPELLING,
    type arguments included, compared to the request string — not the
    resolved effect instance (#1292).  Two consequences, in opposite
    directions:

    * ``handle[State<Nat>]`` does **not** bound a ``State<Int>``
      propagation.  Required: the checker discharges against
      ``EffectInstance`` equality, so the call site would fail E125
      without the row.
    * ``handle[State<MyAlias>]`` with ``type MyAlias = Int`` does not
      bound one either, though the checker *does* discharge that one.
      The comparison under-prunes here, leaving the caller a row it
      does not need — which still type-checks, so it is the safe
      direction, and it is the documented behaviour until #1292 swaps
      the comparison onto resolved instances.

    Only a matching spelling prunes; every other outcome keeps the
    edge.
    """
    fns = _top_level_fns(program)
    if fn_name not in fns:
        return None
    callees = {
        name: _unhandled_callee_names(decl, effect) & fns.keys()
        for name, decl in fns.items()
    }
    affected = {fn_name}
    changed = True
    while changed:
        changed = False
        for name, called in callees.items():
            if name not in affected and called & affected:
                affected.add(name)
                changed = True
    return [name for name in fns if name in affected]


def _row_names(row: ast.EffectSet) -> set[str]:
    names: set[str] = set()
    for ref in row.effects:
        if isinstance(ref, ast.EffectRef):
            names.add(ref.name)
        elif isinstance(ref, ast.QualifiedEffectRef):
            names.add(f"{ref.module}.{ref.name}")
    return names


def effect_row_rewrite(
    text: str, decl: ast.FnDecl, effect: str,
) -> tuple[int, int, str] | None:
    """``(start, end, replacement)`` adding *effect* to *decl*'s row,
    or ``None`` if the row already names it (idempotence).

    Span facts this relies on (verified against the parser):
    ``PureEffect.span`` covers exactly ``pure``; ``EffectSet.span``
    covers the whole ``<...>`` including brackets, so the append
    splice reuses the original source verbatim up to the closing
    bracket.
    """
    row = decl.effect
    if row.span is None:
        return None
    if isinstance(row, ast.PureEffect):
        start, end = span_offsets(text, row.span)
        return start, end, f"<{effect}>"
    if isinstance(row, ast.EffectSet):
        if _effect_base(effect) in {
            _effect_base(n) for n in _row_names(row)
        }:
            return None
        start, end = span_offsets(text, row.span)
        return start, end, text[start : end - 1] + f", {effect}>"
    return None


async def add_effect(
    server: VeraLanguageServer,
    uri: str,
    fn_name: str,
    effect: str,
    version: int | None = None,
) -> dict[str, Any]:
    """Run the full addEffect workflow against *server* state.

    Same locking and version-guarding model as
    :func:`strengthen_contract`: the candidate is rewritten from the
    canonical text, which goes to :func:`apply_propose_edit` as
    *base_text*, and the edit names that text's version.  Raises
    ``ValueError`` when the request cannot name a target (no analysis,
    an analysis that does not describe the open document, unparseable
    document, unknown top-level function).
    """
    with server.analysis_lock:
        analysis = server.current_analysis(uri)
        # Before anything is read off the analysis -- the rows to
        # rewrite, or the answer that there are none -- it has to be the
        # open document's, at the version the client asked about.
        require_current(uri, server.store.get(uri), analysis, None, version)
    if analysis is None:
        raise ValueError(
            f"no analysis for {uri!r} — open the document first",
        )
    if analysis.program is None:
        raise ValueError(
            f"document {uri!r} does not parse; "
            "effect rows cannot be located",
        )
    affected = transitive_callers(analysis.program, fn_name, effect)
    if affected is None:
        raise ValueError(f"no top-level function {fn_name!r}")

    fns = _top_level_fns(analysis.program)
    rewrites: list[tuple[int, int, str]] = []
    rewritten: list[str] = []
    for name in affected:
        rewrite = effect_row_rewrite(analysis.text, fns[name], effect)
        if rewrite is not None:
            rewrites.append(rewrite)
            rewritten.append(name)
    if not rewrites:
        # Every affected row already names the effect: nothing to
        # verify, nothing to apply — the documented no-op shape.
        return {
            "applied": False,
            "ok": True,
            "proof_delta": None,
            "diagnostics": 0,
            "client": None,
            "rewritten": [],
        }

    candidate = analysis.text
    for start, end, replacement in sorted(rewrites, reverse=True):
        candidate = candidate[:start] + replacement + candidate[end:]
    response = await apply_propose_edit(
        server, uri, candidate, force=False, base_text=analysis.text,
        version=version,
    )
    response["rewritten"] = rewritten
    return response
