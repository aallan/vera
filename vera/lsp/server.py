"""The ``vera lsp`` language server (#222).

Phase C delivered the transport: handshake, full-text document sync,
the in-memory :class:`~vera.lsp.documents.DocumentStore`, and the
coordinate layer.  Phase D wires the obligation core in behind it:
``publishDiagnostics`` (tier-annotated, with per-function tier hints),
hover from the checker's expression-type side-table, slot
go-to-definition, and typed-hole completion — all computed by the pure
backing functions in :mod:`vera.lsp.features` and served here.
Phase F adds the skill-layer workflows (:mod:`vera.lsp.workflows`):
multi-step edit → verify → apply sequences exposed as single methods,
so the verification gate cannot be skipped or reordered.

Structure note: ``VeraLanguageServer`` subclasses pygls 2.x's typed
``pygls.lsp.server.LanguageServer`` (the 1.x ``pygls.server`` path no
longer exists) and carries the store, the warm
``VerificationSession``, and the per-URI analysis cache.

Threading: Z3 contexts are not thread-safe, so every analysis runs
under ``analysis_lock`` — one session, strictly serialised, no matter
which transport thread delivers the triggering notification.  The three
edit-applying methods are coroutines: each waits for the client's
answer to its ``workspace/applyEdit`` with the lock released, so the
notifications that arrive meanwhile are read and analysed while it
waits.

Document state: the store, the per-URI analysis table and the published
diagnostics describe the client's open buffer, so they are written only
from the client's own ``didOpen`` / ``didChange`` / ``didClose``
(#1444).  An edit the server proposes reaches them as the client's
``didChange`` if the client applies it, and not at all otherwise.  An
analysis that raises leaves no entry for the text it failed on, and an
``E699`` is published in its place; every reader of the table goes
through :func:`~vera.lsp.features.current_analysis`, which returns only
an analysis of the open text.
"""

from __future__ import annotations

import functools
import logging
import threading

from typing import Any

from lsprotocol import types as lsp
from pygls.exceptions import JsonRpcInvalidParams
from pygls.lsp.server import LanguageServer
from pygls.protocol import LanguageServerProtocol

from vera import __version__
from vera.lsp.documents import DocumentStore
from vera.lsp.extensions import speculative_edit
from vera.lsp.features import (
    Analysis,
    analysis_failure,
    analyze,
    completion_at,
    current_analysis,
    definition_at,
    hover_at,
    to_lsp_diagnostics,
)
from vera.lsp.workflows import (
    APPLY_EDIT_TIMEOUT_S,
    StaleDocumentError,
    add_effect,
    apply_propose_edit,
    require_current,
    strengthen_contract,
)
from vera.obligations.session import VerificationSession


_MISSING = object()

logger = logging.getLogger(__name__)


def _param(params: Any, key: str) -> Any:
    """Extract *key* from custom-method params of either shape.

    pygls hands custom methods an attribute-style namespace; tests and
    other in-process callers may pass a plain dict.  Membership is
    decided with a sentinel, never truthiness — ``text=""`` (replace
    with an empty document) is a present value, and falling through to
    ``.get`` on an attribute carrier would raise ``AttributeError``.
    """
    value = getattr(params, key, _MISSING)
    if value is _MISSING and hasattr(params, "get"):
        value = params.get(key, _MISSING)
    return None if value is _MISSING else value


def _require_str(params: Any, key: str) -> str:
    """Extract *key* and fail closed at the protocol boundary.

    Custom methods take their params as plain JSON, so nothing
    upstream validates the shape; a missing or non-string field would
    otherwise surface as an opaque internal error from deep inside
    the parse pipeline.  ``JsonRpcInvalidParams`` (-32602) is the
    JSON-RPC-native refusal.  The empty string stays valid — it is a
    present value (replace-with-empty-document), not a missing one.
    """
    value = _param(params, key)
    if not isinstance(value, str):
        raise JsonRpcInvalidParams(
            message=f"{key!r} must be a string, got {type(value).__name__}",
        )
    return value


def _version_param(params: Any) -> int | None:
    """The optional ``version``: the document version a request was made
    from, or ``None`` when the client did not say.

    A JSON integer, or absent (``null`` counts as absent, as it does for
    an LSP ``OptionalVersionedTextDocumentIdentifier``).  Anything else
    fails closed: a version the server cannot compare is not permission
    to skip the comparison.  ``bool`` is refused explicitly, because
    Python counts it as an ``int``.
    """
    value = _param(params, "version")
    if value is None:
        return None
    if isinstance(value, bool) or not isinstance(value, int):
        raise JsonRpcInvalidParams(
            message=(
                f"'version' must be an integer, got {type(value).__name__}"
            ),
        )
    return value


def _force_param(params: Any) -> bool:
    """The ``force`` flag, failing closed: only JSON ``true`` engages.

    ``force`` bypasses the verification gate — the one bit whose whole
    purpose is to be hard to skip — so generic truthiness is the wrong
    coercion: a malformed payload like ``"force": "false"`` must not
    silently apply an unverified edit.  Strictness costs a refused
    edit with an explanatory delta; leniency costs the failure mode
    the method exists to prevent.
    """
    return _param(params, "force") is True


class VeraProtocol(LanguageServerProtocol):
    """pygls' protocol, handing over the client's answer to
    ``workspace/applyEdit`` UNSTRUCTURED.

    pygls structures that answer into ``ApplyWorkspaceEditResult``, which
    turns ``"applied": "false"`` into ``True`` and raises in the reader on
    ``null`` or ``{}`` -- dropping the answer, so the edit request never
    completes.  The edit workflows read the raw answer themselves and
    accept only a strict boolean (:func:`vera.lsp.workflows.read_answer`,
    #1444).
    """

    @functools.lru_cache  # the shape pygls declares, so the override matches
    def get_result_type(self, method: str) -> type[Any] | None:
        if method == lsp.WORKSPACE_APPLY_EDIT:
            return None
        return super().get_result_type(method)


class VeraLanguageServer(LanguageServer):
    """LanguageServer carrying document, session, and analysis state."""

    def __init__(self) -> None:
        super().__init__(
            name="vera-lsp",
            version=__version__,
            text_document_sync_kind=lsp.TextDocumentSyncKind.Full,
            protocol_cls=VeraProtocol,
        )
        #: How long an edit workflow waits for an applyEdit answer.
        self.apply_edit_timeout_s = APPLY_EDIT_TIMEOUT_S
        self.store = DocumentStore()
        self.session = VerificationSession()
        self.analysis_lock = threading.Lock()
        self.analyses: dict[str, Analysis] = {}

    def analyze_and_publish(self, uri: str, text: str) -> None:
        """Run the pipeline for *uri* and publish its diagnostics.

        Called with the text the handler has just stored, so the entry
        this writes describes the client's buffer.  If the pipeline
        RAISES, the entry is removed rather than left describing the
        text before this one, and the diagnostic published in place of
        the analysis names the failure (#1444): every reader then
        answers as it does for a document with no analysis, and the
        client can see why.
        """
        with self.analysis_lock:
            try:
                analysis = analyze(self.session, uri, text)
                # Inside the `try`: an analysis is kept only once what is
                # published for it has been built, so a conversion that
                # raises is reported like any other failure on this text.
                diagnostics = to_lsp_diagnostics(analysis)
            except Exception as exc:
                # Any exception is a compiler bug on this text; it goes to
                # the log with its traceback and to the client as E699.
                logger.exception("analysis of %s raised", uri)
                self.analyses.pop(uri, None)
                diagnostics = analysis_failure(uri, text, exc)
            else:
                self.analyses[uri] = analysis
        self.text_document_publish_diagnostics(
            lsp.PublishDiagnosticsParams(uri=uri, diagnostics=diagnostics),
        )

    def current_analysis(self, uri: str) -> Analysis | None:
        """The analysis of *uri*'s open text, or ``None``: the one reader
        of the analysis table (:func:`vera.lsp.features.current_analysis`
        checks the entry against the open document)."""
        return current_analysis(self.store.get(uri), self.analyses.get(uri))


def create_server() -> VeraLanguageServer:
    """Build a fresh server with all handlers registered.

    Factory (rather than a module-level singleton) so each test gets
    an isolated instance with its own store, session, and caches.
    """
    server = VeraLanguageServer()
    store = server.store

    @server.feature(lsp.TEXT_DOCUMENT_DID_OPEN)
    def did_open(
        ls: Any, params: lsp.DidOpenTextDocumentParams,
    ) -> None:
        doc = params.text_document
        store.open(doc.uri, doc.text, doc.version)
        server.analyze_and_publish(doc.uri, doc.text)

    @server.feature(lsp.TEXT_DOCUMENT_DID_CHANGE)
    def did_change(
        ls: Any, params: lsp.DidChangeTextDocumentParams,
    ) -> None:
        # Full sync: the last content change carries the whole text.
        if params.content_changes:
            text = params.content_changes[-1].text
            doc = store.change(
                params.text_document.uri,
                text,
                params.text_document.version,
            )
            server.analyze_and_publish(doc.uri, doc.text)

    @server.feature(lsp.TEXT_DOCUMENT_DID_CLOSE)
    def did_close(
        ls: Any, params: lsp.DidCloseTextDocumentParams,
    ) -> None:
        store.close(params.text_document.uri)
        server.analyses.pop(params.text_document.uri, None)
        # Clear stale squiggles for the closed buffer.
        server.text_document_publish_diagnostics(
            lsp.PublishDiagnosticsParams(
                uri=params.text_document.uri, diagnostics=[],
            ),
        )

    @server.feature(lsp.TEXT_DOCUMENT_HOVER)
    def hover(
        ls: Any, params: lsp.HoverParams,
    ) -> lsp.Hover | None:
        analysis = server.current_analysis(params.text_document.uri)
        if analysis is None:
            return None
        return hover_at(analysis, params.position)

    @server.feature(lsp.TEXT_DOCUMENT_DEFINITION)
    def definition(
        ls: Any, params: lsp.DefinitionParams,
    ) -> lsp.Location | None:
        analysis = server.current_analysis(params.text_document.uri)
        if analysis is None:
            return None
        return definition_at(analysis, params.position)

    @server.feature(
        lsp.TEXT_DOCUMENT_COMPLETION,
        lsp.CompletionOptions(trigger_characters=["?"]),
    )
    def completion(
        ls: Any, params: lsp.CompletionParams,
    ) -> lsp.CompletionList | None:
        analysis = server.current_analysis(params.text_document.uri)
        if analysis is None:
            return None
        return completion_at(analysis, params.position)

    @server.feature("vera/speculativeEdit")
    def vera_speculative_edit(ls: Any, params: Any) -> dict[str, Any]:
        """#222 Phase E: proof-delta for an in-memory edit.

        The speculative verify shares the warm session (and its
        discharge cache — pre-warming, by design) under the same lock,
        but never touches the per-URI analysis table or published
        diagnostics: the canonical editor state is unchanged.  The delta
        is only as good as its baseline, so the request is refused on
        the terms ``vera/proposeEdit`` is refused on: no open document,
        no analysis of its current text, or an optional ``version`` it
        is no longer at.  An empty baseline would read as "every proof
        kept" about a text nothing was measured against.
        """
        uri = _require_str(params, "uri")
        text = _require_str(params, "text")
        version = _version_param(params)
        with server.analysis_lock:
            try:
                _, baseline_analysis = require_current(
                    uri, server.store.get(uri), server.current_analysis(uri),
                    None, version,
                )
            except StaleDocumentError as exc:
                raise JsonRpcInvalidParams(message=str(exc)) from exc
            return speculative_edit(
                server.session, baseline_analysis.obligations, uri, text,
            )

    @server.feature("vera/proposeEdit")
    async def vera_propose_edit(ls: Any, params: Any) -> dict[str, Any]:
        """#222 Phase F1: enforced edit → verify → apply workflow.

        The whole sequence — speculative verify, gate, and (on pass) a
        version-guarded ``workspace/applyEdit`` and the wait for the
        client's answer — runs in
        :func:`vera.lsp.workflows.apply_propose_edit`; this handler is
        wire glue only.  It is a coroutine so that pygls runs it as a
        task and goes on reading messages — the client's answer among
        them — while it waits.  A proposal against an analysis that
        does not describe the open document refuses with InvalidParams,
        as the other two edit methods refuse requests they cannot serve
        against the document as it stands.
        """
        uri = _require_str(params, "uri")
        text = _require_str(params, "text")
        version = _version_param(params)
        try:
            return await apply_propose_edit(
                server, uri, text, _force_param(params), version=version,
            )
        except StaleDocumentError as exc:
            raise JsonRpcInvalidParams(message=str(exc)) from exc

    @server.feature("vera/strengthenContract")
    async def vera_strengthen_contract(
        ls: Any, params: Any,
    ) -> dict[str, Any]:
        """#222 Phase F2: contract change with call-site audit.

        Splice + verify + gate run in
        :func:`vera.lsp.workflows.strengthen_contract`; requests that
        cannot name a splice target (unknown function, unopened or
        unparseable document) refuse with InvalidParams.
        """
        uri = _require_str(params, "uri")
        fn_name = _require_str(params, "fn")
        kind = _require_str(params, "kind")
        expr = _require_str(params, "expr")
        if kind not in ("requires", "ensures"):
            raise JsonRpcInvalidParams(
                message=f"'kind' must be 'requires' or 'ensures', "
                f"got {kind!r}",
            )
        version = _version_param(params)
        try:
            return await strengthen_contract(
                server, uri, fn_name, kind, expr, version=version,
            )
        except ValueError as exc:
            raise JsonRpcInvalidParams(message=str(exc)) from exc

    @server.feature("vera/addEffect")
    async def vera_add_effect(ls: Any, params: Any) -> dict[str, Any]:
        """#222 Phase F3: effect propagation through the call graph.

        Closure + multi-site rewrite + verify + gate run in
        :func:`vera.lsp.workflows.add_effect`; requests that cannot
        name a target refuse with InvalidParams.
        """
        uri = _require_str(params, "uri")
        fn_name = _require_str(params, "fn")
        effect = _require_str(params, "effect").strip()
        if not effect:
            raise JsonRpcInvalidParams(
                message="'effect' must be a non-empty effect reference",
            )
        version = _version_param(params)
        try:
            return await add_effect(
                server, uri, fn_name, effect, version=version,
            )
        except ValueError as exc:
            raise JsonRpcInvalidParams(message=str(exc)) from exc

    return server


def main() -> None:
    """Entry point for ``vera lsp``: serve LSP over stdio."""
    create_server().start_io()
