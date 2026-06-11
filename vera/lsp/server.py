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
which transport thread delivers the triggering notification.
"""

from __future__ import annotations

import threading

from typing import Any

from lsprotocol import types as lsp
from pygls.lsp.server import LanguageServer

from vera import __version__
from vera.lsp.documents import DocumentStore
from vera.lsp.extensions import speculative_edit
from vera.lsp.features import (
    Analysis,
    analyze,
    completion_at,
    definition_at,
    hover_at,
    to_lsp_diagnostics,
)
from vera.lsp.workflows import apply_propose_edit
from vera.obligations.session import VerificationSession


_MISSING = object()


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


class VeraLanguageServer(LanguageServer):
    """LanguageServer carrying document, session, and analysis state."""

    def __init__(self) -> None:
        super().__init__(
            name="vera-lsp",
            version=__version__,
            text_document_sync_kind=lsp.TextDocumentSyncKind.Full,
        )
        self.store = DocumentStore()
        self.session = VerificationSession()
        self.analysis_lock = threading.Lock()
        self.analyses: dict[str, Analysis] = {}

    def analyze_and_publish(self, uri: str, text: str) -> None:
        """Run the pipeline for *uri* and publish its diagnostics."""
        with self.analysis_lock:
            analysis = analyze(self.session, uri, text)
            self.analyses[uri] = analysis
        self.text_document_publish_diagnostics(
            lsp.PublishDiagnosticsParams(
                uri=uri,
                diagnostics=to_lsp_diagnostics(analysis),
            ),
        )


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
        analysis = server.analyses.get(params.text_document.uri)
        if analysis is None:
            return None
        return hover_at(analysis, params.position)

    @server.feature(lsp.TEXT_DOCUMENT_DEFINITION)
    def definition(
        ls: Any, params: lsp.DefinitionParams,
    ) -> lsp.Location | None:
        analysis = server.analyses.get(params.text_document.uri)
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
        analysis = server.analyses.get(params.text_document.uri)
        if analysis is None:
            return None
        return completion_at(analysis, params.position)

    @server.feature("vera/speculativeEdit")
    def vera_speculative_edit(ls: Any, params: Any) -> dict[str, Any]:
        """#222 Phase E: proof-delta for an in-memory edit.

        The speculative verify shares the warm session (and its
        discharge cache — pre-warming, by design) under the same lock,
        but never touches the per-URI analysis table or published
        diagnostics: the canonical editor state is unchanged.
        """
        uri = _param(params, "uri")
        text = _param(params, "text")
        baseline_analysis = server.analyses.get(uri)
        baseline = (
            baseline_analysis.obligations
            if baseline_analysis is not None else []
        )
        with server.analysis_lock:
            return speculative_edit(server.session, baseline, uri, text)

    @server.feature("vera/proposeEdit")
    def vera_propose_edit(ls: Any, params: Any) -> dict[str, Any]:
        """#222 Phase F1: enforced edit → verify → apply workflow.

        The whole sequence — speculative verify, gate, and (on pass)
        ``workspace/applyEdit`` + canonical-state update — runs in
        :func:`vera.lsp.workflows.apply_propose_edit`; this handler is
        wire glue only.
        """
        uri = _param(params, "uri")
        text = _param(params, "text")
        force = bool(_param(params, "force"))
        return apply_propose_edit(server, uri, text, force)

    return server


def main() -> None:
    """Entry point for ``vera lsp``: serve LSP over stdio."""
    create_server().start_io()
