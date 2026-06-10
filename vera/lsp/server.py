"""The ``vera lsp`` language server (#222).

Phase C delivered the transport: handshake, full-text document sync,
the in-memory :class:`~vera.lsp.documents.DocumentStore`, and the
coordinate layer.  Phase D wires the obligation core in behind it:
``publishDiagnostics`` (tier-annotated, with per-function tier hints),
hover from the checker's expression-type side-table, slot
go-to-definition, and typed-hole completion — all computed by the pure
backing functions in :mod:`vera.lsp.features` and served here.

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
from vera.lsp.features import (
    Analysis,
    analyze,
    completion_at,
    definition_at,
    hover_at,
    to_lsp_diagnostics,
)
from vera.obligations.session import VerificationSession


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

    return server


def main() -> None:
    """Entry point for ``vera lsp``: serve LSP over stdio."""
    create_server().start_io()
