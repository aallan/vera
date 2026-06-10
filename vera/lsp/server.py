"""The ``vera lsp`` language server — transport skeleton (#222 Phase C).

Phase C is deliberately featureless: the server completes the LSP
handshake, advertises full-text document sync, and maintains the
in-memory :class:`~vera.lsp.documents.DocumentStore`.  Phase D wires
the obligation core in behind this transport (publishDiagnostics,
hover, slot goto, typed-hole completion); Phase E adds the
``vera/speculativeEdit`` extension.  Keeping the skeleton free of
language features means the capability surface advertised at
``initialize`` never promises something unimplemented.

Structure note: ``VeraLanguageServer`` subclasses pygls 2.x's typed
``pygls.lsp.server.LanguageServer`` (the 1.x ``pygls.server`` path no
longer exists) and carries the document store as a declared attribute.

Threading note (Phase D forward-reference): Z3 contexts are not
thread-safe, so all verification will be serialised through a single
session-owning worker; the pygls event loop itself never touches the
``VerificationSession``.
"""

from __future__ import annotations

from typing import Any

from lsprotocol import types as lsp
from pygls.lsp.server import LanguageServer

from vera import __version__
from vera.lsp.documents import DocumentStore


class VeraLanguageServer(LanguageServer):
    """LanguageServer carrying the in-memory document store."""

    def __init__(self) -> None:
        super().__init__(
            name="vera-lsp",
            version=__version__,
            text_document_sync_kind=lsp.TextDocumentSyncKind.Full,
        )
        self.store = DocumentStore()


def create_server() -> VeraLanguageServer:
    """Build a fresh server with document-sync handlers registered.

    Factory (rather than a module-level singleton) so each test gets
    an isolated instance with its own store.
    """
    server = VeraLanguageServer()
    store = server.store

    @server.feature(lsp.TEXT_DOCUMENT_DID_OPEN)
    def did_open(
        ls: Any, params: lsp.DidOpenTextDocumentParams,
    ) -> None:
        doc = params.text_document
        store.open(doc.uri, doc.text, doc.version)

    @server.feature(lsp.TEXT_DOCUMENT_DID_CHANGE)
    def did_change(
        ls: Any, params: lsp.DidChangeTextDocumentParams,
    ) -> None:
        # Full sync: the last content change carries the whole text.
        if params.content_changes:
            text = params.content_changes[-1].text
            store.change(
                params.text_document.uri,
                text,
                params.text_document.version,
            )

    @server.feature(lsp.TEXT_DOCUMENT_DID_CLOSE)
    def did_close(
        ls: Any, params: lsp.DidCloseTextDocumentParams,
    ) -> None:
        store.close(params.text_document.uri)

    return server


def main() -> None:
    """Entry point for ``vera lsp``: serve LSP over stdio."""
    create_server().start_io()
