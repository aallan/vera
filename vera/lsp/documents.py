"""In-memory document store for the LSP server (#222 Phase C).

The store is the source of truth for open files: every feature reads
document text from here, never from disk, so unsaved editor buffers
are what get verified.  (Imported modules still resolve from disk in
the single-file project model — making the *resolver* buffer-aware is
deferred until the multi-file model matters, per the plan's risk
notes.)

Sync model: full-text (``TextDocumentSyncKind.Full``).  Incremental
sync is a transport optimisation the obligation core cannot exploit
yet — its invalidation operates on whole-function hashes — so the
skeleton keeps the simplest correct thing.  Each change bumps
``version`` and invalidates the cached :class:`LineIndex`.
"""

from __future__ import annotations

from dataclasses import dataclass, field

from vera.lsp.convert import LineIndex


@dataclass
class Document:
    """One open document: URI, current text, version, lazy line index."""

    uri: str
    text: str
    version: int = 0
    _index: LineIndex | None = field(default=None, repr=False)

    @property
    def index(self) -> LineIndex:
        if self._index is None:
            self._index = LineIndex(self.text)
        return self._index


class DocumentStore:
    """URI-keyed map of open documents."""

    def __init__(self) -> None:
        self._docs: dict[str, Document] = {}

    def open(self, uri: str, text: str, version: int = 0) -> Document:
        doc = Document(uri=uri, text=text, version=version)
        self._docs[uri] = doc
        return doc

    def change(self, uri: str, text: str, version: int) -> Document:
        """Full-text replacement; creates the document if the client
        sent didChange without didOpen (defensive — some clients do)."""
        doc = self._docs.get(uri)
        if doc is None:
            return self.open(uri, text, version)
        doc.text = text
        doc.version = version
        doc._index = None
        return doc

    def close(self, uri: str) -> None:
        self._docs.pop(uri, None)

    def get(self, uri: str) -> Document | None:
        return self._docs.get(uri)

    def __len__(self) -> int:
        return len(self._docs)
