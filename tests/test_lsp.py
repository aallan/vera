"""Tests for vera/lsp/ — transport skeleton + coordinate layer (#222 Phase C).

Three layers, matching the #222 plan's testing strategy:

1. **Coordinate conversion** (the substance): parametrized goldens for
   the three coordinate systems — ``ast.Span`` (1-based line, 1-based
   code-point column, exclusive end), ``SourceLocation`` (1-based
   line, 0-based column), LSP (0-based line, UTF-16 column) — with
   multi-byte and astral-plane fixtures, plus round-trips.
2. **Document store**: open/change/close semantics, version tracking,
   index invalidation on change.
3. **End-to-end**: one stdio round-trip against the real ``vera lsp``
   subprocess (initialize → didOpen → shutdown → exit), pinning the
   advertised capabilities.  Transport logic beyond the wire round-trip
   is pygls' responsibility, not ours, so one e2e test suffices.
"""

from __future__ import annotations

import json
import subprocess
import sys

import pytest

from lsprotocol import types as lsp

from vera.ast import Span
from vera.errors import SourceLocation
from vera.lsp.convert import (
    LineIndex,
    location_to_position,
    location_to_range,
    position_to_cp,
    span_to_range,
)
from vera.lsp.documents import DocumentStore

# A line with an astral-plane char: "ab🎉cd" — 🎉 (U+1F389) is ONE
# code point but TWO UTF-16 code units, so LSP columns after it shift
# by one relative to Python string indices.
ASTRAL_LINE = "ab\U0001f389cd"


class TestLineIndex:
    @pytest.mark.parametrize(
        ("cp_col", "utf16_col"),
        [(0, 0), (1, 1), (2, 2), (3, 4), (4, 5), (5, 6)],
    )
    def test_cp_to_utf16_astral(self, cp_col: int, utf16_col: int) -> None:
        index = LineIndex(ASTRAL_LINE)
        assert index.cp_to_utf16(0, cp_col) == utf16_col

    @pytest.mark.parametrize(
        ("utf16_col", "cp_col"),
        [(0, 0), (1, 1), (2, 2), (4, 3), (5, 4), (6, 5)],
    )
    def test_utf16_to_cp_astral(self, utf16_col: int, cp_col: int) -> None:
        index = LineIndex(ASTRAL_LINE)
        assert index.utf16_to_cp(0, utf16_col) == cp_col

    def test_utf16_inside_surrogate_pair_snaps_to_char_start(self) -> None:
        # UTF-16 offset 3 lands inside 🎉's surrogate pair; the LSP
        # spec says invalid positions degrade gracefully — we snap to
        # the character's start (code point 2).
        index = LineIndex(ASTRAL_LINE)
        assert index.utf16_to_cp(0, 3) == 2

    def test_ascii_is_identity(self) -> None:
        index = LineIndex("plain ascii\nsecond line")
        assert index.cp_to_utf16(1, 6) == 6
        assert index.utf16_to_cp(1, 6) == 6

    def test_out_of_range_line_degrades_to_identity(self) -> None:
        index = LineIndex("one line")
        assert index.cp_to_utf16(99, 5) == 0  # empty virtual line
        assert index.utf16_to_cp(99, 5) == 0

    def test_column_clamped_to_line_length(self) -> None:
        index = LineIndex("abc")
        assert index.cp_to_utf16(0, 99) == 3

    def test_bmp_multibyte_is_one_unit(self) -> None:
        # é and → are multi-byte in UTF-8 but single UTF-16 units;
        # only astral chars shift LSP columns.
        index = LineIndex("é→x")
        assert index.cp_to_utf16(0, 3) == 3


class TestSpanConversion:
    def test_span_is_one_based_inclusive_to_lsp_zero_based(self) -> None:
        # Span line 2, cols 3..6 (1-based, exclusive end) on ASCII →
        # LSP line 1, chars 2..5.
        index = LineIndex("first\nabcdefgh")
        span = Span(line=2, column=3, end_line=2, end_column=6)
        r = span_to_range(span, index)
        assert (r.start.line, r.start.character) == (1, 2)
        assert (r.end.line, r.end.character) == (1, 5)

    def test_span_after_astral_char_shifts_utf16(self) -> None:
        # Span covering "cd" in "ab🎉cd": code points 3..5 → 1-based
        # cols 4..6; UTF-16 chars 4..6 (the 🎉 occupies units 2-3).
        index = LineIndex(ASTRAL_LINE)
        span = Span(line=1, column=4, end_line=1, end_column=6)
        r = span_to_range(span, index)
        assert (r.start.character, r.end.character) == (4, 6)


class TestLocationConversion:
    def test_location_column_is_zero_based(self) -> None:
        # SourceLocation col is 0-based (unlike Span) — col 4 on ASCII
        # maps straight to LSP char 4.
        index = LineIndex("abcdefgh")
        loc = SourceLocation(file=None, line=1, column=4)
        pos = location_to_position(loc, index)
        assert (pos.line, pos.character) == (0, 4)

    def test_location_range_widens_over_slot_token(self) -> None:
        # Point at the @ of "@Int.0" widens across the slot token.
        index = LineIndex("  @Int.0 + 1")
        loc = SourceLocation(file=None, line=1, column=2)
        r = location_to_range(loc, index)
        assert r.start.character == 2
        assert r.end.character == 8  # past "@Int.0"

    def test_location_range_on_non_token_is_one_char(self) -> None:
        index = LineIndex("a (b)")
        loc = SourceLocation(file=None, line=1, column=2)  # the "("
        r = location_to_range(loc, index)
        assert (r.start.character, r.end.character) == (2, 3)

    def test_location_range_at_eol_is_empty_not_crashing(self) -> None:
        index = LineIndex("ab")
        loc = SourceLocation(file=None, line=1, column=2)
        r = location_to_range(loc, index)
        assert r.start.character == 2
        assert r.end.character == 2

    def test_position_to_cp_round_trip(self) -> None:
        index = LineIndex(ASTRAL_LINE)
        pos = lsp.Position(line=0, character=4)  # after 🎉
        line1, cp = position_to_cp(pos, index)
        assert (line1, cp) == (1, 3)


class TestDocumentStore:
    def test_open_get_close(self) -> None:
        store = DocumentStore()
        store.open("file:///a.vera", "text", version=1)
        doc = store.get("file:///a.vera")
        assert doc is not None and doc.text == "text" and doc.version == 1
        store.close("file:///a.vera")
        assert store.get("file:///a.vera") is None
        assert len(store) == 0

    def test_change_replaces_text_and_invalidates_index(self) -> None:
        store = DocumentStore()
        doc = store.open("file:///a.vera", "old", version=1)
        first_index = doc.index
        store.change("file:///a.vera", "new text", version=2)
        assert doc.text == "new text" and doc.version == 2
        assert doc.index is not first_index  # rebuilt lazily

    def test_change_without_open_creates_document(self) -> None:
        store = DocumentStore()
        doc = store.change("file:///b.vera", "hello", version=3)
        assert store.get("file:///b.vera") is doc
        assert doc.version == 3

    def test_close_unknown_uri_is_noop(self) -> None:
        store = DocumentStore()
        store.open("file:///kept.vera", "text")
        store.close("file:///never-opened.vera")
        # Observable postcondition: nothing raised AND unrelated
        # documents are untouched.
        assert len(store) == 1
        assert store.get("file:///kept.vera") is not None


def _lsp_msg(payload: dict[str, object]) -> bytes:
    body = json.dumps(payload).encode("utf-8")
    return f"Content-Length: {len(body)}\r\n\r\n".encode() + body


class TestServerEndToEnd:
    def test_stdio_handshake_round_trip(self) -> None:
        """initialize → didOpen → shutdown → exit against the real
        ``vera lsp`` subprocess, over raw JSON-RPC stdio framing."""
        proc = subprocess.Popen(
            [sys.executable, "-m", "vera.cli", "lsp"],
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
        requests = (
            _lsp_msg({
                "jsonrpc": "2.0", "id": 1, "method": "initialize",
                "params": {
                    "processId": None, "rootUri": None,
                    "capabilities": {},
                },
            })
            + _lsp_msg({
                "jsonrpc": "2.0", "method": "initialized", "params": {},
            })
            + _lsp_msg({
                "jsonrpc": "2.0", "method": "textDocument/didOpen",
                "params": {"textDocument": {
                    "uri": "file:///t.vera", "languageId": "vera",
                    "version": 1, "text": "-- comment\n",
                }},
            })
            + _lsp_msg({
                "jsonrpc": "2.0", "id": 2, "method": "shutdown",
                "params": None,
            })
            + _lsp_msg({"jsonrpc": "2.0", "method": "exit", "params": None})
        )
        try:
            out, err = proc.communicate(requests, timeout=60)
        except subprocess.TimeoutExpired:
            proc.kill()
            out, err = proc.communicate()
            pytest.fail(
                "vera lsp subprocess timed out; killed to avoid an "
                f"orphan. stdout={out[:300]!r} stderr={err[:300]!r}"
            )
        text = out.decode("utf-8", errors="replace")
        assert '"serverInfo"' in text, (text[:300], err.decode()[:300])
        assert "vera-lsp" in text
        assert '"textDocumentSync"' in text
        assert proc.returncode == 0

    def test_create_server_handlers_update_store(self) -> None:
        """Document-sync handlers drive the store (in-process, no IO)."""
        from vera.lsp.server import create_server

        server = create_server()
        protocol = server.protocol
        # Drive the registered feature handlers directly through the
        # feature manager — transport-free.
        fm = protocol.fm if hasattr(protocol, "fm") else server.feature_manager
        open_handler = fm.features[lsp.TEXT_DOCUMENT_DID_OPEN]
        change_handler = fm.features[lsp.TEXT_DOCUMENT_DID_CHANGE]
        close_handler = fm.features[lsp.TEXT_DOCUMENT_DID_CLOSE]

        open_handler(lsp.DidOpenTextDocumentParams(
            text_document=lsp.TextDocumentItem(
                uri="file:///x.vera", language_id="vera",
                version=1, text="one",
            ),
        ))
        assert server.store.get("file:///x.vera").text == "one"

        change_handler(lsp.DidChangeTextDocumentParams(
            text_document=lsp.VersionedTextDocumentIdentifier(
                uri="file:///x.vera", version=2,
            ),
            content_changes=[
                lsp.TextDocumentContentChangeWholeDocument(text="two"),
            ],
        ))
        assert server.store.get("file:///x.vera").text == "two"
        assert server.store.get("file:///x.vera").version == 2

        close_handler(lsp.DidCloseTextDocumentParams(
            text_document=lsp.TextDocumentIdentifier(uri="file:///x.vera"),
        ))
        assert server.store.get("file:///x.vera") is None
