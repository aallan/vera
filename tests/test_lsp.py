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
import os
import pathlib
import subprocess
import sys

import pytest

from lsprotocol import types as lsp

from vera.ast import QualifiedEffectRef, Span
from vera.errors import SourceLocation
from vera.lsp.convert import (
    LineIndex,
    location_to_position,
    location_to_range,
    position_to_cp,
    span_to_range,
    uri_to_path,
)
from vera.lsp.documents import DocumentStore

# A line with an astral-plane char: "ab🎉cd" — 🎉 (U+1F389) is ONE
# code point but TWO UTF-16 code units, so LSP columns after it shift
# by one relative to Python string indices.
ASTRAL_LINE = "ab\U0001f389cd"


class TestUriToPath:
    """`uri_to_path` — the fourth conversion at the LSP boundary (#1246).

    LSP identifies a document by URI; the compiler identifies it by
    path, and USES the path (the module resolver reads imports from
    `Path(file).parent`).  Handing the pipeline a raw `file://` URI made
    that parent the literal directory `file:`.
    """

    def test_file_uri_round_trips_a_real_path(
        self, tmp_path: pathlib.Path,
    ) -> None:
        target = tmp_path / "entry.vera"
        target.write_text("", encoding="utf-8")
        assert uri_to_path(target.as_uri()) == str(target)

    def test_percent_escapes_are_decoded_once(
        self, tmp_path: pathlib.Path,
    ) -> None:
        """A space escapes to `%20`; a literal `%` escapes to `%25`.

        Decoding twice would turn `a%2520b` back into `a%20b` instead of
        the literal `a%20b` the path really holds, so the round-trip
        through a genuinely `%`-bearing name is the case that separates
        one unquote from two.
        """
        for name in ("a b.vera", "a%20b.vera"):
            target = tmp_path / name
            target.write_text("", encoding="utf-8")
            assert uri_to_path(target.as_uri()) == str(target), name

    def test_localhost_authority_is_not_part_of_the_path(self) -> None:
        """`file://localhost/x` names `/x`, not `//localhost/x`."""
        assert uri_to_path("file://localhost/tmp/x.vera") == (
            uri_to_path("file:///tmp/x.vera")
        )

    def test_a_foreign_authority_never_raises(self) -> None:
        """`file://host/...` names a file on ANOTHER machine (G1).

        Python 3.14's `url2pathname` validates the authority and raises
        `URLError` for anything but localhost — before the fold that was
        meant to handle it ever ran.  `analyze` calls this outside its
        own try/except, and `analyze_and_publish` reports whatever
        escapes it as an E699 by calling `analysis_failure` -- which
        calls this again, so a raise here would escape the handler
        after all.  3.13 returned a `//host/...` string instead, which on
        POSIX is not a UNC mount but a stray local path — so the old
        behaviour was wrong on every version, just differently.

        This process can only open a LOCAL file, so a remote authority
        names no path here and the URI stays an opaque label — the same
        answer on every Python and platform.
        """
        for uri in (
            "file://myserver/share/x.vera",
            "file://127.0.0.1/tmp/x.vera",
            "file://example.com/a/b.vera",
        ):
            assert uri_to_path(uri) == uri, uri

    def test_scheme_matching_is_case_insensitive(self) -> None:
        """RFC 3986 §3.1: schemes are case-insensitive.

        Asserted RELATIONALLY — every spelling gives the answer the
        lowercase one gives — rather than against a literal
        `/tmp/x.vera`, which is what `url2pathname` returns on POSIX and
        not what it returns on Windows (`\\tmp\\x.vera`).  The property
        is that case does not change the answer, and that is expressible
        without naming the answer at all.  The inequality is the other
        half: without it, three URIs all failing to convert would agree
        with each other and satisfy the equality.
        """
        lowercase = uri_to_path("file:///tmp/x.vera")
        for spelling in (
            "FILE:///tmp/x.vera",
            "File:///tmp/x.vera",
            "fIlE:///tmp/x.vera",
        ):
            assert uri_to_path(spelling) == lowercase, spelling
            assert uri_to_path(spelling) != spelling, spelling

    def test_a_file_uri_naming_no_path_stays_opaque(self) -> None:
        """`file://` and `file:` decode to the empty string.

        This pins the returned STRING only — that a degenerate URI is
        carried through as the opaque label it is, rather than becoming
        `""` and looking like a path.  It does NOT stop the resolver
        rooting at the CWD, and an earlier version of this docstring
        claimed it did: `Path("file:")` is exactly as directory-less as
        `Path("")`, so both give `.`.  That property is enforced at the
        resolver root instead (`VerificationSession.verify_source`) and
        tested by `TestPathlessDocumentIsolation` below — which is the
        test this one was passing for the wrong reason.
        """
        for uri in ("file://", "file:"):
            assert uri_to_path(uri) == uri, uri

    def test_the_root_uri_is_a_path_not_a_degenerate(self) -> None:
        """`file:///` names the root directory, and that IS a path.

        The empty-decode guard must not swallow it: a root resolves
        imports against the filesystem root, which finds nothing and
        says so, where the CWD fallback finds whatever is lying there.
        Pinned so the guard stays keyed on emptiness rather than on
        "looks unlike a document".

        Asserted as the PROPERTY "converted, and the result is a root",
        not as the literal `/`: `url2pathname` returns the platform's
        spelling, `/` on POSIX and `\\` on Windows.  A root is the path
        that has no filename component and is its own parent, which is
        true of both spellings.
        """
        result = uri_to_path("file:///")
        assert result != "file:///"          # it converted at all
        root = pathlib.Path(result)
        assert root.name == "", result       # no filename component
        assert root.parent == root, result   # a root is its own parent

    def test_a_malformed_uri_never_raises(self) -> None:
        """`urlsplit` raises `ValueError` on a bad authority (PR #1282).

        `file://[` is "Invalid IPv6 URL" — and the raise happened before
        any of the guards below, on the same didOpen/didChange path that
        `URLError` escaped from.  Totality is the property; the value is
        the opaque label, because a URI this malformed names no path.
        """
        for uri in ("file://[", "file://[::1", "file://a[b]c/x",
                    "file://]", "file://[]"):
            assert uri_to_path(uri) == uri, uri

    def test_non_file_schemes_pass_through_unchanged(self) -> None:
        """`untitled:` and friends name no path — pre-existing behaviour.

        The pipeline carries such a label without ever opening it, which
        is what an unsaved buffer needs.
        """
        for uri in ("untitled:Untitled-1", "vscode-vfs://host/a.vera",
                    "inmemory://model/1"):
            assert uri_to_path(uri) == uri

    def test_a_bare_path_is_already_a_path(self) -> None:
        """Tests and the CLI-adjacent callers pass plain paths."""
        assert uri_to_path("/tmp/x.vera") == "/tmp/x.vera"


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


# =====================================================================
# Phase D — language features over the obligation core
# =====================================================================

from vera.lsp.features import (  # noqa: E402
    analyze,
    completion_at,
    definition_at,
    hover_at,
    to_lsp_diagnostics,
)
from vera.obligations.session import VerificationSession  # noqa: E402

FEATURE_SRC = (
    "public fn dec(@Nat, @Nat -> @Nat)\n"
    "  requires(@Nat.0 >= 1)\n"
    "  ensures(true)\n"
    "  effects(pure)\n"
    "{\n"
    "  let @Nat = @Nat.0 - 1;\n"
    "  ?\n"
    "}\n"
)


def _analyze(src: str) -> object:
    return analyze(VerificationSession(), "file:///t.vera", src)


class TestAnalyzeDiagnostics:
    def test_parse_error_yields_single_diagnostic(self) -> None:
        a = _analyze("public fn broken(")
        assert len(a.diagnostics) == 1
        assert a.diagnostics[0].severity == "error"
        assert a.program is None
        lsp_diags = to_lsp_diagnostics(a)
        assert len(lsp_diags) == 1
        assert lsp_diags[0].source == "vera"

    def test_type_errors_short_circuit_verification(self) -> None:
        a = _analyze(
            "public fn f(@Int -> @Int)\n"
            "  requires(true) ensures(true) effects(pure)\n"
            '{ "nope" }\n'
        )
        assert any(d.severity == "error" for d in a.diagnostics)
        assert a.obligations == []

    def test_tier3_warning_carries_tier_in_data(self) -> None:
        a = _analyze(
            "public forall<T> fn ident(@T -> @T)\n"
            "  requires(true)\n"
            "  ensures(@T.result == @T.0)\n"
            "  effects(pure)\n"
            "{\n"
            "  @T.0\n"
            "}\n"
        )
        lsp_diags = to_lsp_diagnostics(a)
        e520 = [d for d in lsp_diags if d.code == "E520"]
        assert len(e520) == 1
        assert e520[0].data == {"tier": 3}

    def test_tier_hint_synthesised_per_function(self) -> None:
        a = _analyze(FEATURE_SRC)
        hints = [
            d for d in to_lsp_diagnostics(a) if d.code == "tier"
        ]
        assert len(hints) == 1
        assert hints[0].severity == lsp.DiagnosticSeverity.Hint
        assert "Tier 1" in hints[0].message
        assert "dec" in hints[0].message

    def test_a_file_uri_document_resolves_its_imports(
        self, tmp_path: pathlib.Path,
    ) -> None:
        """The shipped entry point hands `analyze` a URI, not a path.

        `server.py` passes `doc.uri` straight through, and the module
        resolver reads imports from `Path(file).parent` — which for
        `file:///a/b.vera` is the directory `file:`.  So a document with
        imports resolved none of them, produced ZERO obligations and
        zero hints, and said nothing about it: `verify_source` returns
        its resolver errors as `check_diagnostics`, which `analyze`
        does not collect.  Silently unverified, and contradicting
        LSP_SERVER.md's "module imports resolve from disk" (#1246
        adversarial round).
        """
        lib = tmp_path / "glib.vera"
        lib.write_text(
            "module glib;\n"
            "\n"
            "public forall<T> fn pick(@T, @T -> @T)\n"
            "  requires(true)\n"
            "  ensures(true)\n"
            "  effects(pure)\n"
            "{\n"
            "  @T.1\n"
            "}\n",
            encoding="utf-8",
        )
        entry = tmp_path / "entry.vera"
        entry_src = (
            "import glib;\n"
            "\n"
            "public fn main(@Nat, @Nat -> @Nat)\n"
            "  requires(true)\n"
            "  ensures(true)\n"
            "  effects(pure)\n"
            "{\n"
            "  glib::pick(@Nat.1, @Nat.0)\n"
            "}\n"
        )
        entry.write_text(entry_src, encoding="utf-8")

        a = analyze(VerificationSession(), entry.as_uri(), entry_src)
        assert a.obligations, "URI document produced no obligations"
        assert a.path == str(entry), (a.path, str(entry))
        # `uri` still answers the client-facing question unchanged.
        assert a.uri == entry.as_uri()
        # And the #1246 filter works on the REAL path: `glib`'s clone is
        # in the stream, and only `main` gets a hint here.
        assert str(lib) in {ob.file for ob in a.obligations}
        hints = [d for d in to_lsp_diagnostics(a) if d.code == "tier"]
        assert [h.message.split(":")[0] for h in hints] == ["main"], [
            h.message for h in hints
        ]

    def test_analyze_survives_every_document_uri_shape(self) -> None:
        """The escape route G1 travelled, closed at the source.

        `analyze` calls `uri_to_path` BEFORE its try/except.
        `analyze_and_publish` turns what escapes `analyze` into an E699,
        but builds that E699 with `analysis_failure`, which calls
        `uri_to_path` too -- so a raise here would still leave the
        didOpen/didChange handler.  A conversion on that path must be
        total.
        """
        for uri in (
            "file://myserver/share/x.vera",
            "file://127.0.0.1/tmp/x.vera",
            "file://localhost/tmp/x.vera",
            "FILE:///tmp/x.vera",
            "file://",
            "file:",
            "untitled:Untitled-1",
            "vscode-vfs://host/a.vera",
            "",
        ):
            a = analyze(VerificationSession(), uri, FEATURE_SRC)
            assert a.uri == uri, uri
            assert isinstance(a.path, str), uri

    def test_definition_still_reports_the_uri_not_the_path(self) -> None:
        """`textDocument/definition` Locations must carry a URI.

        The path is what the compiler was driven with; the URI is what
        the client is told.  Collapsing the two would have made
        go-to-definition return a bare filesystem path.
        """
        a = analyze(VerificationSession(), "file:///t.vera", FEATURE_SRC)
        loc = definition_at(a, lsp.Position(line=5, character=14))
        assert loc is not None
        assert loc.uri == "file:///t.vera", loc.uri

    def test_imported_modules_obligations_get_no_hint_here(
        self, tmp_path: pathlib.Path,
    ) -> None:
        """A hint belongs to the document its obligations live in (#1246).

        Verifying an entry program verifies the imported modules it
        pulls in, so the obligation stream carries `glib`'s functions
        beside the entry's own.  `publishDiagnostics` is per-URI, and
        `glib`'s line numbers index `glib.vera` — placed in this
        document they land on whatever text happens to occupy that
        line, or past its end.  Before `ProofObligation.file` (#1239)
        nothing could tell them apart.
        """
        lib = tmp_path / "glib.vera"
        lib.write_text(
            "module glib;\n"
            "\n"
            "public forall<T> fn pick(@T, @T -> @T)\n"
            "  requires(true)\n"
            "  ensures(true)\n"
            "  effects(pure)\n"
            "{\n"
            "  @T.1\n"
            "}\n",
            encoding="utf-8",
        )
        entry = tmp_path / "entry.vera"
        entry_src = (
            "import glib;\n"
            "\n"
            "public fn main(@Nat, @Nat -> @Nat)\n"
            "  requires(true)\n"
            "  ensures(true)\n"
            "  effects(pure)\n"
            "{\n"
            "  glib::pick(@Nat.1, @Nat.0)\n"
            "}\n"
        )
        entry.write_text(entry_src, encoding="utf-8")

        a = analyze(VerificationSession(), str(entry), entry_src)
        # The premise: the stream really does carry both files.
        files = {ob.file for ob in a.obligations}
        assert str(lib) in files, files
        assert str(entry) in files, files

        hints = [d for d in to_lsp_diagnostics(a) if d.code == "tier"]
        assert [h.message.split(":")[0] for h in hints] == ["main"], [
            h.message for h in hints
        ]
        # And the one hint that IS published still points at a line of
        # this document rather than at a line number borrowed from it.
        assert hints[0].range.start.line < len(entry_src.splitlines())

    def test_hint_survives_an_obligation_without_a_file(self) -> None:
        """`file=None` means "not from a verifier run", not "foreign".

        Every obligation the verifier reifies from a run carries the
        file it was given, so `None` only reaches here from a
        hand-constructed record; dropping those would silently delete
        a hint rather than move it.
        """
        a = _analyze(FEATURE_SRC)
        assert a.obligations
        for ob in a.obligations:
            ob.file = None
        hints = [d for d in to_lsp_diagnostics(a) if d.code == "tier"]
        assert len(hints) == 1, [h.message for h in hints]

    def test_violated_function_gets_no_cheerful_hint(self) -> None:
        a = _analyze(
            "public fn bad(@Int -> @Int)\n"
            "  requires(true)\n"
            "  ensures(@Int.result > @Int.0)\n"
            "  effects(pure)\n"
            "{\n"
            "  @Int.0\n"
            "}\n"
        )
        codes = [d.code for d in to_lsp_diagnostics(a)]
        assert "tier" not in codes
        assert any(d.severity == "error" for d in a.diagnostics)


class TestPathlessDocumentIsolation:
    """A document with no path on disk is analysed ALONE (#1246 review).

    The resolver roots at `Path(file).parent`, and a document that names
    no location gives `.` — the process CWD.  So a path-less document
    searched for imports wherever the language server was started, and
    whatever importable module was lying there became part of it.
    Measured, not reasoned about: the same source, analysed from a CWD
    that holds an importable `glib.vera` and from one that does not.
    """

    LIB = (
        "module glib;\n"
        "\n"
        "public forall<T> fn pick(@T, @T -> @T)\n"
        "  requires(true)\n"
        "  ensures(true)\n"
        "  effects(pure)\n"
        "{\n"
        "  @T.1\n"
        "}\n"
    )
    SRC = (
        "import glib;\n"
        "\n"
        "public fn main(@Nat, @Nat -> @Nat)\n"
        "  requires(true)\n"
        "  ensures(true)\n"
        "  effects(pure)\n"
        "{\n"
        "  glib::pick(@Nat.1, @Nat.0)\n"
        "}\n"
    )
    #: Every spelling of "this document has no path".
    PATHLESS = ("untitled:Untitled-1", "file:", "file://", "",
                "vscode-vfs://host/a.vera")

    def _analyze_from(
        self, cwd: pathlib.Path, uri: str,
    ) -> object:
        original = os.getcwd()
        os.chdir(cwd)
        try:
            return analyze(VerificationSession(), uri, self.SRC)
        finally:
            os.chdir(original)

    def test_a_pathless_document_ignores_a_module_in_the_cwd(
        self, tmp_path: pathlib.Path,
    ) -> None:
        """The bug, at every path-less spelling.

        Asserted as "no obligation belongs to a foreign file", which is
        the property; an obligation COUNT would also move for unrelated
        reasons, and did — a path-less document now verifies its own
        function instead of being short-circuited by a resolver error.
        """
        holds = tmp_path / "holds"
        holds.mkdir()
        (holds / "glib.vera").write_text(self.LIB, encoding="utf-8")

        for uri in self.PATHLESS:
            a = self._analyze_from(holds, uri)
            foreign = sorted({
                ob.file for ob in a.obligations
                if ob.file is not None and "glib" in ob.file
            })
            assert foreign == [], (uri, foreign)

    def test_the_control_directory_holds_no_module_to_find(
        self, tmp_path: pathlib.Path,
    ) -> None:
        """The control the positive is measured against.

        Without it, "no foreign obligations" would also hold because the
        fixture module was never importable in the first place.
        """
        empty = tmp_path / "empty"
        empty.mkdir()
        holds = tmp_path / "holds"
        holds.mkdir()
        (holds / "glib.vera").write_text(self.LIB, encoding="utf-8")

        for uri in self.PATHLESS:
            a_empty = self._analyze_from(empty, uri)
            a_holds = self._analyze_from(holds, uri)
            assert (
                [ob.file for ob in a_empty.obligations]
                == [ob.file for ob in a_holds.obligations]
            ), uri

    def test_the_module_really_is_importable_from_that_directory(
        self, tmp_path: pathlib.Path,
    ) -> None:
        """The premise: a REAL path in that directory does pull it in.

        This is what makes the two tests above evidence rather than a
        pair of tautologies — if the fixture were simply unimportable,
        they would pass with the fix reverted.
        """
        holds = tmp_path / "holds"
        holds.mkdir()
        (holds / "glib.vera").write_text(self.LIB, encoding="utf-8")
        entry = holds / "entry.vera"
        entry.write_text(self.SRC, encoding="utf-8")

        a = analyze(VerificationSession(), entry.as_uri(), self.SRC)
        foreign = sorted({
            ob.file for ob in a.obligations
            if ob.file is not None and "glib" in ob.file
        })
        assert foreign, [ob.file for ob in a.obligations]

    def test_the_unresolved_import_is_reported_not_swallowed(
        self, tmp_path: pathlib.Path,
    ) -> None:
        """Isolation must not become silence.

        Dropping the modules is only honest if the import that could not
        resolve says so — otherwise a path-less document would look
        fully analysed while a name in it went unresolved.
        """
        holds = tmp_path / "holds"
        holds.mkdir()
        (holds / "glib.vera").write_text(self.LIB, encoding="utf-8")

        for uri in self.PATHLESS:
            a = self._analyze_from(holds, uri)
            codes = [d.error_code for d in a.diagnostics]
            assert "E230" in codes, (uri, codes)


class TestRelativePathDocument:
    """A relative path is a REAL location, and keeps its imports (#1282).

    The path-less isolation rule keyed on "the parent is `.`", which is
    true of `untitled:Untitled-1` AND of `entry.vera` — a real file
    whose directory happens to be the process CWD.  So a genuine
    relative-path document silently lost every import.
    """

    LIB = (
        "module glib;\n"
        "\n"
        "public forall<T> fn pick(@T, @T -> @T)\n"
        "  requires(true)\n  ensures(true)\n  effects(pure)\n"
        "{\n  @T.1\n}\n"
    )
    SRC = (
        "import glib;\n"
        "\n"
        "public fn main(@Nat, @Nat -> @Nat)\n"
        "  requires(true)\n  ensures(true)\n  effects(pure)\n"
        "{\n  glib::pick(@Nat.1, @Nat.0)\n}\n"
    )

    def test_a_relative_path_resolves_its_siblings(
        self, tmp_path: pathlib.Path,
    ) -> None:
        (tmp_path / "glib.vera").write_text(self.LIB, encoding="utf-8")
        (tmp_path / "entry.vera").write_text(self.SRC, encoding="utf-8")
        original = os.getcwd()
        os.chdir(tmp_path)
        try:
            result = VerificationSession().verify_source(
                self.SRC, file="entry.vera",
            )
        finally:
            os.chdir(original)
        foreign = sorted({
            ob.file for ob in result.obligations
            if ob.file is not None and "glib" in ob.file
        })
        assert foreign, [ob.file for ob in result.obligations]

    def test_the_absolute_spelling_agrees_with_it(
        self, tmp_path: pathlib.Path,
    ) -> None:
        """Same document, two spellings, same module namespace."""
        (tmp_path / "glib.vera").write_text(self.LIB, encoding="utf-8")
        entry = tmp_path / "entry.vera"
        entry.write_text(self.SRC, encoding="utf-8")
        original = os.getcwd()
        os.chdir(tmp_path)
        try:
            rel = VerificationSession().verify_source(
                self.SRC, file="entry.vera",
            )
        finally:
            os.chdir(original)
        abs_ = VerificationSession().verify_source(self.SRC, file=str(entry))
        assert len(rel.obligations) == len(abs_.obligations), (
            len(rel.obligations), len(abs_.obligations))

    #: (label, `file` spelling relative to the CWD, does it exist on disk,
    #: must the resolver root at a directory).  The four-way discrimination
    #: `(parent != "." or path.is_file()) and parent.is_dir()` makes, one
    #: row per branch it can take.
    ROOTING_TABLE = (
        ("absolute_on_disk", "<abs>", True, True),
        ("relative_on_disk", "entry.vera", True, True),
        ("relative_absent", "entry.vera", False, False),
        ("untitled_buffer", "untitled:Untitled-1", False, False),
        ("phantom_vfs_root", "vscode-vfs:/host/a.vera", False, False),
        ("degenerate_file_scheme", "", False, False),
    )

    @pytest.mark.parametrize(
        ("label", "spelling", "on_disk", "roots"),
        ROOTING_TABLE, ids=[r[0] for r in ROOTING_TABLE],
    )
    def test_the_resolver_roots_only_at_a_real_directory(
        self, tmp_path: pathlib.Path, label: str, spelling: str,
        on_disk: bool, roots: bool,
    ) -> None:
        """One table over the guard's four branches (PR #1283 review).

        The `path.is_file()` disjunct exists because keying on the parent
        alone took the siblings away from a genuine relative document — a
        regression caught by review rather than by a test, on the didChange
        path.  `relative_absent` is the row that distinguishes the two: same
        `.` parent as a real relative document, no file behind it.

        The degradation is asserted as a decision, not left implicit: where
        the resolver does not root, `resolver_errors` stays empty, so E011 /
        E012 / E013 are never produced and the module-not-found story comes
        from E230 alone.
        """
        (tmp_path / "glib.vera").write_text(self.LIB, encoding="utf-8")
        if on_disk:
            (tmp_path / "entry.vera").write_text(self.SRC, encoding="utf-8")
        file = (
            str(tmp_path / "entry.vera") if spelling == "<abs>" else spelling
        )
        original = os.getcwd()
        os.chdir(tmp_path)
        try:
            result = VerificationSession().verify_source(self.SRC, file=file)
        finally:
            os.chdir(original)

        reached = any(
            ob.file is not None and "glib" in ob.file
            for ob in result.obligations
        )
        assert reached is roots, (label, [ob.file for ob in result.obligations])
        codes = [d.error_code for d in result.check_diagnostics]
        if roots:
            assert "E230" not in codes, (label, codes)
        else:
            # E230 (the import check) and NOT a resolver diagnostic.
            assert "E230" in codes, (label, codes)
            assert not ({"E011", "E012", "E013"} & set(codes)), (label, codes)


class TestModuleAwareDiagnosticsReachTheEditor:
    """The module-aware check's errors must be published (#1282).

    `analyze` type-checked module-BLIND and then called `verify_source`,
    which type-checks module-AWARE.  Only the second saw resolver errors
    and module-typed errors, and it returned them as `check_diagnostics`
    — which `analyze` discarded.  So a real type error in a cross-module
    call produced a document with a warning, no obligations, and no sign
    that anything had failed.  Since #1513 the first check is
    module-aware too (an unresolved call is an error, so a blind one
    would refuse every imported call); these cells hold either design to
    publishing the module-aware errors.
    """

    HDR = "  requires(true)\n  ensures(true)\n  effects(pure)\n"
    LIB = (
        "module glib;\n\npublic fn takes_int(@Int -> @Int)\n"
        "  requires(true)\n  ensures(true)\n  effects(pure)\n"
        "{ @Int.0 }\n"
    )

    def _codes(self, tmp_path: pathlib.Path, lib: str | None,
               src: str) -> list[str | None]:
        if lib is not None:
            (tmp_path / "glib.vera").write_text(lib, encoding="utf-8")
        entry = tmp_path / "entry.vera"
        entry.write_text(src, encoding="utf-8")
        a = analyze(VerificationSession(), entry.as_uri(), src)
        return [d.code for d in to_lsp_diagnostics(a)]

    def test_a_module_typed_error_is_published(
        self, tmp_path: pathlib.Path,
    ) -> None:
        codes = self._codes(
            tmp_path, self.LIB,
            f'import glib;\n\npublic fn main(@Unit -> @Int)\n{self.HDR}'
            '{ glib::takes_int("nope") }\n',
        )
        assert "E202" in codes, codes

    def test_a_missing_module_is_published(
        self, tmp_path: pathlib.Path,
    ) -> None:
        codes = self._codes(
            tmp_path, None,
            f'import nosuch;\n\npublic fn main(@Unit -> @Int)\n{self.HDR}'
            '{ nosuch::f(1) }\n',
        )
        assert "E012" in codes, codes

    def test_a_clean_document_gains_no_duplicates(
        self, tmp_path: pathlib.Path,
    ) -> None:
        """Appending must not double-report what was already published.

        `verify_source`'s check re-derives the diagnostics `analyze`'s
        own check produced, so a blind append shows each twice.
        """
        codes = self._codes(
            tmp_path, self.LIB,
            f'import glib;\n\npublic fn main(@Unit -> @Int)\n{self.HDR}'
            '{ glib::takes_int(1) }\n',
        )
        assert len(codes) == len(set(codes)), codes

    def test_a_missing_module_reports_each_diagnostic_once(
        self, tmp_path: pathlib.Path,
    ) -> None:
        """The overlap case: E230 is on BOTH sides, E012 on one."""
        codes = self._codes(
            tmp_path, None,
            f'import nosuch;\n\npublic fn main(@Unit -> @Int)\n{self.HDR}'
            '{ nosuch::f(1) }\n',
        )
        assert codes.count("E230") == 1, codes


class TestHover:
    def test_hover_reports_smallest_enclosing_expression_type(self) -> None:
        a = _analyze(FEATURE_SRC)
        # line 6 (0-based 5), inside `@Nat.0` of the subtraction.
        h = hover_at(a, lsp.Position(line=5, character=14))
        assert h is not None
        assert "Nat" in h.contents.value

    def test_hover_off_any_expression_is_none(self) -> None:
        a = _analyze(FEATURE_SRC)
        # Line 4 (`  effects(pure)`) records no expression types.
        assert hover_at(a, lsp.Position(line=3, character=4)) is None

    def test_hover_on_parse_error_document_is_none(self) -> None:
        a = _analyze("public fn broken(")
        assert hover_at(a, lsp.Position(line=0, character=2)) is None


class TestDefinition:
    def test_slot_zero_jumps_to_most_recent_parameter(self) -> None:
        a = _analyze(FEATURE_SRC)
        # @Nat.0 in the requires clause (line 2, 0-based 1).
        loc = definition_at(a, lsp.Position(line=1, character=13))
        assert loc is not None
        assert loc.range.start.line == 0
        # De Bruijn: @Nat.0 = the SECOND parameter (most recent),
        # which starts after "public fn dec(@Nat, " — not the first.
        assert loc.range.start.character > len("public fn dec(")

    def test_let_bound_index_has_no_signature_definition(self) -> None:
        _analyze(FEATURE_SRC)
        # On line 6 the let pushes a third @Nat; an @Nat.2 reference
        # would name a parameter, but @Nat indices beyond the param
        # count (e.g. a hypothetical @Nat.5) resolve nowhere.  Use the
        # hole line's bindings to pick an index >= param count via a
        # crafted source instead:
        src = (
            "public fn g(@Int -> @Int)\n"
            "  requires(true) ensures(true) effects(pure)\n"
            "{\n"
            "  let @Int = @Int.0 + 1;\n"
            "  @Int.0 + @Int.1\n"
            "}\n"
        )
        b = analyze(VerificationSession(), "file:///g.vera", src)
        # @Int.0 on line 5 binds to the LET (index 0 = most recent =
        # the let binding, beyond the single parameter's table entry
        # only when index >= len(positions) — here positions has 1
        # entry so @Int.1 (the param) resolves, @Int.0 (the let) does
        # not... slot_table maps params only: @Int.0 -> positions[0]
        # exists (the param is the only table entry, slot-0-first
        # AFTER the let shifts indices at runtime).  Signature-level
        # resolution is approximate for body references by design;
        # this test pins the documented behaviour for an
        # out-of-range index:
        loc = definition_at(b, lsp.Position(line=4, character=12))
        # @Int.1 with one param: positions has len 1, index 1 >= 1 →
        # None (binds through the let-shifted environment).
        assert loc is None

    def test_position_not_on_slot_is_none(self) -> None:
        a = _analyze(FEATURE_SRC)
        assert definition_at(a, lsp.Position(line=4, character=0)) is None

    def test_slot_in_where_block_resolves_to_inner_params(self) -> None:
        """A slot inside a `where` function names the INNER function's
        parameters — the innermost-enclosing-fn rule, not the first
        top-level match."""
        src = (
            "public fn outer(@Int -> @Int)\n"
            "  requires(true) ensures(true) effects(pure)\n"
            "{\n"
            "  helper(@Int.0)\n"
            "}\n"
            "where {\n"
            "  fn helper(@Int -> @Int)\n"
            "    requires(true) ensures(true) effects(pure)\n"
            "  {\n"
            "    @Int.0 + 1\n"
            "  }\n"
            "}\n"
        )
        a = analyze(VerificationSession(), "file:///w.vera", src)
        # @Int.0 inside helper's body (line 10, 0-based 9).
        loc = definition_at(a, lsp.Position(line=9, character=6))
        assert loc is not None
        # Must land on helper's signature (line 7, 0-based 6) — not
        # outer's (line 0).
        assert loc.range.start.line == 6

    def test_parameterised_slot_resolves_to_its_parameter(self) -> None:
        """Go-to-definition works on a PARAMETERISED slot reference (#1208).

        The slot table is keyed by the rendered name (``Option<Int>``); the
        lookup used to be by the reference's bare HEAD (``Option``), so every
        `@T<Args>.n` missed the table and go-to-definition silently returned
        nothing — the whole class of container-typed parameters.  Keyed with
        :func:`vera.naming.slot_ref_key`, the reference renders the way the
        binding did.

        Two parameters of the SAME rendered name pin which one was reached:
        `@Option<Int>.0` is De Bruijn most-recent, so it must land on
        parameter 2, not parameter 1.
        """
        src = (
            "public fn pick(@Option<Int>, @Option<Int> -> @Int)\n"
            "  requires(true) ensures(true) effects(pure)\n"
            "{\n"
            "  match @Option<Int>.0 {\n"
            "    Some(@Int) -> @Int.0,\n"
            "    None -> 0\n"
            "  }\n"
            "}\n"
        )
        a = analyze(VerificationSession(), "file:///p.vera", src)
        # `@Option<Int>.0` on line 4 (0-based 3), inside the match scrutinee.
        loc = definition_at(a, lsp.Position(line=3, character=12))
        assert loc is not None, (
            "a parameterised slot reference must resolve to its parameter"
        )
        assert loc.range.start.line == 0
        # Parameter 2, not parameter 1: the second `@Option<Int>` starts past
        # `public fn pick(@Option<Int>, `.
        assert loc.range.start.character > len(
            "public fn pick(@Option<Int>, ") - 2

    def test_parameterised_slot_alias_spelling_resolves(self) -> None:
        """The reference may be spelled through an ALIAS and still resolve.

        `@Option<Cnt>` (parameter) and `@Option<Int>` (reference) render to
        the one name `Option<Int>` — THE renderer resolves type ARGUMENTS —
        so go-to-definition must cross the spelling, exactly as the checker's
        own binding lookup does.  A syntactic key would see two different
        names and return nothing.
        """
        src = (
            "type Cnt = Int;\n"
            "\n"
            "public fn f(@Option<Cnt> -> @Int)\n"
            "  requires(true) ensures(true) effects(pure)\n"
            "{\n"
            "  match @Option<Int>.0 {\n"
            "    Some(@Int) -> @Int.0,\n"
            "    None -> 0\n"
            "  }\n"
            "}\n"
        )
        a = analyze(VerificationSession(), "file:///alias.vera", src)
        # `@Option<Int>.0` on line 6 (0-based 5).
        loc = definition_at(a, lsp.Position(line=5, character=12))
        assert loc is not None, (
            "an alias-spelled parameter must be reachable from a "
            "canonically-spelled reference"
        )
        assert loc.range.start.line == 2  # the signature, line 3 (0-based 2)

    def test_forall_var_shadowing_an_alias_lands_on_the_right_param(
        self,
    ) -> None:
        """The jump is computed in the FUNCTION's scope, not the module's.

        `T` is a module alias AND `g`'s own type parameter; the type
        parameter shadows the alias, so the checker binds `Option<Int>`
        (parameter 1) and `Option<T>` (parameter 2) as two stacks.  Resolved
        against the bare module environment they merge into one, and
        `@Option<Int>.0` — De Bruijn most-recent of a two-entry stack —
        lands on parameter 2.  Wrong parameter, no error: the function's own
        type parameters have to be in the environment the table is built
        against.
        """
        src = (
            "type T = Int;\n"
            "\n"
            "public forall<T> fn g(@Option<Int>, @Option<T> -> @Int)\n"
            "  requires(true) ensures(true) effects(pure)\n"
            "{\n"
            "  match @Option<Int>.0 {\n"
            "    Some(@Int) -> @Int.0,\n"
            "    None -> 0 - 1\n"
            "  }\n"
            "}\n"
        )
        a = analyze(VerificationSession(), "file:///shadow.vera", src)
        # `@Option<Int>.0` on line 6 (0-based 5).
        loc = definition_at(a, lsp.Position(line=5, character=12))
        assert loc is not None
        sig = "public forall<T> fn g("
        assert loc.range.start.line == 2
        assert loc.range.start.character == len(sig) + 1, (
            "must land on parameter 1 (@Option<Int>); parameter 2 means the "
            "forall shadow was invisible and the two stacks merged"
        )

    def test_where_helper_inherits_the_parents_forall_shadow(self) -> None:
        """A helper INSIDE a generic parent is narrowed by the parent's vars.

        `fn_scopes` accumulates rather than replaces — the checker saves and
        restores ONE type-parameter map, so a `where` helper sees its parent's
        `forall<T>` as well as its own.  With `type T = Int` also in scope, a
        helper rendered against the bare module environment merges its two
        `@Option` parameters into one stack and go-to-definition lands on
        parameter 2 where the checker resolves parameter 1.

        The CLI side of this shape is pinned
        (`test_where_helper_inherits_the_parents_forall_vars`); this is its
        LSP twin, added because dropping the accumulation in
        `definition_at` survived the LSP suite while failing the CLI one
        (#1208 review, M9) — one narrowing, two surfaces, and only one of
        them was watching.
        """
        src = (
            "type T = Int;\n"
            "\n"
            "public forall<T> fn outer(@Option<Int>, @Option<T> -> @Int)\n"
            "  requires(true) ensures(true) effects(pure)\n"
            "{\n"
            "  helper(@Option<Int>.0, @Option<T>.0)\n"
            "}\n"
            "where {\n"
            "  fn helper(@Option<Int>, @Option<T> -> @Int)\n"
            "    requires(true) ensures(true) effects(pure)\n"
            "  {\n"
            "    match @Option<Int>.0 {\n"
            "      Some(@Int) -> @Int.0,\n"
            "      None -> 0 - 1\n"
            "    }\n"
            "  }\n"
            "}\n"
        )
        a = analyze(VerificationSession(), "file:///where_shadow.vera", src)
        # `@Option<Int>.0` inside the HELPER's body, line 12 (0-based 11).
        loc = definition_at(a, lsp.Position(line=11, character=14))
        assert loc is not None, (
            "a helper's own parameter must be reachable from its body"
        )
        assert loc.range.start.line == 8, (
            "must land on the helper's signature (line 9), not the parent's"
        )
        sig = "  fn helper("
        assert loc.range.start.character == len(sig) + 1, (
            "must land on the helper's parameter 1 (@Option<Int>); parameter "
            "2 means the parent's forall shadow did not reach the helper and "
            "its two stacks merged"
        )


class TestHoleCompletion:
    def test_completion_inside_hole_lists_bindings(self) -> None:
        a = _analyze(FEATURE_SRC)
        c = completion_at(a, lsp.Position(line=6, character=2))
        assert c is not None
        labels = [i.label for i in c.items]
        assert labels[0] == "@Nat.0"
        assert len(labels) == 3  # two params + the let binding
        assert all(i.detail == "Nat" for i in c.items)

    def test_completion_immediately_after_hole(self) -> None:
        a = _analyze(FEATURE_SRC)
        c = completion_at(a, lsp.Position(line=6, character=3))
        assert c is not None and c.items

    def test_completion_away_from_hole_is_none(self) -> None:
        a = _analyze(FEATURE_SRC)
        assert completion_at(a, lsp.Position(line=0, character=0)) is None


# =====================================================================
# Phase E — vera/speculativeEdit proof delta
# =====================================================================

from vera.lsp.extensions import proof_delta, speculative_edit  # noqa: E402

SPEC_URI = "file:///s.vera"

SPEC_BASE = (
    "public fn f(@Nat -> @Nat)\n"
    "  requires(@Nat.0 >= 1)\n"
    "  ensures(true)\n"
    "  effects(pure)\n"
    "{\n"
    "  @Nat.0 - 1\n"
    "}\n"
)


class TestSpeculativeEdit:
    def _baseline(self) -> tuple[VerificationSession, list[object]]:
        """A baseline built the way the SERVER builds one.

        `vera/speculativeEdit` diffs against `server.analyses[uri]`,
        which `analyze` produced — so the baseline is keyed on whatever
        `analyze` passed as `file=`.  Building it here with a different
        call, and a different `file=`, made both sides of the delta
        agree with each other and neither agree with production: with
        `analyze` on the path and `speculative_edit` on the raw URI, an
        identical-text edit reported `unchanged: 0` and every obligation
        `removed`, and this suite was green throughout (#1246 review).
        Going through `analyze` is what makes these tests a guard.
        """
        session = VerificationSession()
        analysis = analyze(session, SPEC_URI, SPEC_BASE)
        assert not [d for d in analysis.diagnostics
                    if d.severity == "error"], analysis.diagnostics
        assert analysis.obligations
        return session, analysis.obligations

    def test_identical_text_reports_all_unchanged(self) -> None:
        session, baseline = self._baseline()
        out = speculative_edit(
            session, baseline, SPEC_URI, SPEC_BASE,
        )
        assert out["ok"] is True
        assert out["proof_delta"]["unchanged"] == len(baseline)
        assert out["proof_delta"]["newly_undischarged"] == []
        assert out["proof_delta"]["newly_discharged"] == []
        assert out["diagnostics"] == 0

    def test_breaking_edit_reports_newly_undischarged(self) -> None:
        """Weakening the precondition makes the @Nat subtraction
        violated — the keeps/drops signal the #222 design notes call
        the one thing no generic language server can produce."""
        session, baseline = self._baseline()
        broken = SPEC_BASE.replace(
            "requires(@Nat.0 >= 1)", "requires(true)",
        )
        out = speculative_edit(
            session, baseline, SPEC_URI, broken,
        )
        und = out["proof_delta"]["newly_undischarged"]
        assert any(
            i["kind"] == "nat_sub" and i["status_after"] == "violated"
            for i in und
        )
        # The edit must NOT have been committed anywhere — the session
        # still replays the ORIGINAL source fully from cache.
        # Driven with the PATH, as every production caller is — the
        # discharge cache is keyed on the obligations' `file`, so a
        # replay probe spelling the document differently from the
        # baseline measures the spelling rather than the cache.
        again = session.verify_source(SPEC_BASE, file=uri_to_path(SPEC_URI))
        assert again.ok
        assert session.last_run_stats.replayed_fns >= 1

    def test_strengthening_edit_reports_newly_discharged(self) -> None:
        """The reverse direction: starting from the weak (violated)
        state, the speculative strong contract discharges the
        subtraction obligation."""
        weak = SPEC_BASE.replace("requires(@Nat.0 >= 1)", "requires(true)")
        session = VerificationSession()
        # Through `analyze`, as the server does: a baseline built by a
        # second `verify_source` call spelling the document differently
        # from the speculative side shares no obligation identities, so
        # everything reads as newly discharged and the assertion passes
        # whatever the delta actually says (PR #1282 review).
        baseline = analyze(session, SPEC_URI, weak).obligations
        assert baseline, "no baseline obligations to diff against"
        out = speculative_edit(
            session, baseline, SPEC_URI, SPEC_BASE,
        )
        dis = out["proof_delta"]["newly_discharged"]
        assert any(i["kind"] == "nat_sub" for i in dis), dis
        # `nat_sub` is the obligation that SURVIVES the edit — same
        # expression, same site, only its provability changes — so it
        # must be re-proved rather than replaced.  A baseline keyed
        # apart from the speculative run reports it as removed, which
        # is what distinguishes the two.  (`requires` legitimately does
        # appear in `removed`: this edit rewrites that contract.)
        removed = out["proof_delta"]["removed"]
        assert not any(i["kind"] == "nat_sub" for i in removed), removed

    def test_parse_error_reports_not_ok(self) -> None:
        session, baseline = self._baseline()
        out = speculative_edit(
            session, baseline, SPEC_URI, "public fn broken(",
        )
        assert out["ok"] is False
        assert out["proof_delta"] is None
        assert out["diagnostics"] >= 1

    def test_type_error_reports_not_ok_with_count(self) -> None:
        session, baseline = self._baseline()
        bad = SPEC_BASE.replace("@Nat.0 - 1", '"not a nat"')
        out = speculative_edit(
            session, baseline, SPEC_URI, bad,
        )
        assert out["ok"] is False
        assert out["proof_delta"] is None
        assert out["diagnostics"] >= 1

    def test_deleted_function_reports_removed(self) -> None:
        session, baseline = self._baseline()
        out = speculative_edit(
            session, baseline, SPEC_URI,
            "public fn g(@Int -> @Int)\n"
            "  requires(true) ensures(true) effects(pure)\n"
            "{ @Int.0 }\n",
        )
        # All of f's obligations disappear; g's trivial contracts are
        # new discharges.
        assert len(out["proof_delta"]["removed"]) == len(baseline)
        assert out["proof_delta"]["newly_discharged"]

    def test_proof_delta_pure_function(self) -> None:
        """proof_delta is a pure set-difference over identity keys."""
        session, baseline = self._baseline()
        delta = proof_delta(baseline, baseline)
        assert delta["unchanged"] == len(baseline)
        assert not delta["removed"]
        delta2 = proof_delta(baseline, [])
        assert len(delta2["removed"]) == len(baseline)
        assert delta2["unchanged"] == 0


# =====================================================================
# Phase F1 — vera/proposeEdit enforced edit workflow
# =====================================================================

import asyncio  # noqa: E402
import concurrent.futures  # noqa: E402
import inspect  # noqa: E402
import threading  # noqa: E402
import types  # noqa: E402

from collections.abc import Awaitable, Callable  # noqa: E402
from typing import Any  # noqa: E402

from pygls.exceptions import (  # noqa: E402
    JsonRpcException,
    JsonRpcInvalidParams,
)

from vera.lsp.server import (  # noqa: E402
    _force_param,
    _param,
    _require_str,
)
from vera.obligations import ProofObligation  # noqa: E402
from vera.lsp.workflows import (  # noqa: E402
    _handled_effect_key,
    add_effect,
    apply_propose_edit,
    effect_row_rewrite,
    full_document_range,
    propose_edit,
    splice_contract,
    strengthen_contract,
    transitive_callers,
)

# Same program, every span shifted one line: parses identically but all
# obligation content keys change, so the delta is removed+rediscovered
# with nothing undischarged — a "clean different text" fixture that
# needs no new Vera semantics.
SHIFTED_BASE = "-- shifted\n" + SPEC_BASE
BROKEN_BASE = SPEC_BASE.replace("requires(@Nat.0 >= 1)", "requires(true)")
URI = "file:///p.vera"


#: What a client advertises to take a version-guarded whole-document
#: edit: the `workspace/applyEdit` request itself, and `documentChanges`
#: -- the only `WorkspaceEdit` form whose text edits name the document
#: VERSION they apply to.
VERSIONED_EDITS = lsp.ClientCapabilities(
    workspace=lsp.WorkspaceClientCapabilities(
        apply_edit=True,
        workspace_edit=lsp.WorkspaceEditClientCapabilities(
            document_changes=True,
        ),
    ),
)

LOCK_HELD = (
    "analysis_lock is held while the server waits on the client: the "
    "real server's next didChange would block on it forever"
)


class _OneThreadLock:
    """``analysis_lock`` for a harness that runs on one thread.

    There, acquiring a lock that is already held can only wait for a
    coroutine suspended in the same thread -- a deadlock -- so this
    raises where the real ``threading.Lock`` would block forever, and a
    workflow holding the lock across its wait fails the test instead of
    hanging it.
    """

    def __init__(self) -> None:
        self._lock = threading.Lock()

    def locked(self) -> bool:
        return self._lock.locked()

    def __enter__(self) -> None:
        if not self._lock.acquire(blocking=False):
            raise AssertionError(LOCK_HELD)

    def __exit__(self, *exc: object) -> None:
        self._lock.release()


def _offset(text: str, position: lsp.Position) -> int:
    """The index into *text* of an LSP *position* (0-based line, UTF-16
    column), clamped as the protocol tells a client to clamp: a line
    past the last is the end of the text, a column past a line's end is
    that end.  Written here rather than borrowed from the code under
    test, so the modelled client applies what it is SENT."""
    lines = text.split("\n")
    if position.line >= len(lines):
        return len(text)
    start = sum(len(line) + 1 for line in lines[: position.line])
    units = 0
    for i, ch in enumerate(lines[position.line]):
        if units >= position.character:
            return start + i
        units += 2 if ord(ch) > 0xFFFF else 1
    return start + len(lines[position.line])


class _EditRequest:
    """One ``workspace/applyEdit`` as the modelled client received it.

    ``future`` is the client's answer, and only the client side of the
    harness settles it: the server can only wait on it.
    """

    def __init__(self, params: lsp.ApplyWorkspaceEditParams) -> None:
        self.params = params
        self.future: concurrent.futures.Future[
            lsp.ApplyWorkspaceEditResult
        ] = concurrent.futures.Future()

    def target(self) -> tuple[str, int | None, lsp.TextEdit]:
        """``(uri, version precondition, edit)`` of the one text edit.

        Reads both ``WorkspaceEdit`` forms, so a server that sends the
        unversioned ``changes`` form is modelled too.  That form names no
        version, and neither does ``documentChanges`` with a ``null``
        one: either way the precondition is ``None``, nothing for the
        client to check.
        """
        edit = self.params.edit
        if edit.document_changes:
            (change,) = edit.document_changes
            assert isinstance(change, lsp.TextDocumentEdit), change
            (text_edit,) = change.edits
            assert isinstance(text_edit, lsp.TextEdit), text_edit
            return (
                change.text_document.uri,
                change.text_document.version,
                text_edit,
            )
        assert edit.changes is not None, edit
        ((uri, (text_edit,)),) = edit.changes.items()
        return uri, None, text_edit

    def answer(self, applied: bool) -> None:
        self.future.set_result(lsp.ApplyWorkspaceEditResult(applied=applied))


class _FakeServer:
    """Structural stand-in for ``VeraLanguageServer``, with the editor on
    the far side of the wire modelled explicitly (#1444).

    **Server side.**  ``store`` / ``session`` / ``analysis_lock`` /
    ``analyses`` / ``analyze_and_publish`` / ``client_capabilities`` are
    the members the workflows touch, and ``did_open`` / ``did_change`` /
    ``did_close`` mirror the real server's three document-sync handlers.
    Those three are the only way anything in this harness moves the
    store, and that is the rule under test: the store describes the
    client's buffer, so only the client's own notifications write it.

    **Client side.**  ``buffers`` is the editor's own state, one
    ``(text, version)`` per open URI.  ``open`` and ``type`` change a
    buffer and notify, as an editor does.  ``workspace_apply_edit``
    receives the server's request and returns a Future that the CLIENT
    settles, according to ``policy``:

    * ``"accept"`` -- a conforming client.  It refuses an edit whose
      version precondition names a version its buffer has moved past;
      otherwise it applies the edit, notifies its own ``didChange`` (the
      echo), and then answers.
    * ``"decline"`` -- answers ``applied: false``; nothing changes.
    * ``"fail"`` -- answers with a JSON-RPC error response.
    * ``"cancel"`` -- the request is cancelled unanswered, as pygls
      cancels every outstanding request at shutdown.
    * ``"broken_pipe"`` -- the request cannot even be sent.
    * ``"manual"`` -- nothing; the test settles each request itself, in
      whatever order the case needs (``request`` waits for one).

    An automatic answer runs as a task, so it arrives after the server
    has suspended on the request, which is where a real answer arrives.
    Each first records whether ``analysis_lock`` is held.  This loop is
    one thread, so a lock held while the client acts can only be held by
    the suspended workflow, and the real server's next ``didChange``
    would block on it forever; ``_OneThreadLock`` turns every such
    acquire into a failure rather than a hang.
    """

    #: How far one client-side change moves a buffer's version.  Not 1:
    #: LSP versions need only increase, and a step of one would let a
    #: server that INVENTS ``version + 1`` guess the client's.
    STEP = 10

    def __init__(self, policy: str = "accept") -> None:
        # Server side.
        self.store = DocumentStore()
        self.session = VerificationSession()
        self.analysis_lock = _OneThreadLock()
        self.analyses: dict[str, Any] = {}
        self.published: list[str] = []
        #: Texts whose analysis raises, as an internal compiler error in
        #: the pipeline would: the handler has written the store by then.
        self.unanalysable: set[str] = set()
        #: URIs whose analysis failed, in publish order: the E699 the real
        #: server publishes in place of an analysis.
        self.failed: list[str] = []
        # Client side.
        self.client_capabilities = VERSIONED_EDITS
        self.policy = policy
        self.buffers: dict[str, tuple[str, int]] = {}
        self.disk: dict[str, str] = {}
        self.requests: list[_EditRequest] = []
        self.client_tasks: list[asyncio.Task[None]] = []
        self.lock_held_when_asked: list[bool] = []
        self._arrivals: list[asyncio.Future[None]] = []
        #: The real server's bound on the wait; a cell that models a
        #: client which never answers sets it to 0.
        self.apply_edit_timeout_s = 60.0

    # -- the server's three document-sync handlers, as the real ones --

    def did_open(self, uri: str, text: str, version: int) -> None:
        self.store.open(uri, text, version)
        self.analyze_and_publish(uri, text)

    def did_change(self, uri: str, text: str, version: int) -> None:
        doc = self.store.change(uri, text, version)
        self.analyze_and_publish(doc.uri, doc.text)

    def did_close(self, uri: str) -> None:
        self.store.close(uri)
        self.analyses.pop(uri, None)
        self.published.append(uri)

    def analyze_and_publish(self, uri: str, text: str) -> None:
        with self.analysis_lock:
            if text in self.unanalysable:
                # As the real server: no entry for a text the store has
                # left, and the failure published in its place.
                self.analyses.pop(uri, None)
                self.failed.append(uri)
            else:
                self.analyses[uri] = analyze(self.session, uri, text)
        self.published.append(uri)

    def current_analysis(self, uri: str) -> Any:
        from vera.lsp.features import current_analysis

        return current_analysis(self.store.get(uri), self.analyses.get(uri))

    # -- the editor --

    def open(self, uri: str, text: str, version: int = 1) -> None:
        """The editor opens *uri*: its buffer, then its ``didOpen``."""
        self.buffers[uri] = (text, version)
        self.did_open(uri, text, version)

    def type(self, uri: str, text: str) -> None:
        """The buffer becomes *text* -- typing, or an edit being applied
        -- and the client notifies it at its next version."""
        _, version = self.buffers[uri]
        self.buffers[uri] = (text, version + self.STEP)
        self.did_change(uri, text, version + self.STEP)

    def apply(self, request: _EditRequest) -> bool:
        """Apply *request* as a conforming client does; True if applied.

        The version check is the client's half of the precondition: a
        ``TextDocumentEdit`` naming a version the buffer has moved past
        is refused whole.  Otherwise the edit's range is replaced in the
        buffer AS IT NOW IS -- so a range computed from an older text
        lands where that range now falls, as it would in an editor --
        and the result is the client's own change, notified the way
        every change is.  A document the editor does not have open is
        written to disk, and nothing is notified.
        """
        uri, version, edit = request.target()
        if uri not in self.buffers:
            self.disk[uri] = edit.new_text
            return True
        text, current = self.buffers[uri]
        if version is not None and version != current:
            return False
        start = _offset(text, edit.range.start)
        end = _offset(text, edit.range.end)
        self.type(uri, text[:start] + edit.new_text + text[end:])
        return True

    def workspace_apply_edit(
        self, params: lsp.ApplyWorkspaceEditParams,
    ) -> concurrent.futures.Future[lsp.ApplyWorkspaceEditResult]:
        if self.policy == "broken_pipe":
            raise BrokenPipeError("the client has gone away")
        request = _EditRequest(params)
        self.requests.append(request)
        for arrival in self._arrivals:
            if not arrival.done():
                arrival.set_result(None)
        self._arrivals.clear()
        if self.policy != "manual":
            self.client_tasks.append(
                asyncio.get_running_loop().create_task(
                    self._respond(request),
                ),
            )
        return request.future

    async def _respond(self, request: _EditRequest) -> None:
        """The automatic client, running once the server waits on it."""
        try:
            self.lock_held_when_asked.append(self.analysis_lock.locked())
            assert not self.analysis_lock.locked(), LOCK_HELD
            if self.policy == "accept":
                request.answer(self.apply(request))
            elif self.policy == "decline":
                request.answer(False)
            elif self.policy == "fail":
                request.future.set_exception(
                    JsonRpcException.from_error(
                        lsp.ResponseError(
                            code=-32603,
                            message="the client could not apply the edit",
                        ),
                    ),
                )
            elif self.policy == "cancel":
                request.future.cancel()
            elif self.policy == "silent":
                pass  # never answers: a lost write, or a client that hung
            else:
                raise AssertionError(f"unknown client policy {self.policy!r}")
        except Exception as exc:
            # Settle first, so the server is not left waiting on an
            # answer that will never come; then fail the test with it.
            if not request.future.done():
                request.future.set_exception(exc)
            raise

    async def request(
        self, workflow: asyncio.Future[Any], n: int = 0,
    ) -> _EditRequest:
        """The *n*-th ``workspace/applyEdit`` the server sent, waiting for
        it if need be -- and failing, not hanging, if *workflow* finishes
        without sending it."""
        while len(self.requests) <= n:
            arrival: asyncio.Future[None]
            arrival = asyncio.get_running_loop().create_future()
            self._arrivals.append(arrival)
            await asyncio.wait(
                {arrival, workflow}, return_when=asyncio.FIRST_COMPLETED,
            )
            if len(self.requests) <= n and workflow.done():
                raise AssertionError(
                    f"the workflow finished without sending request {n}: "
                    f"{workflow.result()!r}",
                )
        return self.requests[n]


async def _awaited(value: Any) -> Any:
    """*value*, awaited if it is awaitable.

    Lets one cell drive a coroutine workflow and a synchronous one
    alike, so a workflow that stops waiting for the client fails the
    cell on what it DID to the server's state rather than on its return
    type.  (That the workflows ARE coroutines is pinned on its own, by
    ``TestProposeEditWiring.test_edit_workflows_wait_as_coroutines``.)
    """
    return await value if inspect.isawaitable(value) else value


#: Failure detector for the fake-client cells, never an ordering device
#: (the fake's counterpart to ``WIRE_TIMEOUT_S``): every step is ordered by
#: an await, and a working workflow settles in a small fraction of this.
#: It exists so that a wait nothing will ever settle -- the failure the
#: server's own bound on the wait prevents -- fails the cell instead of
#: hanging the suite, which CI runs with no per-test timeout.
SETTLE_TIMEOUT_S = 120


def _settle(server: _FakeServer, script: Callable[[], Any]) -> Any:
    """Run *script* to completion on a fresh event loop; return its value.

    *script* is a workflow call (``lambda: apply_propose_edit(...)``) or
    an async test script.  Every task the modelled client started is
    awaited afterwards, so an assertion raised on the client's side of
    the wire fails the test instead of vanishing into the loop.  The
    whole of it is bounded by ``SETTLE_TIMEOUT_S``: the fake runs on
    one thread and never blocks (its lock raises instead), so every
    hang it can have is an await, which the bound cancels.
    """
    async def main() -> Any:
        out = await _awaited(script())
        for task in server.client_tasks:
            await task
        return out

    async def bounded() -> Any:
        try:
            return await asyncio.wait_for(main(), SETTLE_TIMEOUT_S)
        except TimeoutError:
            pytest.fail(
                f"the scenario did not settle within {SETTLE_TIMEOUT_S} s: "
                "something awaits an answer nothing will give",
            )

    return asyncio.run(bounded())


class TestProposeEditGate:
    def _baseline(self) -> tuple[VerificationSession, list[object]]:
        session = VerificationSession()
        result = session.verify_source(SPEC_BASE, file=URI)
        assert result.ok
        return session, result.obligations

    def test_clean_edit_applies(self) -> None:
        session, baseline = self._baseline()
        should, response = propose_edit(
            session, baseline, URI, SHIFTED_BASE,
        )
        assert should is True
        assert response["applied"] is True
        assert response["ok"] is True
        assert response["diagnostics"] == 0
        assert response["proof_delta"]["newly_undischarged"] == []

    def test_strengthening_edit_applies(self) -> None:
        """newly_discharged must not block the gate — strengthening
        proofs is the whole point of proposing an edit."""
        session = VerificationSession()
        weak = session.verify_source(BROKEN_BASE, file=URI)
        should, response = propose_edit(
            session, weak.obligations, URI, SPEC_BASE,
        )
        assert should is True
        assert response["proof_delta"]["newly_discharged"]

    def test_breaking_edit_refused(self) -> None:
        session, baseline = self._baseline()
        should, response = propose_edit(
            session, baseline, URI, BROKEN_BASE,
        )
        assert should is False
        assert response["applied"] is False
        und = response["proof_delta"]["newly_undischarged"]
        assert any(i["kind"] == "nat_sub" for i in und)

    def test_error_edit_refused(self) -> None:
        session, baseline = self._baseline()
        bad = SPEC_BASE.replace("@Nat.0 - 1", '"not a nat"')
        should, response = propose_edit(session, baseline, URI, bad)
        assert should is False
        assert response["ok"] is False
        assert response["proof_delta"] is None
        assert response["diagnostics"] >= 1

    def test_force_overrides_proof_gate(self) -> None:
        """force applies the edit but the delta still reports the
        damage — override is loud, not blind."""
        session, baseline = self._baseline()
        should, response = propose_edit(
            session, baseline, URI, BROKEN_BASE, force=True,
        )
        assert should is True
        assert response["applied"] is True
        assert response["proof_delta"]["newly_undischarged"]

    def test_force_overrides_error_gate(self) -> None:
        session, baseline = self._baseline()
        should, response = propose_edit(
            session, baseline, URI, "public fn broken(", force=True,
        )
        assert should is True
        assert response["ok"] is False
        assert response["proof_delta"] is None


class _StubSession:
    """A ``VerificationSession`` stand-in returning a fixed outcome.

    ``speculative_edit`` calls ``verify_source(text, file=...)`` and
    reads exactly three things off the result -- ``ok``, ``obligations``
    and ``diagnostics`` -- so a status transition can be injected
    without a Vera program that actually produces it.  That matters
    here: ``verified -> timeout`` is a solver's whim, not a property of
    any source text, so the transition the gate got wrong is not
    reachable from a fixture at all.  Testing the gate through real
    verification would leave exactly that row untested, which is how it
    survived.
    """

    def __init__(
        self, obligations: list[ProofObligation], ok: bool = True,
    ) -> None:
        self._obligations = obligations
        self._ok = ok

    def verify_source(
        self, text: str, file: str | None = None,
    ) -> types.SimpleNamespace:
        return types.SimpleNamespace(
            ok=self._ok, obligations=self._obligations, diagnostics=[],
        )


#: Every member of ``ObligationStatus``, so a table over transitions
#: is a table over the whole vocabulary rather than a chosen subset.
_STATUSES = (
    "verified", "violated", "tier3", "timeout", "tier3_unguarded",
)


def _ob(
    status: str, line: int = 1, expr: str = "p", fn: str = "f",
    owner: str = "",
) -> ProofObligation:
    """One obligation with fixed identity, varying only in outcome.

    ``content_key`` hashes the identity fields and never the status, so
    two of these with different statuses are the SAME obligation before
    and after an edit -- which is what makes a transition a transition
    rather than a removal plus a discovery.

    ``line`` is a parameter because the span IS one of those identity
    fields: moving it makes the very same obligation arrive under a new
    key, which is the shape a one-line insertion above it produces and
    the case ``_relocation_key`` exists to pair back up.
    """
    return ProofObligation(
        fn_name=fn, kind="ensures", expr_text=expr, status=status,
        line=line, column=1, file="/p.vera", owner=owner,
    )


class TestProofPreservationAcrossTheStatusVocabulary:
    """A proof that is lost needs `force`, whatever it is lost TO.

    The gate read `newly_undischarged` and the error count.  But
    `proof_delta` sorts by the AFTER status, and routes anything ending
    in `timeout` to its own `timed_out` category -- so an obligation
    that went `verified -> timeout` appeared in neither the list the
    gate consulted nor the diagnostics, and the edit applied.  The
    verifier records a postcondition timeout as a warning with
    `ok=True`, so nothing else caught it either: a previously proved
    obligation silently stopped being proved and `applied` came back
    `True`.

    The categories are a PRESENTATION of the delta.  Their separation
    was never permission to apply, and the gate now asks the question
    directly, over the whole status vocabulary, in one place.
    """

    @pytest.mark.parametrize(
        ("before", "after", "applies"),
        [
            # A proof survives: nothing to refuse.
            ("verified", "verified", True),
            # A proof is LOST.  Every one of these is a regression, and
            # the vocabulary is enumerated so a new status cannot be
            # added later and quietly default to "apply".
            ("verified", "timeout", False),
            ("verified", "tier3", False),
            ("verified", "tier3_unguarded", False),
            ("verified", "violated", False),
            # Already undischarged and unchanged: the current policy,
            # deliberately kept.  The edit did not take anything away.
            ("timeout", "timeout", True),
            ("tier3", "tier3", True),
            ("violated", "violated", True),
            # An obligation that was undischarged and IMPROVED.
            ("timeout", "verified", True),
            ("violated", "verified", True),
        ],
    )
    def test_transition(
        self, before: str, after: str, applies: bool,
    ) -> None:
        session = _StubSession([_ob(after)])
        should, response = propose_edit(
            session, [_ob(before)], URI, "-- text",  # type: ignore[arg-type]
        )
        assert should is applies, (
            f"{before} -> {after}: expected applies={applies}"
        )
        assert response["applied"] is applies
        # Asserted on the LIST, not only on the verdict.  `tier3` and
        # `tier3_unguarded` are refused by `newly_undischarged` too, so
        # a predicate narrowed to `("violated", "timeout")` keeps every
        # verdict above correct and only this line reds (#1461 review).
        lost = before == "verified" != after
        assert len(response["proof_delta"]["proof_regressions"]) == int(lost)

    @pytest.mark.parametrize(
        ("before", "after"),
        [
            ("verified", "timeout"),
            ("verified", "tier3"),
            ("verified", "tier3_unguarded"),
            ("verified", "violated"),
        ],
    )
    def test_force_still_overrides_every_regression(
        self, before: str, after: str,
    ) -> None:
        """`force` is the override for all of them, not just some."""
        session = _StubSession([_ob(after)])
        should, response = propose_edit(
            session, [_ob(before)], URI, "-- text",  # type: ignore[arg-type]
            force=True,
        )
        assert should is True
        assert response["applied"] is True

    def test_a_newly_introduced_timeout_is_not_a_regression(self) -> None:
        """A boundary the rule draws deliberately.

        An obligation the edit CREATES, which then times out, took no
        proof away -- there was nothing there before.  It is reported
        (`timed_out` carries it, with `status_before: None`) but it does
        not need `force`.  Pinned because it is the case adjacent to the
        bug, and the obvious over-correction is to refuse it too.
        """
        session = _StubSession([_ob("timeout")])
        should, response = propose_edit(
            session, [], URI, "-- text",  # type: ignore[arg-type]
        )
        assert should is True
        assert response["proof_delta"]["timed_out"]
        assert response["proof_delta"]["timed_out"][0]["status_before"] is None

    @pytest.mark.parametrize(
        ("status", "applies"),
        [
            # Unknown, not false: falls back to a runtime check, and
            # took no proof away.  Allowed, as before.
            ("timeout", True),
            # Z3 produced a counterexample.  A definite falsehood the
            # edit INTRODUCED — refused, as before.
            ("violated", False),
            # Outside the decidable fragment; a runtime check is
            # emitted.  Refused, as before.
            ("tier3", False),
        ],
    )
    def test_an_obligation_the_edit_introduces(
        self, status: str, applies: bool,
    ) -> None:
        """The half `proof_regressions` deliberately cannot see.

        A brand-new obligation has no `before`, so the preservation
        predicate says nothing about it and `newly_undischarged` is the
        only conjunct that can — which is why both are in the gate and
        neither subsumes the other.  Without this cell the older
        conjunct mutation-survives its own removal: every OTHER row in
        the table has a `before`, so the new predicate covers them all
        and dropping `newly_undischarged` stays green while a newly
        introduced `violated` silently starts applying.

        The asymmetry is the point.  `violated` is a counterexample, an
        error; `timeout` is the solver saying it does not know, a
        warning with a runtime check behind it.  Introducing an unknown
        is not the same act as introducing a falsehood.
        """
        session = _StubSession([_ob(status)])
        should, _ = propose_edit(
            session, [], URI, "-- text",  # type: ignore[arg-type]
        )
        assert should is applies

    def test_the_regression_is_reported_not_merely_refused(self) -> None:
        """The refusal names what was lost, so an agent can act on it."""
        session = _StubSession([_ob("timeout")])
        should, response = propose_edit(
            session, [_ob("verified")], URI, "-- text",  # type: ignore[arg-type]
        )
        assert should is False
        regressed = response["proof_delta"]["proof_regressions"]
        assert len(regressed) == 1
        assert regressed[0]["status_before"] == "verified"
        assert regressed[0]["status_after"] == "timeout"
        assert regressed[0]["fn"] == "f"

    def test_the_presentation_categories_are_unchanged(self) -> None:
        """The fix must not reshuffle what the delta reports.

        `verified -> timeout` still presents as `timed_out`, not as
        `newly_undischarged`: the gate stopped reading the categories,
        which is different from redefining them.
        """
        session = _StubSession([_ob("timeout")])
        _, response = propose_edit(
            session, [_ob("verified")], URI, "-- text",  # type: ignore[arg-type]
        )
        delta = response["proof_delta"]
        assert len(delta["timed_out"]) == 1
        assert delta["newly_undischarged"] == []
        assert delta["newly_discharged"] == []


class TestARelocatedObligationIsStillTheSameObligation:
    """One inserted line must not walk an edit past the gate.

    `content_key` hashes the span, so an obligation that MOVED arrives
    under a new key: it presents as a removal plus a rediscovery, and a
    predicate that only compares same-key obligations has no transition
    to judge.  An edit that inserts a line near the top and costs a
    proof further down the file therefore reported
    `proof_regressions: []` and applied without `force`, while the
    identical injection with no line shift was refused (#1461 review).

    The pairing changes what each entry is reported AGAINST, not which
    list it is in: the four categories still partition the speculative
    stream by the after-status, and a relocated obligation is still a
    removal at its old span plus an entry at its new one.  What it
    gains is the `status_before` of the obligation it paired with,
    which is what lets `proof_regressions` see the loss and lets the
    gate tell a pair that only moved from one that worsened.
    """

    @pytest.mark.parametrize(
        "after", ["timeout", "tier3", "tier3_unguarded", "violated"],
    )
    def test_a_proof_lost_by_an_obligation_that_moved(
        self, after: str,
    ) -> None:
        """The finding, one row per way the proof can be lost."""
        session = _StubSession([_ob(after, line=2)])
        should, response = propose_edit(
            session, [_ob("verified", line=1)],  # type: ignore[arg-type]
            URI, "-- inserted\n",
        )
        assert should is False
        assert response["applied"] is False
        (regressed,) = response["proof_delta"]["proof_regressions"]
        assert regressed["status_before"] == "verified"
        assert regressed["status_after"] == after
        # Both spans, because the agent has to find what it broke and
        # the AFTER line is not where the obligation used to be.
        assert (regressed["line_before"], regressed["line"]) == (1, 2)

    def test_force_still_overrides_a_relocated_regression(self) -> None:
        session = _StubSession([_ob("timeout", line=2)])
        should, response = propose_edit(
            session, [_ob("verified", line=1)],  # type: ignore[arg-type]
            URI, "-- inserted\n", force=True,
        )
        assert should is True
        delta = response["proof_delta"]
        assert len(delta["proof_regressions"]) == 1
        # The PRESENTATION half of the pairing, pinned: `timed_out` is
        # not a gate input, so nothing else in the suite would notice it
        # reporting this entry against `None` -- and then the one list
        # an agent reads to see WHY a timeout appeared would not say the
        # obligation used to be proved (#1461 review G1).  Contrast
        # `test_a_newly_introduced_timeout_is_not_a_regression`, where a
        # genuinely new obligation still reports `None`.
        assert delta["timed_out"][0]["status_before"] == "verified"

    def test_a_harmless_shift_is_not_a_regression(self) -> None:
        """The other half: moving a proof is not losing one."""
        session = _StubSession([_ob("verified", line=2)])
        should, response = propose_edit(
            session, [_ob("verified", line=1)],  # type: ignore[arg-type]
            URI, "-- inserted\n",
        )
        assert should is True
        delta = response["proof_delta"]
        assert delta["proof_regressions"] == []
        # The third `was`-threaded branch, pinned for the same reason as
        # the one in the force cell above (#1461 review G1).
        assert delta["newly_discharged"][0]["status_before"] == "verified"

    def test_a_harmless_shift_of_real_obligations_applies(self) -> None:
        """The same, through the real verifier rather than a stub.

        `SHIFTED_BASE` prepends one comment line, so every obligation in
        the file moves and NONE changes status.  The `removed` assertion
        is what stops this cell being vacuous: the relocation really did
        happen, the pairing really was exercised, and it found nothing
        to refuse.
        """
        session = VerificationSession()
        analysis = analyze(session, SPEC_URI, SPEC_BASE)
        assert analysis.obligations
        should, response = propose_edit(
            session, analysis.obligations, SPEC_URI, SHIFTED_BASE,
        )
        delta = response["proof_delta"]
        assert [r["status_before"] for r in delta["removed"]] == (
            ["verified"] * len(analysis.obligations)
        ), "the shift must present as removals, or the pairing is untested"
        assert delta["proof_regressions"] == []
        assert should is True

    def test_a_harmless_shift_carrying_a_tier3_obligation_applies(
        self,
    ) -> None:
        """`newly_undischarged` is a gate input, so it too must pair.

        `int_overflow` on `@Int.1 * @Int.0` is Tier 3, and a comment
        insertion moves it.  Span-keyed, that reads as a brand-new
        undischarged obligation, so the gate refused a shift that
        changed nothing -- in ANY program carrying a Tier-3 obligation
        (#1461 review, case A2b).  A relocated obligation is not an
        addition.
        """
        src = (
            "public fn m(@Int, @Int -> @Int)\n"
            "  requires(true)\n"
            "  ensures(true)\n"
            "  effects(pure)\n"
            "{\n"
            "  @Int.1 * @Int.0\n"
            "}\n"
        )
        uri = "file:///m.vera"
        session = VerificationSession()
        analysis = analyze(session, uri, src)
        assert [o.status for o in analysis.obligations].count("tier3") == 1, (
            "the cell needs a real Tier-3 obligation to be about anything"
        )
        should, response = propose_edit(
            session, analysis.obligations, uri, "-- shifted\n" + src,
        )
        delta = response["proof_delta"]
        assert len(delta["removed"]) == len(analysis.obligations)
        assert delta["proof_regressions"] == []
        # The Tier-3 obligation is still REPORTED -- the categories are
        # a partition of the speculative stream and dropping it would
        # make the delta unrenderable -- but it is reported against the
        # `before` it paired with, so the gate can see it did not move.
        (still_tier3,) = delta["newly_undischarged"]
        assert still_tier3["status_before"] == still_tier3["status_after"]
        assert should is True

    def test_two_identical_obligations_pair_in_source_order(self) -> None:
        """`_relocation_key` is not unique, so pairing must be stable.

        Two textually identical obligations in one function share a key.
        Both shift by one line and the SECOND loses its proof; the
        positional pairing has to notice that one, and exactly one.
        """
        session = _StubSession([
            _ob("verified", line=4), _ob("timeout", line=8),
        ])
        should, response = propose_edit(
            session,  # type: ignore[arg-type]
            [_ob("verified", line=3), _ob("verified", line=7)],
            URI, "-- inserted\n",
        )
        assert should is False
        (regressed,) = response["proof_delta"]["proof_regressions"]
        assert (regressed["line_before"], regressed["line"]) == (7, 8)

    @pytest.mark.parametrize("relocated", [False, True], ids=["fixed", "moved"])
    @pytest.mark.parametrize(
        ("before", "after", "applies"),
        [
            # Worsening between two undischarged statuses.  No proof is
            # lost, so `proof_regressions` is silent by design and
            # `newly_undischarged` is the conjunct that must speak.
            ("tier3", "violated", False),
            ("tier3", "tier3_unguarded", False),
            ("timeout", "violated", False),
            ("timeout", "tier3", False),
            ("tier3_unguarded", "violated", False),
            # Unchanged: not an addition, nothing taken away.
            ("violated", "violated", True),
            ("tier3", "tier3", True),
        ],
    )
    def test_relocation_is_invisible_to_the_gate(
        self, before: str, after: str, applies: bool, relocated: bool,
    ) -> None:
        """A pair is judged as the same pair at a fixed span would be.

        Dropping every paired entry from `newly_undischarged` would be
        the easy way to fix case A2b, and it would let an edit that
        moved a line do exactly what the identical unmoved edit is
        refused for -- `tier3 -> violated` leaves that list, and
        `proof_regressions` watches proofs, not falsehoods.  So the two
        columns of this table must agree, row for row.
        """
        session = _StubSession([_ob(after, line=2 if relocated else 1)])
        should, response = propose_edit(
            session, [_ob(before, line=1)],  # type: ignore[arg-type]
            URI, "-- edit\n",
        )
        assert should is applies, (
            f"{before} -> {after} "
            f"({'relocated' if relocated else 'same span'})"
        )
        # Never a proof regression: none of these started `verified`.
        assert response["proof_delta"]["proof_regressions"] == []

    @pytest.mark.parametrize("relocated", [False, True], ids=["fixed", "moved"])
    @pytest.mark.parametrize("after", list(_STATUSES))
    @pytest.mark.parametrize("before", list(_STATUSES))
    def test_every_speculative_obligation_lands_in_exactly_one_category(
        self, before: str, after: str, relocated: bool,
    ) -> None:
        """The four categories must PARTITION the speculative stream.

        A consumer renders the delta from them, so an obligation that
        reaches none of them is an obligation the display says went
        away while it is still there.  The first cut of the relocation
        fix dropped same-status pairs out of `newly_undischarged` to
        keep them from reaching the gate, and `violated -> violated`
        then showed a counterexample vanishing because a line moved
        (#1461 review F1).  The exclusion belongs in the gate, which
        reads `status_before` off the entry; the category keeps it.
        """
        delta = proof_delta(
            [_ob(before, line=5)], [_ob(after, line=6 if relocated else 5)],
        )
        landed = (
            delta["unchanged"]
            + len(delta["newly_discharged"])
            + len(delta["timed_out"])
            + len(delta["newly_undischarged"])
        )
        assert landed == 1, f"{before} -> {after}: landed in {landed}"

    def test_a_deleted_proof_is_not_a_regression(self) -> None:
        """The boundary the pairing draws, stated rather than implied.

        An obligation with no counterpart on the new side was DELETED,
        not relocated.  The gate protects proofs, not contracts: a
        removed contract is visible in the edit itself, and nothing
        unproved is left behind.  It is reported -- under `removed`,
        carrying the status it had -- and it does not need `force`.
        """
        session = _StubSession([])
        should, response = propose_edit(
            session, [_ob("verified")], URI, "-- gone\n",  # type: ignore[arg-type]
        )
        assert should is True
        assert response["proof_delta"]["proof_regressions"] == []
        (gone,) = response["proof_delta"]["removed"]
        assert (gone["status_before"], gone["status_after"]) == (
            "verified", None,
        )

    @pytest.mark.parametrize(
        ("replacement", "applies"),
        [
            # Replacing a proof with a counterexample, or with an
            # obligation outside the fragment, is refused -- by
            # `newly_undischarged`, which is what catches an obligation
            # with no `before`.
            ("violated", False),
            ("tier3", False),
            # And the one that is NOT closed, pinned so it is a stated
            # boundary and not a surprise: a replacement that merely
            # times out is a new, unproved obligation, and the policy
            # for those is the same one
            # `test_a_newly_introduced_timeout_is_not_a_regression`
            # already pins -- it took no proof away, so it applies.
            ("timeout", True),
        ],
    )
    def test_a_deletion_followed_by_a_weaker_contract(
        self, replacement: str, applies: bool,
    ) -> None:
        """Delete a proved `ensures`, add a differently-worded one.

        Different text is a different `_relocation_key`, so this is a
        deletion plus an addition and never a pair.  The addition is
        judged as an addition.
        """
        session = _StubSession([_ob(replacement, expr="weaker")])
        should, response = propose_edit(
            session, [_ob("verified")], URI, "-- weaker\n",  # type: ignore[arg-type]
        )
        assert should is applies
        assert response["proof_delta"]["proof_regressions"] == []

    def test_same_named_helpers_under_two_owners_do_not_pair(self) -> None:
        """`owner` is load-bearing HERE even though `content_key` omits it.

        `fn_name` is a `where` helper's bare name, so `h` in `a` and `h`
        in `b` are two functions with one name.  `content_key` can leave
        `owner` out because the span already separates them -- and this
        key drops the span, so the justification does not carry over.
        Without `owner` these two pair against each other, and one
        owner's lost proof is attributed to the other's (#1461 review).
        """
        session = _StubSession([
            _ob("verified", line=9, fn="h", owner="b"),
            _ob("timeout", line=4, fn="h", owner="a"),
        ])
        should, response = propose_edit(
            session,  # type: ignore[arg-type]
            [_ob("verified", line=3, fn="h", owner="a"),
             _ob("verified", line=8, fn="h", owner="b")],
            URI, "-- inserted\n",
        )
        assert should is False
        (regressed,) = response["proof_delta"]["proof_regressions"]
        assert (regressed["line_before"], regressed["line"]) == (3, 4)

    def test_predicates_differing_only_inside_a_literal_do_not_pair(
        self,
    ) -> None:
        """`expr_text` is used verbatim, and this is why.

        `format_expr` has already normalised source spacing by the time
        the text reaches the key, so re-normalising it collapses only
        the whitespace the renderer deliberately KEPT -- inside a string
        literal, where it is part of the value (#1461 review).

        The two spellings swap places, which is what makes the cell
        able to fail: keyed verbatim they pair by TEXT, so
        `"a  b"` goes verified -> timeout and is refused.  Collapsed
        into one group they pair by POSITION instead, every pair looks
        unchanged, and the edit applies with the lost proof unreported.
        """
        wide, thin = 's == "a  b"', 's == "a b"'
        session = _StubSession([
            _ob("verified", line=4, expr=thin),
            _ob("timeout", line=8, expr=wide),
        ])
        should, response = propose_edit(
            session,  # type: ignore[arg-type]
            [_ob("verified", line=3, expr=wide),
             _ob("timeout", line=7, expr=thin)],
            URI, "-- inserted\n",
        )
        assert should is False
        (regressed,) = response["proof_delta"]["proof_regressions"]
        assert (regressed["line_before"], regressed["line"]) == (3, 8)

    def test_an_obligation_that_moved_to_another_function_is_not_paired(
        self,
    ) -> None:
        """The key is not text alone: `fn_name` and `file` are in it.

        A proved obligation deleted from `f` while a same-text one
        appears in `g` is two edits, not one relocation -- pairing them
        would report a regression `g` never had.
        """
        session = _StubSession([_ob("timeout", fn="g")])
        should, response = propose_edit(
            session, [_ob("verified", fn="f")],  # type: ignore[arg-type]
            URI, "-- moved\n",
        )
        assert response["proof_delta"]["proof_regressions"] == []
        assert should is True


#: Text the user types while an edit is pending -- a clean program,
#: distinct from every proposal, so its survival is observable.
TYPED_BASE = "-- typed while the edit was pending\n" + SPEC_BASE
#: A second clean proposal, for two edits in flight at once.
OTHER_BASE = "-- another proposal\n" + SPEC_BASE


def _doc_state(server: _FakeServer) -> tuple[str, int] | None:
    """The server's canonical ``(text, version)`` for ``URI``."""
    doc = server.store.get(URI)
    return None if doc is None else (doc.text, doc.version)


class TestProposeEditWiring:
    """The apply half of ``vera/proposeEdit`` against a modelled client.

    #1444: the server's document state describes the CLIENT'S buffer, so
    it moves only when the client says the buffer moved.  The cells follow
    the issue's test shape -- a declined edit leaves text, version and
    analysis unchanged; an accepted edit converges; a newer ``didChange``
    during a pending application wins; failure or cancellation is not
    reported as applied -- plus the edges each of those has: both orders
    in which an accepting client's answer and its ``didChange`` can
    arrive, two proposals in flight at once, a client that cannot take a
    version-guarded edit, and a document the client never opened.
    """

    def _server(self, policy: str = "accept") -> _FakeServer:
        server = _FakeServer(policy)
        server.open(URI, SPEC_BASE, version=1)
        server.published.clear()
        return server

    def test_the_edit_is_sent_guarded_by_the_verified_version(
        self,
    ) -> None:
        """One request, in the only form that can carry a version: a
        whole-document ``TextDocumentEdit`` naming version 1, the version
        whose text the gate verified the proposal against."""
        server = self._server()
        _settle(server, lambda: apply_propose_edit(server, URI, SHIFTED_BASE))
        assert len(server.requests) == 1
        edit = server.requests[0].params.edit
        assert edit.changes is None, "unversioned `changes` form sent"
        (change,) = edit.document_changes
        assert change.text_document == (
            lsp.OptionalVersionedTextDocumentIdentifier(uri=URI, version=1)
        )
        (text_edit,) = change.edits
        assert text_edit.new_text == SHIFTED_BASE
        # SPEC_BASE ends with a newline: the range ends on the virtual
        # line past the last, column 0.
        assert text_edit.range == lsp.Range(
            start=lsp.Position(line=0, character=0),
            end=lsp.Position(line=SPEC_BASE.count("\n"), character=0),
        )

    def test_gate_refusal_sends_nothing_and_touches_nothing(self) -> None:
        server = self._server()
        before = server.analyses[URI]
        out = _settle(
            server, lambda: apply_propose_edit(server, URI, BROKEN_BASE),
        )
        assert out["applied"] is False
        assert server.requests == []
        assert server.published == []
        assert _doc_state(server) == (SPEC_BASE, 1)
        assert server.analyses[URI] is before
        assert out["client"] is None

    def test_declined_edit_leaves_text_version_and_analysis(self) -> None:
        """The issue's reproduction: a client that declines.  The server
        keeps describing the buffer the client kept."""
        server = self._server("decline")
        before = server.analyses[URI]
        out = _settle(
            server, lambda: apply_propose_edit(server, URI, SHIFTED_BASE),
        )
        assert _doc_state(server) == (SPEC_BASE, 1)
        assert server.analyses[URI] is before
        assert server.published == []
        assert server.buffers[URI] == (SPEC_BASE, 1)
        assert out["applied"] is False
        assert out["client"] == "declined"

    def test_accepted_edit_converges_at_the_clients_version(self) -> None:
        """The client applies the edit and notifies its ``didChange``
        before it answers.  The server's state is the client's: the
        proposal, at version 11 -- the client's number, which a server
        counting ``version + 1`` for itself cannot produce -- analysed
        and published once, by that notification."""
        server = self._server("accept")

        async def script() -> dict[str, Any]:
            out = await _awaited(
                apply_propose_edit(server, URI, SHIFTED_BASE),
            )
            # As the response goes back, not only once the dust settles.
            assert _doc_state(server) == (SHIFTED_BASE, 11)
            return out

        out = _settle(server, script)
        assert server.buffers[URI] == (SHIFTED_BASE, 11)
        assert _doc_state(server) == (SHIFTED_BASE, 11)
        assert server.analyses[URI].text == SHIFTED_BASE
        assert server.published == [URI]
        assert out["applied"] is True
        assert out["client"] == "applied"

    def test_an_answer_ahead_of_its_did_change_waits_for_it(self) -> None:
        """The other order: ``applied: true`` arrives before the client's
        ``didChange``, as it does from a client that debounces change
        notifications.  Until that notification the server has no
        version for the new text and nothing it may publish, so the
        response comes back with the state untouched, and the
        notification then converges it."""
        server = self._server("manual")
        before = server.analyses[URI]

        async def script() -> dict[str, Any]:
            workflow = asyncio.ensure_future(
                _awaited(apply_propose_edit(server, URI, SHIFTED_BASE)),
            )
            request = await server.request(workflow)
            request.answer(True)
            out = await workflow
            assert _doc_state(server) == (SPEC_BASE, 1)
            assert server.analyses[URI] is before
            assert server.published == []
            server.type(URI, SHIFTED_BASE)  # the client's didChange
            return out

        out = _settle(server, script)
        assert _doc_state(server) == (SHIFTED_BASE, 11)
        assert server.analyses[URI].text == SHIFTED_BASE
        assert server.published == [URI]
        assert out["applied"] is True
        assert out["client"] == "applied"

    def test_newer_did_change_during_a_pending_application_wins(
        self,
    ) -> None:
        """The user types while the client has the request in hand.  The
        edit names version 1 and the buffer is at 11, so a conforming
        client refuses it -- and the newer text stands on both sides."""
        server = self._server("manual")

        async def script() -> dict[str, Any]:
            workflow = asyncio.ensure_future(
                _awaited(apply_propose_edit(server, URI, SHIFTED_BASE)),
            )
            request = await server.request(workflow)
            assert not server.analysis_lock.locked(), LOCK_HELD
            server.type(URI, TYPED_BASE)  # didChange, version 11
            request.answer(server.apply(request))
            return await workflow

        out = _settle(server, script)
        assert server.buffers[URI] == (TYPED_BASE, 11)
        assert _doc_state(server) == (TYPED_BASE, 11)
        assert server.analyses[URI].text == TYPED_BASE
        assert out["applied"] is False
        assert out["client"] == "declined"

    def test_newer_did_change_after_an_accepted_edit_is_not_overwritten(
        self,
    ) -> None:
        """The client applies the edit (its ``didChange`` at 11), the
        user types on (21), and only then does ``applied: true`` arrive.
        The answer is news about a state the server has already moved
        past, so it must not move the server back to the proposal."""
        server = self._server("manual")

        async def script() -> dict[str, Any]:
            workflow = asyncio.ensure_future(
                _awaited(apply_propose_edit(server, URI, SHIFTED_BASE)),
            )
            request = await server.request(workflow)
            assert server.apply(request)  # didChange, version 11
            server.type(URI, TYPED_BASE)  # didChange, version 21
            request.answer(True)
            return await workflow

        out = _settle(server, script)
        assert _doc_state(server) == (TYPED_BASE, 21)
        assert server.analyses[URI].text == TYPED_BASE
        assert server.published == [URI, URI]
        assert out["applied"] is True
        assert out["client"] == "applied"

    def test_two_proposals_in_flight_only_the_first_lands(self) -> None:
        """Both gates verify against version 1, so both requests name
        version 1.  Whichever the client applies first moves the buffer
        on, and the precondition makes it refuse the other rather than
        overwrite the first with a text computed without it."""
        server = self._server("manual")

        async def script() -> tuple[dict[str, Any], dict[str, Any]]:
            first = asyncio.ensure_future(
                _awaited(apply_propose_edit(server, URI, SHIFTED_BASE)),
            )
            first_request = await server.request(first, 0)
            second = asyncio.ensure_future(
                _awaited(apply_propose_edit(server, URI, OTHER_BASE)),
            )
            second_request = await server.request(second, 1)
            for request in (first_request, second_request):
                assert request.target()[1] == 1
            first_request.answer(server.apply(first_request))
            second_request.answer(server.apply(second_request))
            return await first, await second

        first, second = _settle(server, script)
        assert (first["applied"], first["client"]) == (True, "applied")
        assert (second["applied"], second["client"]) == (False, "declined")
        assert _doc_state(server) == (SHIFTED_BASE, 11)
        assert server.buffers[URI] == (SHIFTED_BASE, 11)

    def test_an_error_answer_is_not_reported_as_applied(self) -> None:
        server = self._server("fail")
        before = server.analyses[URI]
        out = _settle(
            server, lambda: apply_propose_edit(server, URI, SHIFTED_BASE),
        )
        assert _doc_state(server) == (SPEC_BASE, 1)
        assert server.analyses[URI] is before
        assert server.published == []
        assert out["applied"] is False
        assert out["client"] == "failed"

    def test_a_request_that_cannot_be_sent_is_not_reported_as_applied(
        self,
    ) -> None:
        server = self._server("broken_pipe")
        before = server.analyses[URI]
        out = _settle(
            server, lambda: apply_propose_edit(server, URI, SHIFTED_BASE),
        )
        assert _doc_state(server) == (SPEC_BASE, 1)
        assert server.analyses[URI] is before
        assert server.published == []
        assert out["applied"] is False
        assert out["client"] == "failed"

    def test_a_cancelled_request_is_not_reported_as_applied(self) -> None:
        """The request is cancelled with no answer -- pygls cancels every
        outstanding request at shutdown.  Nothing is known about the
        client's buffer, so nothing is claimed about it: ``applied`` is
        ``null``, neither true nor false."""
        server = self._server("cancel")
        before = server.analyses[URI]
        out = _settle(
            server, lambda: apply_propose_edit(server, URI, SHIFTED_BASE),
        )
        assert _doc_state(server) == (SPEC_BASE, 1)
        assert server.analyses[URI] is before
        assert server.published == []
        assert out["applied"] is None
        assert out["client"] == "cancelled"
        assert "re-read the document" in out["client_reason"]

    def test_cancelling_the_workflow_leaves_the_request_answerable(
        self,
    ) -> None:
        """The proposeEdit request itself is cancelled while the client
        decides.  The cancellation propagates -- the request ends as
        cancelled, never as applied -- but the edit request stays live:
        pygls would raise ``InvalidStateError`` into its reader on a
        late answer to a request cancelled out from under it."""
        server = self._server("manual")
        before = server.analyses[URI]

        async def script() -> None:
            workflow = asyncio.ensure_future(
                _awaited(apply_propose_edit(server, URI, SHIFTED_BASE)),
            )
            request = await server.request(workflow)
            workflow.cancel()
            with pytest.raises(asyncio.CancelledError):
                await workflow
            assert not request.future.cancelled()
            request.answer(True)  # late; must not raise

        _settle(server, script)
        assert _doc_state(server) == (SPEC_BASE, 1)
        assert server.analyses[URI] is before
        assert server.published == []

    def test_a_client_without_versioned_edits_is_sent_nothing(self) -> None:
        """No ``documentChanges``, no way to name a version: the edit
        would land on whatever the buffer holds when it arrives.  The
        gate's answer still comes back; the edit does not go out."""
        server = self._server("accept")
        server.client_capabilities = lsp.ClientCapabilities(
            workspace=lsp.WorkspaceClientCapabilities(apply_edit=True),
        )
        out = _settle(
            server, lambda: apply_propose_edit(server, URI, SHIFTED_BASE),
        )
        assert server.requests == []
        assert _doc_state(server) == (SPEC_BASE, 1)
        assert out["applied"] is False
        assert out["client"] == "unsupported"
        assert out["proof_delta"] is not None

    def test_an_unopened_document_is_refused(self) -> None:
        """proposeEdit on a URI the client has not opened: there is no
        version to guard the edit with -- the protocol's ``null`` means
        "the file on disk is the master", which a client applies to
        whatever its buffer holds when the edit lands -- and no analysis
        to judge it against.  Refused, as the two derived workflows
        refuse it, and nothing is sent."""
        server = _FakeServer("accept")
        refusal = _refusal(
            server, lambda: apply_propose_edit(server, URI, SPEC_BASE),
        )
        assert "open the document first" in refusal
        assert server.requests == []
        assert server.store.get(URI) is None
        assert server.published == []

    def test_an_unanswered_request_times_out_not_left_pending(self) -> None:
        """A request can go unanswered with nothing cancelling it -- a
        write error pygls swallows, or a client that hangs.  The wait is
        bounded, and the proposal answers ``timeout`` rather than never:
        with ``applied`` unknown, because the edit request is still open
        and the client may yet apply it."""
        server = self._server("silent")
        server.apply_edit_timeout_s = 0
        out = _settle(
            server, lambda: apply_propose_edit(server, URI, SHIFTED_BASE),
        )
        assert _doc_state(server) == (SPEC_BASE, 1)
        assert (out["applied"], out["client"]) == (None, "timeout")
        assert "did not answer within 0 s" in out["client_reason"]
        assert "may still apply it" in out["client_reason"]

    def test_an_edit_applied_after_the_timeout_still_reaches_the_server(
        self,
    ) -> None:
        """The case the ``timeout`` outcome exists for: the proposal has
        answered, and only then does the client apply the edit.  The
        answer said ``applied: null`` -- it claimed neither way -- and
        the client's own ``didChange`` brings the server's state along,
        as any change does.  (A real 0.2 s wait: the bound is what is
        under test.  The order is fixed by the awaits, not by it.)"""
        server = self._server("manual")
        server.apply_edit_timeout_s = 0.2

        async def script() -> dict[str, Any]:
            workflow = asyncio.ensure_future(
                _awaited(apply_propose_edit(server, URI, SHIFTED_BASE)),
            )
            request = await server.request(workflow)
            out = await workflow  # the bound runs out; nothing answered
            assert (out["applied"], out["client"]) == (None, "timeout")
            assert _doc_state(server) == (SPEC_BASE, 1)
            request.answer(server.apply(request))  # the client, late
            return out

        _settle(server, script)
        assert server.buffers[URI] == (SHIFTED_BASE, 11)
        assert _doc_state(server) == (SHIFTED_BASE, 11)
        assert server.analyses[URI].text == SHIFTED_BASE

    @pytest.mark.parametrize(("answer", "reason"), [
        (None, "answered null"),
        ({}, "has no `applied`"),
        ({"applied": "false"}, "'false', not a boolean"),
        ({"applied": 1}, "1, not a boolean"),
        ({"applied": None}, "None, not a boolean"),
    ])
    def test_an_answer_that_is_not_a_boolean_is_failed(
        self, answer: Any, reason: str,
    ) -> None:
        """Only a boolean ``applied`` is an answer, read off the JSON as
        sent -- the object pygls builds for an untyped result, since its
        typed reading turns ``"false"`` into ``True``."""
        from pygls.protocol import _dict_to_object

        from vera.lsp.workflows import read_answer

        outcome, applied, why = read_answer(_dict_to_object(answer))
        assert outcome == "failed"
        assert applied is None  # it answered, but not whether it applied
        assert reason in (why or "")

    def test_a_boolean_answer_is_read_as_sent(self) -> None:
        from pygls.protocol import _dict_to_object

        from vera.lsp.workflows import read_answer

        assert read_answer(_dict_to_object({"applied": True})) == (
            "applied", True, None,
        )
        assert read_answer(_dict_to_object(
            {"applied": False, "failureReason": "the buffer moved"},
        )) == ("declined", False, "the buffer moved")
        assert read_answer(
            lsp.ApplyWorkspaceEditResult(applied=False),
        ) == ("declined", False, None)

    def test_verification_lock_is_free_while_the_client_decides(
        self,
    ) -> None:
        """Z3 work stays serialised, but the lock is not held across the
        wait: the client's answer arrives while the workflow is
        suspended, and so does every notification the server must go on
        analysing meanwhile."""
        server = self._server("accept")
        _settle(server, lambda: apply_propose_edit(server, URI, SHIFTED_BASE))
        assert server.lock_held_when_asked == [False]

    def test_edit_workflows_wait_as_coroutines(self) -> None:
        """Waiting for the client's answer without blocking the reader
        that delivers it takes a coroutine -- in the workflows, and in
        the three handlers pygls schedules them from.  A synchronous
        handler that waited would stop the event loop that has to read
        the answer."""
        from vera.lsp.server import create_server

        for workflow in (apply_propose_edit, strengthen_contract, add_effect):
            assert inspect.iscoroutinefunction(workflow), workflow
        features = create_server().protocol.fm.features
        for method in (
            "vera/proposeEdit", "vera/strengthenContract", "vera/addEffect",
        ):
            assert inspect.iscoroutinefunction(features[method]), method


#: The client capabilities a wire scenario initialises with.
WIRE_VERSIONED_EDITS = {
    "workspace": {"applyEdit": True, "workspaceEdit": {"documentChanges": True}},
}

#: Failure detector for the wire scenarios, never an ordering device:
#: every step inside one is ordered by an await, and a working server
#: finishes in a small fraction of this.  It exists because the failure
#: it bounds -- a handler blocking the event loop while it waits for the
#: client -- would otherwise hang the suite instead of failing it.
WIRE_TIMEOUT_S = 300


class _WireClient:
    """A scripted client on the far side of a REAL server's protocol.

    The server writes to ``write`` -- its transport -- and each message
    it sends is queued for ``receive``.  ``send`` hands the server a
    JSON-RPC message the way pygls' own reader does: JSON decoded with
    ``structure_message`` as the object hook, then ``handle_message``.
    Server and client share one event loop, so events happen in the
    order of the awaits.
    """

    def __init__(self, server: Any) -> None:
        self.server = server
        self.inbox: asyncio.Queue[dict[str, Any]] = asyncio.Queue()
        #: Messages ``receive`` passed over, kept for ``unread``.
        self.held: list[dict[str, Any]] = []
        server.protocol.set_writer(self, include_headers=False)

    def write(self, data: bytes) -> None:
        self.inbox.put_nowait(json.loads(data.decode("utf-8")))

    def close(self) -> None:
        return None

    def send(self, **message: Any) -> None:
        protocol = self.server.protocol
        body = json.dumps({"jsonrpc": "2.0", **message})
        protocol.handle_message(
            json.loads(body, object_hook=protocol.structure_message),
        )

    async def receive(
        self, match: Callable[[dict[str, Any]], bool],
    ) -> dict[str, Any]:
        """The first message the server sent that satisfies *match*,
        waiting for it if need be; the others stay unread."""
        for i, message in enumerate(self.held):
            if match(message):
                return self.held.pop(i)
        while True:
            message = await self.inbox.get()
            if match(message):
                return message
            self.held.append(message)

    def unread(self) -> list[dict[str, Any]]:
        """Every message the server has sent that is not yet read, now
        marked read."""
        while not self.inbox.empty():
            self.held.append(self.inbox.get_nowait())
        out, self.held = self.held, []
        return out

    def start(self, capabilities: dict[str, Any], text: str) -> None:
        """initialize, initialized, and ``didOpen`` URI at version 1."""
        self.send(id="init", method="initialize", params={
            "processId": None, "rootUri": None,
            "capabilities": capabilities,
        })
        self.send(method="initialized", params={})
        self.did_open(text, 1)

    def did_open(self, text: str, version: int) -> None:
        self.send(method="textDocument/didOpen", params={"textDocument": {
            "uri": URI, "languageId": "vera", "version": version,
            "text": text,
        }})

    def did_change(self, text: str, version: int) -> None:
        self.send(method="textDocument/didChange", params={
            "textDocument": {"uri": URI, "version": version},
            "contentChanges": [{"text": text}],
        })

    def propose(self, request_id: str, text: str) -> None:
        self.send(id=request_id, method="vera/proposeEdit", params={
            "uri": URI, "text": text,
        })

    async def edit_request(self) -> dict[str, Any]:
        return await self.receive(
            lambda m: m.get("method") == "workspace/applyEdit",
        )

    async def response(self, request_id: str) -> dict[str, Any]:
        return await self.receive(
            lambda m: m.get("id") == request_id and "method" not in m,
        )


def _on_the_wire(
    scenario: Callable[[_WireClient], Awaitable[None]],
) -> None:
    """Run *scenario* against a fresh real server on its own thread and
    event loop, and re-raise whatever it raised on the test's thread."""
    from vera.lsp.server import create_server

    failures: list[BaseException] = []

    async def main() -> None:
        await scenario(_WireClient(create_server()))

    def run() -> None:
        try:
            asyncio.run(main())
        except BaseException as exc:  # noqa: BLE001 — carried to the test thread and re-raised there
            failures.append(exc)

    worker = threading.Thread(target=run, daemon=True)
    worker.start()
    worker.join(WIRE_TIMEOUT_S)
    if worker.is_alive():
        pytest.fail(
            "the server never finished the scenario: its event loop is "
            "blocked, which is what a handler that waits synchronously "
            "for the client's answer does",
        )
    if failures:
        raise failures[0]


class TestProposeEditOverTheWire:
    """The same questions asked of the REAL server: its handlers, pygls'
    dispatch, and a client that answers ``workspace/applyEdit`` the way
    an editor does -- later, and on its own terms."""

    def test_a_declined_edit_changes_nothing_and_answers_after_the_client(
        self,
    ) -> None:
        async def scenario(client: _WireClient) -> None:
            client.start(WIRE_VERSIONED_EDITS, SPEC_BASE)
            store = client.server.store
            client.propose("p", SHIFTED_BASE)
            request = await client.edit_request()
            # The response waits for the client; it is not already out.
            assert not [m for m in client.unread() if m.get("id") == "p"]
            assert not client.server.analysis_lock.locked(), LOCK_HELD
            (change,) = request["params"]["edit"]["documentChanges"]
            assert change["textDocument"] == {"uri": URI, "version": 1}
            # The user types; the edit names version 1, the buffer is at
            # 2, so a conforming client refuses it.
            client.did_change(TYPED_BASE, 2)
            client.send(id=request["id"], result={"applied": False})
            response = await client.response("p")
            assert response["result"]["applied"] is False
            assert response["result"]["client"] == "declined"
            doc = store.get(URI)
            assert (doc.text, doc.version) == (TYPED_BASE, 2)
            assert client.server.analyses[URI].text == TYPED_BASE

        _on_the_wire(scenario)

    def test_an_accepted_edit_converges_through_the_clients_did_change(
        self,
    ) -> None:
        async def scenario(client: _WireClient) -> None:
            client.start(WIRE_VERSIONED_EDITS, SPEC_BASE)
            store = client.server.store
            client.unread()
            client.propose("p", SHIFTED_BASE)
            request = await client.edit_request()
            client.send(id=request["id"], result={"applied": True})
            response = await client.response("p")
            # Answered, not yet notified: nothing to publish, and no
            # version to publish it at.
            doc = store.get(URI)
            assert (doc.text, doc.version) == (SPEC_BASE, 1)
            assert not [
                m for m in client.unread()
                if m.get("method") == "textDocument/publishDiagnostics"
            ]
            assert response["result"]["applied"] is True
            assert response["result"]["client"] == "applied"
            client.did_change(SHIFTED_BASE, 7)  # the client's own number
            doc = store.get(URI)
            assert (doc.text, doc.version) == (SHIFTED_BASE, 7)
            assert client.server.analyses[URI].text == SHIFTED_BASE
            assert [
                m["params"]["uri"] for m in client.unread()
                if m.get("method") == "textDocument/publishDiagnostics"
            ] == [URI]

        _on_the_wire(scenario)

    def test_a_cancelled_proposal_is_an_error_and_its_edit_stays_answerable(
        self,
    ) -> None:
        async def scenario(client: _WireClient) -> None:
            client.start(WIRE_VERSIONED_EDITS, SPEC_BASE)
            store = client.server.store
            client.propose("p", SHIFTED_BASE)
            request = await client.edit_request()
            client.send(method="$/cancelRequest", params={"id": "p"})
            response = await client.response("p")
            assert "result" not in response, response
            assert response["error"]["code"] == (
                lsp.LSPErrorCodes.RequestCancelled
            )
            # A late answer to the edit must not raise into the reader.
            client.send(id=request["id"], result={"applied": True})
            doc = store.get(URI)
            assert (doc.text, doc.version) == (SPEC_BASE, 1)

        _on_the_wire(scenario)

    def test_a_proposal_on_a_stale_analysis_is_refused(
        self, monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        """The handler's half of the stale-analysis refusal: a
        ``didChange`` whose analysis raises leaves the table behind the
        store, and a proposal gated against it comes back as
        ``InvalidParams`` naming why -- with no edit request sent."""
        import vera.lsp.server as server_module

        analyze_for_real = server_module.analyze

        def analyze_or_fail(
            session: VerificationSession, uri: str, text: str,
        ) -> Any:
            if text == TYPED_BASE:
                raise RuntimeError("an internal error in the pipeline")
            return analyze_for_real(session, uri, text)

        monkeypatch.setattr(server_module, "analyze", analyze_or_fail)

        async def scenario(client: _WireClient) -> None:
            client.start(WIRE_VERSIONED_EDITS, SPEC_BASE)
            client.did_change(TYPED_BASE, 2)  # the store moves; analysis fails
            client.propose("p", SHIFTED_BASE)
            first = await client.receive(
                lambda m: m.get("id") == "p"
                or m.get("method") == "workspace/applyEdit",
            )
            assert first.get("method") != "workspace/applyEdit", (
                "an edit was sent against a stale analysis"
            )
            assert first["error"]["code"] == lsp.ErrorCodes.InvalidParams
            assert "does not describe the open document" in (
                first["error"]["message"]
            )
            doc = client.server.store.get(URI)
            assert (doc.text, doc.version) == (TYPED_BASE, 2)

        _on_the_wire(scenario)

    def test_a_failed_analysis_is_published_and_its_readers_fall_silent(
        self, monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        """A ``didChange`` whose analysis raises: one ``E699`` naming the
        failure is published, the table keeps no entry for the text the
        buffer left, and hover and definition answer nothing -- where
        the previous text's analysis would have answered -- until a
        change the server can analyse brings them back."""
        import vera.lsp.server as server_module

        analyze_for_real = server_module.analyze

        def analyze_or_fail(
            session: VerificationSession, uri: str, text: str,
        ) -> Any:
            if text == TYPED_BASE:
                raise RuntimeError("an internal error in the pipeline")
            return analyze_for_real(session, uri, text)

        monkeypatch.setattr(server_module, "analyze", analyze_or_fail)
        at = {"line": 5, "character": 3}  # `@Nat.0` in SPEC_BASE's body

        async def ask(client: _WireClient, rid: str, method: str) -> Any:
            client.send(id=rid, method=method, params={
                "textDocument": {"uri": URI}, "position": at,
            })
            return (await client.response(rid))["result"]

        async def scenario(client: _WireClient) -> None:
            client.start(WIRE_VERSIONED_EDITS, SPEC_BASE)
            assert await ask(client, "h0", "textDocument/hover") is not None
            client.unread()
            client.did_change(TYPED_BASE, 2)
            published = [
                m["params"] for m in client.unread()
                if m.get("method") == "textDocument/publishDiagnostics"
            ]
            assert [p["uri"] for p in published] == [URI]
            (diagnostic,) = published[0]["diagnostics"]
            assert diagnostic["code"] == "E699"
            assert "Internal compiler error while analysing" in (
                diagnostic["message"]
            )
            assert "an internal error in the pipeline" in (
                diagnostic["message"]
            )
            assert URI not in client.server.analyses
            assert await ask(client, "h1", "textDocument/hover") is None
            assert await ask(client, "d1", "textDocument/definition") is None
            client.did_change(SPEC_BASE, 3)
            assert await ask(client, "h2", "textDocument/hover") is not None

        _on_the_wire(scenario)

    @pytest.mark.parametrize(("method", "params"), [
        ("vera/proposeEdit", {"text": SHIFTED_BASE}),
        ("vera/strengthenContract",
         {"fn": "f", "kind": "ensures", "expr": "true"}),
        ("vera/addEffect", {"fn": "f", "effect": "Async"}),
    ])
    def test_a_request_made_from_an_older_version_is_refused(
        self, method: str, params: dict[str, Any],
    ) -> None:
        async def scenario(client: _WireClient) -> None:
            client.start(WIRE_VERSIONED_EDITS, SPEC_BASE)
            client.did_change(TYPED_BASE, 2)
            client.send(id="r", method=method, params={
                "uri": URI, "version": 1, **params,
            })
            first = await client.receive(
                lambda m: m.get("id") == "r"
                or m.get("method") == "workspace/applyEdit",
            )
            assert first.get("method") != "workspace/applyEdit", (
                "an edit was sent for a request made from version 1"
            )
            assert first["error"]["code"] == lsp.ErrorCodes.InvalidParams
            assert "made from version 1" in first["error"]["message"]
            doc = client.server.store.get(URI)
            assert (doc.text, doc.version) == (TYPED_BASE, 2)

        _on_the_wire(scenario)

    def test_a_proposal_for_an_unopened_document_is_refused(self) -> None:
        """The race from PR #1485's review: a proposal for a document the
        client has not opened, then the client opens it and the user
        types.  An edit sent with a ``null`` version would land on the
        typing; the proposal is refused before anything is sent, and the
        typing stands."""
        async def scenario(client: _WireClient) -> None:
            client.send(id="init", method="initialize", params={
                "processId": None, "rootUri": None,
                "capabilities": WIRE_VERSIONED_EDITS,
            })
            client.send(method="initialized", params={})
            client.propose("p", SHIFTED_BASE)
            first = await client.receive(
                lambda m: m.get("id") == "p"
                or m.get("method") == "workspace/applyEdit",
            )
            assert first.get("method") != "workspace/applyEdit", (
                "an edit was sent for a document the client has not opened"
            )
            assert first["error"]["code"] == lsp.ErrorCodes.InvalidParams
            assert "open the document first" in first["error"]["message"]
            client.did_open(SPEC_BASE, 1)
            client.did_change(TYPED_BASE, 2)
            doc = client.server.store.get(URI)
            assert (doc.text, doc.version) == (TYPED_BASE, 2)

        _on_the_wire(scenario)

    @pytest.mark.parametrize("answer", [
        None, {}, {"applied": "false"},
    ], ids=["null", "empty", "string-false"])
    def test_an_answer_pygls_cannot_type_is_failed(self, answer: Any) -> None:
        """Each of these used to be dropped in pygls' reader (``null``,
        ``{}``) or read as ``True`` (``"false"``).  Read as sent, each
        completes the proposal as failed, with the reason and with
        ``applied`` unknown, and changes nothing."""
        async def scenario(client: _WireClient) -> None:
            client.start(WIRE_VERSIONED_EDITS, SPEC_BASE)
            client.propose("p", SHIFTED_BASE)
            request = await client.edit_request()
            client.send(id=request["id"], result=answer)
            response = await client.response("p")
            assert response["result"]["applied"] is None
            assert response["result"]["client"] == "failed"
            assert response["result"]["client_reason"]
            doc = client.server.store.get(URI)
            assert (doc.text, doc.version) == (SPEC_BASE, 1)

        _on_the_wire(scenario)

    def test_an_unanswered_request_completes_as_timeout(self) -> None:
        async def scenario(client: _WireClient) -> None:
            client.server.apply_edit_timeout_s = 0
            client.start(WIRE_VERSIONED_EDITS, SPEC_BASE)
            client.propose("p", SHIFTED_BASE)
            await client.edit_request()  # never answered
            response = await client.response("p")
            assert response["result"]["applied"] is None
            assert response["result"]["client"] == "timeout"
            assert "did not answer" in response["result"]["client_reason"]

        _on_the_wire(scenario)

    def test_an_edit_applied_after_the_timeout_reaches_the_server(
        self,
    ) -> None:
        """R-1485's repro, as a cell: with a 0.2 s bound, the proposal
        answers ``timeout`` with ``applied`` unknown; the client then
        applies the edit (its ``didChange`` at version 7, then
        ``applied: true``); the store ends at the client's text and
        version, and the late answer raises nothing in the reader."""
        async def scenario(client: _WireClient) -> None:
            client.server.apply_edit_timeout_s = 0.2
            client.start(WIRE_VERSIONED_EDITS, SPEC_BASE)
            client.propose("p", SHIFTED_BASE)
            request = await client.edit_request()
            response = await client.response("p")  # after the bound
            assert response["result"]["applied"] is None
            assert response["result"]["client"] == "timeout"
            assert "may still apply it" in response["result"]["client_reason"]
            client.unread()
            client.did_change(SHIFTED_BASE, 7)  # the client, late
            client.send(id=request["id"], result={"applied": True})
            doc = client.server.store.get(URI)
            assert (doc.text, doc.version) == (SHIFTED_BASE, 7)
            assert client.server.analyses[URI].text == SHIFTED_BASE
            assert not [
                m for m in client.unread()
                if m.get("method") == "window/showMessage"
            ]

        _on_the_wire(scenario)

    def test_a_conversion_that_raises_is_published_as_e699(
        self, monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        """The analysis succeeds and building what is published for it
        raises: that is a failure on this text like any other, so the
        entry is not kept and the E699 is published."""
        import vera.lsp.server as server_module

        convert_for_real = server_module.to_lsp_diagnostics

        def convert_or_fail(analysis: Any) -> Any:
            if analysis.text == TYPED_BASE:
                raise RuntimeError("conversion failed")
            return convert_for_real(analysis)

        monkeypatch.setattr(server_module, "to_lsp_diagnostics", convert_or_fail)

        async def scenario(client: _WireClient) -> None:
            client.start(WIRE_VERSIONED_EDITS, SPEC_BASE)
            client.unread()
            client.did_change(TYPED_BASE, 2)
            published = [
                m["params"] for m in client.unread()
                if m.get("method") == "textDocument/publishDiagnostics"
            ]
            assert [
                [d["code"] for d in p["diagnostics"]] for p in published
            ] == [["E699"]]
            assert URI not in client.server.analyses

        _on_the_wire(scenario)

    def test_a_failed_analysis_publishes_what_it_had_recorded(
        self, monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        """As the CLI's backstop does (#1429): the diagnostics the failing
        pass had recorded come first, then the E699."""
        import vera.lsp.server as server_module

        from vera.errors import (
            Diagnostic,
            SourceLocation,
            attach_partial_diagnostics,
        )

        analyze_for_real = server_module.analyze

        def record_then_fail(
            session: VerificationSession, uri: str, text: str,
        ) -> Any:
            if text != TYPED_BASE:
                return analyze_for_real(session, uri, text)
            exc = RuntimeError("the checker crashed part-way")
            attach_partial_diagnostics(exc, [Diagnostic(
                description="a refusal recorded before the crash",
                location=SourceLocation(file=uri, line=6, column=2),
                severity="error", error_code="E130",
            )])
            raise exc

        monkeypatch.setattr(server_module, "analyze", record_then_fail)

        async def scenario(client: _WireClient) -> None:
            client.start(WIRE_VERSIONED_EDITS, SPEC_BASE)
            client.unread()
            client.did_change(TYPED_BASE, 2)
            published = [
                m["params"] for m in client.unread()
                if m.get("method") == "textDocument/publishDiagnostics"
            ]
            assert [
                [d["code"] for d in p["diagnostics"]] for p in published
            ] == [["E130", "E699"]]

        _on_the_wire(scenario)

    def test_a_client_without_versioned_edits_is_told_so(self) -> None:
        async def scenario(client: _WireClient) -> None:
            client.start({}, SPEC_BASE)
            client.propose("p", SHIFTED_BASE)
            response = await client.response("p")
            assert response["result"]["applied"] is False
            assert response["result"]["client"] == "unsupported"
            assert not [
                m for m in client.unread()
                if m.get("method") == "workspace/applyEdit"
            ]
            doc = client.server.store.get(URI)
            assert (doc.text, doc.version) == (SPEC_BASE, 1)

        _on_the_wire(scenario)


# ---------------------------------------------------------------------
# #1444 — the class rule, over the source: who may write document state
# ---------------------------------------------------------------------

import ast as pyast  # noqa: E402

from dataclasses import dataclass  # noqa: E402

_REPO = pathlib.Path(__file__).resolve().parent.parent

#: What the store and its documents offer that only READS: everything
#: else they offer is a write, whatever it is called, so a method added
#: to either class is policed from the day it exists.
_STORE_READS = frozenset({"get", "__len__"})
_DOCUMENT_READS = frozenset({"index"})


def _document_fields() -> frozenset[str]:
    """A document's fields, from the class."""
    import dataclasses

    from vera.lsp.documents import Document

    return frozenset(f.name for f in dataclasses.fields(Document))


def _document_methods() -> frozenset[str]:
    """The document's own callables other than its declared reads."""
    from vera.lsp.documents import Document

    return frozenset(
        name for name, value in vars(Document).items()
        if callable(value) and not name.startswith("__")
        and name not in _DOCUMENT_READS
    )


_DICT_MUTATORS = frozenset({
    "pop", "popitem", "clear", "update", "setdefault",
    "__setitem__", "__delitem__",
})
#: Every way to put something in front of the client as the server's
#: view of a document: the two publishers, and the protocol they write to.
_PUBLISHERS = frozenset({
    "analyze_and_publish", "text_document_publish_diagnostics", "protocol",
})
#: Names whose dynamic access -- ``getattr(x, "store")``, ``vars(x)["store"]``
#: -- is a way round every other rule here.
_DYNAMIC = frozenset({"store", "analyses", "_docs"}) | _PUBLISHERS


@dataclass(frozen=True)
class _Write:
    """One write to document state, located in the source."""

    path: str  # repo-relative, POSIX
    line: int
    kind: str  # "store" / "document" / "analyses" / "publish" / "state"
    what: str  # the call or target, as written
    scope: tuple[str, int] | None  # innermost def: (name, first line)


def _document_state_writes(source: str, path: str) -> list[_Write]:
    """Every write, in *source*, to server state describing the
    client's buffer -- found by its shape, not by a list of callers:

    * ``store`` -- ANY reference to the document store that is not the
      receiver of one of its declared reads (``get``, ``len``) or the
      value an alias is bound to: a call of any other method, a method
      saved for later, the store passed along, iterated, entered or
      handed to ``getattr``.  The store is a name ``store``, an attribute
      ``.store``, the class ``DocumentStore`` or an alias of one;
    * ``document`` -- any use of ``_docs``; under ``vera/lsp/``, any
      assignment to or deletion of a document field (from
      ``dataclasses.fields(Document)``), and any call of a document
      method that is not a declared read;
    * ``analyses`` -- a mutation of the per-URI analysis table (an
      attribute ``.analyses``, a name ``analyses``, or an alias): an
      item assigned or deleted, an augmented assignment, or a mutating
      method called;
    * ``publish`` -- ANY reference to ``analyze_and_publish``,
      ``text_document_publish_diagnostics`` or the ``protocol`` they
      write to, called or not;
    * ``state`` -- ``.store`` or ``.analyses`` rebound wholesale, or a
      ``DocumentStore`` constructed;
    * ``dynamic`` -- ``getattr`` / ``setattr`` / ``delattr`` /
      ``hasattr``, ``vars(...)[...]`` or ``.__dict__[...]`` naming any
      of the above.

    An ALIAS is a name bound to the store or the table by any binding
    form that takes a value -- plain, annotated or walrus assignment,
    and element-wise unpacking of a tuple or list -- or a parameter
    annotated ``DocumentStore``.  Aliases of aliases are followed to a
    fixpoint, and a use of an alias is classified as a use of the store.

    Each is attributed to its innermost enclosing ``def`` or ``lambda``,
    keyed by name and first line (decorators included, which is what a
    code object's ``co_firstlineno`` gives).
    """
    tree = pyast.parse(source)
    in_lsp = path.startswith("vera/lsp/")
    store_names, table_names = _aliases(tree, in_lsp)
    fields = _document_fields()
    methods = _document_methods()
    parents = _parents(tree)
    writes: list[_Write] = []

    def record(node: pyast.AST, kind: str, scope: Any) -> None:
        writes.append(_Write(
            path, node.lineno, kind, pyast.unparse(node).split("\n")[0],
            scope,
        ))

    def is_store_ref(node: pyast.AST) -> bool:
        return (
            isinstance(node, pyast.Name) and isinstance(node.ctx, pyast.Load)
            and node.id in store_names
        ) or (
            isinstance(node, pyast.Attribute)
            and isinstance(node.ctx, pyast.Load) and node.attr == "store"
        ) or (
            isinstance(node, pyast.Attribute)
            and isinstance(node.value, pyast.Name)
            and node.value.id == "DocumentStore"
        )

    def is_declared_read(ref: pyast.AST) -> bool:
        parent = parents.get(ref)
        if (
            isinstance(parent, pyast.Attribute) and parent.value is ref
            and parent.attr in _STORE_READS
            and isinstance(parents.get(parent), pyast.Call)
            and parents[parent].func is parent
        ):
            return True
        return (
            isinstance(parent, pyast.Call) and parent.args == [ref]
            and isinstance(parent.func, pyast.Name)
            and parent.func.id == "len"
        )

    def visit(node: pyast.AST, scope: tuple[str, int] | None) -> None:
        if isinstance(node, (pyast.FunctionDef, pyast.AsyncFunctionDef)):
            scope = (node.name, min(
                [node.lineno] + [d.lineno for d in node.decorator_list],
            ))
        elif isinstance(node, pyast.Lambda):
            scope = ("<lambda>", node.lineno)
        if is_store_ref(node) and not is_declared_read(node) and not (
            _is_binding_value(node, parents)
        ):
            # Recorded as the USE -- the method it reaches, the call it
            # is passed to -- which is what makes it a write.  (A `with`
            # item has no position of its own; the reference stands in.)
            use = parents.get(node, node)
            record(use if hasattr(use, "lineno") else node, "store", scope)
        if (
            isinstance(node, pyast.Call) and isinstance(node.func, pyast.Name)
            and node.func.id == "DocumentStore"
        ):
            record(node, "state", scope)
        if isinstance(node, pyast.Call) and isinstance(
            node.func, pyast.Attribute,
        ):
            attr, receiver = node.func.attr, node.func.value
            if attr in _DICT_MUTATORS and _is_table(
                receiver, store_names, table_names,
            ):
                record(node, "analyses", scope)
            elif in_lsp and attr in methods:
                record(node, "document", scope)
        if isinstance(node, pyast.Attribute) and isinstance(
            node.ctx, pyast.Load,
        ) and node.attr in _PUBLISHERS:
            record(node, "publish", scope)
        if isinstance(node, pyast.Attribute) and node.attr == "_docs":
            record(node, "document", scope)
        if _is_dynamic_access(node, in_lsp):
            record(node, "dynamic", scope)
        targets: list[pyast.AST] = []
        if isinstance(node, pyast.Assign):
            targets = list(node.targets)
        elif isinstance(node, (pyast.AugAssign, pyast.AnnAssign)):
            targets = [node.target]
        elif isinstance(node, pyast.Delete):
            targets = list(node.targets)
        for target in targets:
            if isinstance(target, pyast.Subscript) and _is_table(
                target.value, store_names, table_names,
            ):
                record(target, "analyses", scope)
            elif (
                isinstance(node, pyast.AugAssign)
                and isinstance(target, pyast.Name)
                and target.id in table_names
            ):
                record(node, "analyses", scope)  # `table |= {...}`
            elif isinstance(target, pyast.Attribute):
                if target.attr in ("store", "analyses"):
                    record(target, "state", scope)
                elif in_lsp and target.attr in fields:
                    record(target, "document", scope)
        for child in pyast.iter_child_nodes(node):
            visit(child, scope)

    visit(tree, None)
    return writes


def _parents(tree: pyast.AST) -> dict[pyast.AST, pyast.AST]:
    return {
        child: node
        for node in pyast.walk(tree)
        for child in pyast.iter_child_nodes(node)
    }


def _is_binding_value(
    ref: pyast.AST, parents: dict[pyast.AST, pyast.AST],
) -> bool:
    """Whether *ref* is the value an alias is bound to -- directly, or as
    an element of a tuple or list that is -- so its uses are classified
    through the alias instead."""
    up, child = parents.get(ref), ref
    while isinstance(up, (pyast.Tuple, pyast.List)):
        up, child = parents.get(up), up
    return isinstance(
        up, (pyast.Assign, pyast.AnnAssign, pyast.NamedExpr),
    ) and up.value is child and not (
        isinstance(up, pyast.NamedExpr) and _used_on_the_spot(up, parents)
    )


def _used_on_the_spot(
    walrus: pyast.NamedExpr, parents: dict[pyast.AST, pyast.AST],
) -> bool:
    """A walrus whose value is used where it stands --
    ``(s := server.store).change(...)`` -- rather than only bound."""
    parent = parents.get(walrus)
    return not isinstance(parent, (pyast.Expr, pyast.Assign))


def _is_dynamic_access(node: pyast.AST, in_lsp: bool = True) -> bool:
    """``getattr``/``setattr``/``delattr``/``hasattr``, ``vars(x)[k]`` or
    ``x.__dict__[k]`` naming, by a string constant, something the scans
    police -- the store, the table, a publisher, and (under
    ``vera/lsp/``, where documents live) a document field."""
    watched = _DYNAMIC | (_document_fields() if in_lsp else frozenset())

    def named(arg: pyast.AST) -> bool:
        return isinstance(arg, pyast.Constant) and arg.value in watched

    if (
        isinstance(node, pyast.Call) and isinstance(node.func, pyast.Name)
        and node.func.id in ("getattr", "setattr", "delattr", "hasattr")
        and len(node.args) >= 2 and named(node.args[1])
    ):
        return True
    if isinstance(node, pyast.Subscript) and named(node.slice):
        base = node.value
        return (
            isinstance(base, pyast.Call) and isinstance(base.func, pyast.Name)
            and base.func.id == "vars"
        ) or (
            isinstance(base, pyast.Attribute) and base.attr == "__dict__"
        )
    return False


def _aliases(
    tree: pyast.AST, in_lsp: bool = True,
) -> tuple[set[str], set[str]]:
    """The names *tree* binds to the store and to the analysis table,
    followed through every value-binding form to a fixpoint (see
    :func:`_document_state_writes`).  The bare names ``store`` and
    ``analyses`` are taken to mean them only under ``vera/lsp/``, where
    they live: elsewhere ``store`` is wasmtime's."""
    store_names = {"store"} if in_lsp else set()
    table_names = {"analyses"} if in_lsp else set()
    for node in pyast.walk(tree):
        if isinstance(node, pyast.arg) and _names_store_type(node.annotation):
            store_names.add(node.arg)
    changed = True
    while changed:  # aliases of aliases
        changed = False
        for target, value in _bindings(tree):
            if not isinstance(target, pyast.Name):
                continue
            for names, is_it in (
                (store_names, _is_store), (table_names, _is_table),
            ):
                if target.id not in names and is_it(
                    value, store_names, table_names,
                ):
                    names.add(target.id)
                    changed = True
    return store_names, table_names


def _analysis_table_reads(source: str, path: str) -> list[_Write]:
    """Every READ of the per-URI analysis table in *source*.

    A reference to the table -- the attribute ``.analyses``, the name
    ``analyses``, or an alias (:func:`_aliases`) -- is a read unless it
    is the object of a write :func:`_document_state_writes` records (an
    item assigned or deleted, a mutating method called, an augmented
    assignment, a rebinding), or the value an alias is bound to, whose
    own uses are then classified the same way.  A walrus binding used on
    the spot (``(t := server.analyses).get(k)``) is classified by that
    use.  Attributed to the innermost enclosing ``def``, as the writes
    are.
    """
    tree = pyast.parse(source)
    store_names, table_names = _aliases(tree, path.startswith("vera/lsp/"))
    parents = {
        child: node
        for node in pyast.walk(tree)
        for child in pyast.iter_child_nodes(node)
    }

    def is_write_or_binding(ref: pyast.AST) -> bool:
        parent = parents.get(ref)
        if isinstance(parent, pyast.NamedExpr) and parent.value is ref:
            # Bound on the spot: what matters is what the walrus is used
            # for, unless it is itself only a binding.
            return is_write_or_binding(parent)
        if (
            isinstance(parent, pyast.Subscript) and parent.value is ref
            and isinstance(parent.ctx, (pyast.Store, pyast.Del))
        ):
            return True
        if (
            isinstance(parent, pyast.Attribute) and parent.value is ref
            and parent.attr in _DICT_MUTATORS
            and isinstance(parents.get(parent), pyast.Call)
        ):
            return True
        up, child = parent, ref
        while isinstance(up, (pyast.Tuple, pyast.List)):
            up, child = parents.get(up), up
        return (
            isinstance(up, (pyast.Assign, pyast.AnnAssign)) and up.value is child
        ) or (
            isinstance(up, pyast.NamedExpr) and up.value is child
            and isinstance(ref, (pyast.Tuple, pyast.List))
        )

    reads: list[_Write] = []

    def visit(node: pyast.AST, scope: tuple[str, int] | None) -> None:
        if isinstance(node, (pyast.FunctionDef, pyast.AsyncFunctionDef)):
            scope = (node.name, min(
                [node.lineno] + [d.lineno for d in node.decorator_list],
            ))
        elif isinstance(node, pyast.Lambda):
            scope = ("<lambda>", node.lineno)
        if (
            isinstance(node, (pyast.Name, pyast.Attribute))
            and isinstance(node.ctx, pyast.Load)
            and _is_table(node, store_names, table_names)
            and not is_write_or_binding(node)
        ):
            reads.append(_Write(
                path, node.lineno, "read",
                pyast.unparse(parents.get(node, node)).split("\n")[0],
                scope,
            ))
        for child in pyast.iter_child_nodes(node):
            visit(child, scope)

    visit(tree, None)
    return reads


def _bindings(tree: pyast.AST) -> list[tuple[pyast.AST, pyast.AST]]:
    """Every ``(target, value)`` pair a binding in *tree* makes: plain,
    annotated (with a value) and walrus assignment, with a tuple or list
    of targets unpacked element-wise against a value of the same
    shape."""
    pairs: list[tuple[pyast.AST, pyast.AST]] = []
    for node in pyast.walk(tree):
        if isinstance(node, pyast.Assign):
            pairs += [(target, node.value) for target in node.targets]
        elif isinstance(node, pyast.AnnAssign) and node.value is not None:
            pairs.append((node.target, node.value))
        elif isinstance(node, pyast.NamedExpr):
            pairs.append((node.target, node.value))
    unpacked: list[tuple[pyast.AST, pyast.AST]] = []
    while pairs:
        target, value = pairs.pop()
        if (
            isinstance(target, (pyast.Tuple, pyast.List))
            and isinstance(value, (pyast.Tuple, pyast.List))
            and len(target.elts) == len(value.elts)
        ):
            pairs += list(zip(target.elts, value.elts))
        else:
            unpacked.append((target, value))
    return unpacked


def _names_store_type(annotation: pyast.AST | None) -> bool:
    """Whether *annotation* spells ``DocumentStore``, bare, qualified or
    as a string."""
    if isinstance(annotation, pyast.Constant) and isinstance(
        annotation.value, str,
    ):
        return annotation.value.rsplit(".", 1)[-1] == "DocumentStore"
    return (
        isinstance(annotation, pyast.Name) and annotation.id == "DocumentStore"
    ) or (
        isinstance(annotation, pyast.Attribute)
        and annotation.attr == "DocumentStore"
    )


def _is_store(
    node: pyast.AST, store_names: set[str], table_names: set[str],
) -> bool:
    if isinstance(node, pyast.NamedExpr):  # `(s := server.store).change`
        return _is_store(node.value, store_names, table_names)
    return (
        (isinstance(node, pyast.Name) and node.id in store_names)
        or (isinstance(node, pyast.Attribute) and node.attr == "store")
        or (
            isinstance(node, pyast.Call)
            and isinstance(node.func, pyast.Name)
            and node.func.id == "DocumentStore"
        )
    )


def _is_table(
    node: pyast.AST, store_names: set[str], table_names: set[str],
) -> bool:
    if isinstance(node, pyast.NamedExpr):  # `(t := server.analyses)[k] = v`
        return _is_table(node.value, store_names, table_names)
    return (
        (isinstance(node, pyast.Name) and node.id in table_names)
        or (isinstance(node, pyast.Attribute) and node.attr == "analyses")
    )


def _code_scope(fn: Any) -> tuple[str, str, int]:
    """``(path, name, first line)`` of a live function."""
    fn = getattr(fn, "func", fn)  # pygls wraps handlers in a partial
    code = fn.__code__
    rel = pathlib.Path(code.co_filename).resolve().relative_to(_REPO)
    return rel.as_posix(), code.co_name, code.co_firstlineno


class TestDocumentStateWriters:
    """#1444's class, held over the whole compiler source.

    The server's document state -- the store, the analysis table, and
    what is published from it -- describes the client's open buffer.  So
    every write to it happens in the handler of one of the client's own
    three notifications (``didOpen`` / ``didChange`` / ``didClose``), or
    in ``analyze_and_publish``, whose callers are held to the same rule;
    the empty state is built in ``VeraLanguageServer.__init__``.  The
    writers are enumerated from the source by shape and the handlers
    from the live server's registrations, so a new writer anywhere in
    ``vera/`` that does not come from the client fails here.
    """

    def _live_scopes(
        self,
    ) -> tuple[dict[tuple[str, str, int], str], tuple[str, str, int], tuple[str, str, int]]:
        from vera.lsp.server import VeraLanguageServer, create_server

        features = create_server().protocol.fm.features
        handlers = {
            _code_scope(features[method]): method
            for method in (
                lsp.TEXT_DOCUMENT_DID_OPEN,
                lsp.TEXT_DOCUMENT_DID_CHANGE,
                lsp.TEXT_DOCUMENT_DID_CLOSE,
            )
        }
        return (
            handlers,
            _code_scope(VeraLanguageServer.analyze_and_publish),
            _code_scope(VeraLanguageServer.__init__),
        )

    def _writes(self) -> list[_Write]:
        writes = []
        for file in sorted((_REPO / "vera").rglob("*.py")):
            rel = file.relative_to(_REPO).as_posix()
            if rel == "vera/lsp/documents.py":
                continue  # the primitives themselves
            writes += _document_state_writes(
                file.read_text(encoding="utf-8"), rel,
            )
        return writes

    @staticmethod
    def _allowed(
        write: _Write,
        handlers: dict[tuple[str, str, int], str],
        publisher: tuple[str, str, int],
        constructor: tuple[str, str, int],
    ) -> bool:
        where = (
            None if write.scope is None else (write.path, *write.scope)
        )
        if write.kind == "state":
            return where == constructor
        if write.kind == "dynamic":
            return False
        if where in handlers:
            return True
        # `analyze_and_publish` may fill the table and publish -- that is
        # its job -- but not call itself: every CALL to it is a write the
        # handler rule has to see.
        return (
            where == publisher
            and write.kind in ("analyses", "publish")
            and "analyze_and_publish" not in write.what
        )

    def test_every_writer_is_a_client_notification(self) -> None:
        handlers, publisher, constructor = self._live_scopes()
        stray = [
            f"{w.path}:{w.line} [{w.kind}] {w.what}"
            for w in self._writes()
            if not self._allowed(w, handlers, publisher, constructor)
        ]
        assert not stray, (
            "document state written outside a client notification "
            "(didOpen / didChange / didClose):\n  " + "\n  ".join(stray)
        )

    def test_each_handler_writes_what_its_notification_says(self) -> None:
        """Premise for the cell above: the scan sees the writes that ARE
        there, one per notification, so its silence elsewhere means
        something."""
        handlers, publisher, _ = self._live_scopes()
        seen: dict[str, set[str]] = {}
        for w in self._writes():
            if w.scope is None:
                continue
            method = handlers.get((w.path, *w.scope))
            if method is not None and w.kind == "store":
                seen.setdefault(method, set()).add(
                    w.what.split("(")[0].rsplit(".", 1)[-1],
                )
        assert seen == {
            lsp.TEXT_DOCUMENT_DID_OPEN: {"open"},
            lsp.TEXT_DOCUMENT_DID_CHANGE: {"change"},
            lsp.TEXT_DOCUMENT_DID_CLOSE: {"close"},
        }
        assert {
            w.kind for w in self._writes()
            if w.scope is not None and (w.path, *w.scope) == publisher
        } == {"analyses", "publish"}

    def _reader_scopes(self) -> set[tuple[str, str, int]]:
        from vera.lsp.server import VeraLanguageServer

        return {_code_scope(VeraLanguageServer.current_analysis)}

    def _reads(self) -> list[_Write]:
        reads = []
        for file in sorted((_REPO / "vera").rglob("*.py")):
            rel = file.relative_to(_REPO).as_posix()
            reads += _analysis_table_reads(
                file.read_text(encoding="utf-8"), rel,
            )
        return reads

    def test_every_reader_of_the_table_checks_currency(self) -> None:
        """The table is read in one place, the accessor that returns an
        entry only if it describes the open text.  Every other reader --
        hover, definition, completion, the proof delta, the workflows --
        goes through it, so none can answer from a text the client's
        buffer has left, whatever state the table is in."""
        allowed = self._reader_scopes()
        stray = [
            f"{r.path}:{r.line} {r.what}"
            for r in self._reads()
            if r.scope is None or (r.path, *r.scope) not in allowed
        ]
        assert not stray, (
            "the analysis table read outside current_analysis:\n  "
            + "\n  ".join(stray)
        )

    def test_the_accessor_is_seen_reading_the_table(self) -> None:
        """Premise for the cell above: the scan sees the read that IS
        there, the accessor's own."""
        allowed = self._reader_scopes()
        assert {
            (r.path, *r.scope) for r in self._reads()
            if r.scope is not None
        } == allowed

    def test_the_scan_reports_a_reader_that_skips_the_accessor(
        self,
    ) -> None:
        """The instrument can fail: every way of reading the table
        outside the accessor is reported, and no write or alias binding
        is mistaken for a read."""
        planted = (
            "def hover(server, uri):\n"
            "    a = server.analyses.get(uri)\n"
            "    b = server.analyses[uri]\n"
            "    t = server.analyses\n"
            "    c = t.get(uri)\n"
            "    if uri in server.analyses:\n"
            "        pass\n"
            "    for u in server.analyses:\n"
            "        pass\n"
            "    d = (w := server.analyses).get(uri)\n"
            "    helper(server.analyses)\n"
            "    server.analyses[uri] = None\n"
            "    server.analyses.pop(uri)\n"
            "    del server.analyses[uri]\n"
            "    server.analyses = {}\n"
        )
        reads = _analysis_table_reads(planted, "vera/lsp/planted.py")
        assert [r.line for r in reads] == [2, 3, 5, 6, 8, 10, 11]
        assert not any(
            r.scope is not None
            and (r.path, *r.scope) in self._reader_scopes()
            for r in reads
        )

    def test_the_scan_reports_a_writer_that_bypasses_the_client(
        self,
    ) -> None:
        """The instrument can fail: every write in a planted
        reconciliation that never heard from the client is reported,
        whichever way its alias was bound -- plain, annotated, walrus,
        unpacked, or handed over as a ``DocumentStore`` parameter -- and
        none is attributed to a handler."""
        planted = (
            "def reconcile(server, uri, text):\n"
            "    server.store.change(uri, text, version=2)\n"
            "    s = server.store\n"
            "    s.open(uri, text, 1)\n"
            "    table = server.analyses\n"
            "    table[uri] = None\n"
            "    server.analyze_and_publish(uri, text)\n"
            "    doc = s.get(uri)\n"
            "    doc.text = text\n"
            "    server.store = None\n"
            "    typed: DocumentStore = server.store\n"
            "    typed.change(uri, text, 3)\n"
            "    annotated: dict[str, object] = server.analyses\n"
            "    annotated.pop(uri)\n"
            "    (walrus := server.analyses)[uri] = None\n"
            "    walrus.clear()\n"
            "    (held := server.store).close(uri)\n"
            "    held.open(uri, text, 4)\n"
            "    first, second = server.store, server.analyses\n"
            "    first.change(uri, text, 5)\n"
            "    second.update({})\n"
            "    table |= {}\n"
            "def hand_off(docs: DocumentStore, uri, text):\n"
            "    docs.change(uri, text, 6)\n"
        )
        writes = _document_state_writes(planted, "vera/lsp/planted.py")
        assert [(w.line, w.kind) for w in writes] == [
            (2, "store"), (4, "store"), (6, "analyses"), (7, "publish"),
            (9, "document"), (10, "state"),
            (12, "store"), (14, "analyses"), (15, "analyses"),
            (16, "analyses"), (17, "store"), (18, "store"), (20, "store"),
            (21, "analyses"), (22, "analyses"), (24, "store"),
        ]
        handlers, publisher, constructor = self._live_scopes()
        assert not any(
            self._allowed(w, handlers, publisher, constructor)
            for w in writes
        )


#: One planted spelling per rule of the writer scan, each reported by
#: that rule alone -- so removing any one rule turns exactly its case red
#: (PR #1485 review): ``(source, [(line, kind, scope name)])``.  The
#: snippets are parsed, never run, so they need only be Python.
WRITER_RULES: dict[str, tuple[str, list[tuple[int, str, str]]]] = {
    "a saved store method": (
        "def f(server, uri, text):\n"
        "    change = server.store.change\n"
        "    change(uri, text, 1)\n",
        [(2, "store", "f")],
    ),
    "the store passed to a helper": (
        "def f(server, uri, text):\n"
        "    reconcile(server.store, uri, text)\n",
        [(2, "store", "f")],
    ),
    "a loop alias": (
        "def f(server, uri, text):\n"
        "    for s in (server.store,):\n"
        "        s.change(uri, text, 1)\n",
        [(2, "store", "f")],
    ),
    "a with alias": (
        "def f(server, uri, text):\n"
        "    with server.store as s:\n"
        "        s.change(uri, text, 1)\n",
        [(2, "store", "f")],
    ),
    "getattr, setattr, vars and __dict__": (
        "def f(server, uri, text, doc):\n"
        "    getattr(server, 'store').change(uri, text, 1)\n"
        "    setattr(doc, 'text', text)\n"
        "    vars(server)['analyses'][uri] = None\n"
        "    server.__dict__['analyses'].get(uri)\n",
        [(2, "dynamic", "f"), (3, "dynamic", "f"), (4, "dynamic", "f"),
         (5, "dynamic", "f")],
    ),
    "a lambda is a scope of its own": (
        "def did_change(server, uri):\n"
        "    reset = lambda: server.store.change(uri, '', 0)\n",
        [(2, "store", "<lambda>")],
    ),
    "the protocol is a publisher": (
        "def f(server, params):\n"
        "    server.protocol.notify('textDocument/publishDiagnostics', params)\n",
        [(2, "publish", "f")],
    ),
    "a publisher counts uncalled": (
        "def f(server, uri, text):\n"
        "    publish = server.analyze_and_publish\n"
        "    publish(uri, text)\n",
        [(2, "publish", "f")],
    ),
    "a Document method is a write": (
        "def f(doc, text):\n"
        "    doc.set_text(text)\n",
        [(2, "document", "f")],
    ),
    "the Document fields come from the class": (
        "def f(doc):\n"
        "    doc.uri = 'file:///elsewhere.vera'\n",
        [(2, "document", "f")],
    ),
    "DocumentStore.<method> is the store": (
        "def f(uri, text):\n"
        "    DocumentStore.change(make_store(), uri, text, 1)\n",
        [(2, "store", "f")],
    ),
}


class TestEachWriterScanRule:
    """Each rule of the writer scan is pinned by a spelling only it
    reports.  The rules are what make the scan's silence mean something,
    and a rule no cell needs can be lost in a later edit without a
    failure (PR #1485 review)."""

    @pytest.mark.parametrize("rule", list(WRITER_RULES))
    def test_the_rule_reports_its_spelling(
        self, rule: str, monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        from vera.lsp.documents import Document

        # A method the class does not have today: the rule must come
        # from the class as it stands, not from a list written earlier.
        monkeypatch.setattr(
            Document, "set_text", lambda self, text: None, raising=False,
        )
        source, expected = WRITER_RULES[rule]
        writes = _document_state_writes(source, "vera/lsp/planted.py")
        assert [
            (w.line, w.kind, w.scope[0] if w.scope else None)
            for w in writes
        ] == expected

    def test_a_lambda_is_a_scope_of_its_own_in_the_reader_scan(
        self,
    ) -> None:
        """A lambda inside the accessor's own ``def`` is not the
        accessor: its read is attributed to the lambda, so it is not
        sanctioned by the accessor's name."""
        planted = (
            "def current_analysis(self, uri):\n"
            "    self._peek = lambda u: self.analyses.get(u)\n"
            "    return None\n"
        )
        reads = _analysis_table_reads(planted, "vera/lsp/planted.py")
        assert [(r.line, r.scope) for r in reads] == [(2, ("<lambda>", 2))]


class TestParamExtraction:
    """Custom-method params arrive as attribute namespaces from pygls
    or plain dicts from in-process callers; ``_param`` must treat
    falsy-but-present values (``text=""``) as present."""

    def test_empty_text_on_attribute_carrier(self) -> None:
        params = types.SimpleNamespace(uri=URI, text="")
        assert _param(params, "text") == ""
        assert _param(params, "uri") == URI

    def test_dict_params(self) -> None:
        assert _param({"uri": URI, "text": ""}, "text") == ""
        assert _param({"force": False}, "force") is False

    def test_missing_key_is_none(self) -> None:
        assert _param(types.SimpleNamespace(uri=URI), "force") is None
        assert _param({"uri": URI}, "force") is None

    def test_require_str_accepts_present_strings(self) -> None:
        assert _require_str({"uri": URI}, "uri") == URI
        # Empty string is a PRESENT value (replace-with-empty-document).
        assert _require_str({"text": ""}, "text") == ""
        assert _require_str(
            types.SimpleNamespace(text=""), "text",
        ) == ""

    def test_require_str_refuses_missing_or_non_string(self) -> None:
        """Malformed payloads fail closed at the protocol boundary
        with JSON-RPC InvalidParams, not an opaque internal error
        from deep inside the parse pipeline."""
        for params in ({}, {"uri": None}, {"uri": 42}, {"uri": ["x"]}):
            with pytest.raises(JsonRpcInvalidParams):
                _require_str(params, "uri")
        with pytest.raises(JsonRpcInvalidParams):
            _require_str(types.SimpleNamespace(), "text")

    def test_version_is_an_integer_or_absent(self) -> None:
        """``version`` is optional; when present it is compared, so a
        value the server cannot compare fails closed rather than skip
        the comparison -- ``true`` included, which Python counts as an
        ``int``."""
        from vera.lsp.server import _version_param

        assert _version_param({}) is None
        assert _version_param({"version": None}) is None
        assert _version_param({"version": 3}) == 3
        assert _version_param(types.SimpleNamespace(version=0)) == 0
        for bad in (True, False, "3", 3.0, [3]):
            with pytest.raises(JsonRpcInvalidParams):
                _version_param({"version": bad})

    def test_force_fails_closed(self) -> None:
        """Only JSON ``true`` engages force — the gate-bypass flag
        must never be engaged by a malformed payload (``"false"`` the
        string is truthy under bool())."""
        assert _force_param({"force": True}) is True
        assert _force_param(types.SimpleNamespace(force=True)) is True
        for bad in ("false", "true", 1, 0, None, [True]):
            assert _force_param({"force": bad}) is False
        assert _force_param({}) is False


class TestFullDocumentRange:
    def test_trailing_newline_ends_on_virtual_line(self) -> None:
        from vera.lsp.documents import Document

        r = full_document_range(Document(uri=URI, text="a\nb\n"))
        assert r.end == lsp.Position(line=2, character=0)

    def test_no_trailing_newline_ends_in_utf16_units(self) -> None:
        from vera.lsp.documents import Document

        # ASTRAL_LINE = "ab🎉cd": 5 code points, 6 UTF-16 units.
        r = full_document_range(Document(uri=URI, text=ASTRAL_LINE))
        assert r.end == lsp.Position(line=0, character=6)


# =====================================================================
# Phase F2 — vera/strengthenContract call-site audit workflow
# =====================================================================

# A caller/callee pair with trivially-true contracts: the substrate
# for contract-strengthening deltas in both directions.
CALL_BASE = (
    "public fn callee(@Nat -> @Nat)\n"
    "  requires(true)\n"
    "  ensures(true)\n"
    "  effects(pure)\n"
    "{\n"
    "  @Nat.0\n"
    "}\n"
    "\n"
    "public fn caller(@Nat -> @Nat)\n"
    "  requires(true)\n"
    "  ensures(true)\n"
    "  effects(pure)\n"
    "{\n"
    "  callee(@Nat.0)\n"
    "}\n"
)


def _program(text: str) -> object:
    a = analyze(VerificationSession(), URI, text)
    assert a.program is not None
    return a.program


class TestSpliceContract:
    def test_replaces_first_requires_of_named_fn(self) -> None:
        out = splice_contract(
            _program(CALL_BASE), CALL_BASE,
            "callee", "requires", "@Nat.0 >= 1",
        )
        assert out is not None
        # callee's clause replaced, caller's untouched.
        assert out.count("requires(@Nat.0 >= 1)") == 1
        assert out.count("requires(true)") == 1
        assert out.index("requires(@Nat.0 >= 1)") < out.index(
            "requires(true)",
        )
        # Everything else byte-identical.
        assert out.replace(
            "requires(@Nat.0 >= 1)", "requires(true)", 1,
        ) == CALL_BASE

    def test_replaces_ensures(self) -> None:
        out = splice_contract(
            _program(CALL_BASE), CALL_BASE,
            "caller", "ensures", "@Nat.0 >= 0",
        )
        assert out is not None
        assert "ensures(@Nat.0 >= 0)" in out
        # callee's ensures untouched: exactly one replaced.
        assert out.count("ensures(true)") == 1

    def test_unknown_fn_returns_none(self) -> None:
        assert splice_contract(
            _program(CALL_BASE), CALL_BASE,
            "missing", "requires", "true",
        ) is None


class TestStrengthenContract:
    def _server(self, policy: str = "accept") -> _FakeServer:
        server = _FakeServer(policy)
        server.open(URI, CALL_BASE, version=1)
        server.published.clear()
        return server

    def test_tightened_pre_refused_with_call_site_audit(self) -> None:
        """The Phase F2 pin: a precondition some caller no longer
        satisfies surfaces as newly_undischarged call_pre items at the
        call site, and the gate refuses the edit."""
        server = self._server()
        out = _settle(server, lambda: strengthen_contract(
            server, URI, "callee", "requires", "@Nat.0 >= 1",
        ))
        assert out["applied"] is False
        und = out["proof_delta"]["newly_undischarged"]
        assert any(i["kind"] == "call_pre" for i in und)
        # Canonical state untouched.
        doc = server.store.get(URI)
        assert doc is not None
        assert doc.text == CALL_BASE
        assert server.requests == []

    def test_provable_ensures_applies(self) -> None:
        """Strengthening callee's postcondition to something its body
        proves (identity on @Nat is always >= 0) discharges and
        applies -- through the client, whose ``didChange`` is what
        brings the server's state along."""
        server = self._server()
        out = _settle(server, lambda: strengthen_contract(
            server, URI, "callee", "ensures", "@Nat.0 >= 0",
        ))
        doc = server.store.get(URI)
        assert doc is not None
        assert "ensures(@Nat.0 >= 0)" in doc.text
        assert doc.version == 1 + _FakeServer.STEP
        assert server.published == [URI]
        assert out["applied"] is True
        assert out["client"] == "applied"
        assert out["proof_delta"]["newly_undischarged"] == []

    def test_the_candidate_is_guarded_by_the_version_it_was_spliced_from(
        self,
    ) -> None:
        """The splice is computed from the canonical text, so the edit
        names that text's version: if the user types while the client
        has the request, the client refuses it rather than lose the
        typing to a candidate built without it."""
        server = self._server("manual")

        async def script() -> dict[str, Any]:
            workflow = asyncio.ensure_future(_awaited(strengthen_contract(
                server, URI, "callee", "ensures", "@Nat.0 >= 0",
            )))
            request = await server.request(workflow)
            assert request.target()[1] == 1
            server.type(URI, "-- typed\n" + CALL_BASE)
            request.answer(server.apply(request))
            return await workflow

        out = _settle(server, script)
        assert _doc_state(server) == ("-- typed\n" + CALL_BASE, 11)
        assert out["applied"] is False
        assert out["client"] == "declined"

    def test_no_analysis_raises(self) -> None:
        server = _FakeServer()
        with pytest.raises(ValueError, match="open the document"):
            _settle(server, lambda: strengthen_contract(
                server, URI, "callee", "requires", "true",
            ))

    def test_unparseable_document_raises(self) -> None:
        server = _FakeServer()
        server.open(URI, "public fn broken(", version=1)
        with pytest.raises(ValueError, match="does not parse"):
            _settle(server, lambda: strengthen_contract(
                server, URI, "callee", "requires", "true",
            ))

    def test_unknown_fn_raises(self) -> None:
        server = self._server()
        with pytest.raises(ValueError, match="missing"):
            _settle(server, lambda: strengthen_contract(
                server, URI, "missing", "requires", "true",
            ))


# =====================================================================
# Phase F3 — vera/addEffect call-graph propagation workflow
# =====================================================================

def _fn(name: str, body: str, effects: str = "pure") -> str:
    return (
        f"public fn {name}(@Nat -> @Nat)\n"
        f"  requires(true)\n"
        f"  ensures(true)\n"
        f"  effects({effects})\n"
        "{\n"
        f"  {body}\n"
        "}\n"
    )


# Diamond: top -> left -> target, top -> right -> target, plus a
# bystander that never calls into the diamond.
DIAMOND = "\n".join([
    _fn("target", "@Nat.0"),
    _fn("left", "target(@Nat.0)"),
    _fn("right", "target(target(@Nat.0))"),
    _fn("top", "left(right(@Nat.0))"),
    _fn("lone", "@Nat.0"),
])


# Handler bounding (#725).  A `handle[State<Int>]` around the call
# discharges the effect, so the caller needs no row of its own; the
# same call reached on a second, unhandled path still does.
_HANDLED = """handle[State<Int>](@Int = 0) {
    get(@Unit) -> { resume(@Int.0) },
    put(@Int) -> { resume(()) }
  } in {
    put(1);
    target(@Nat.0)
  }"""

_PARTIAL = f"""let @Nat = {_HANDLED};
  target(@Nat.1)"""

HANDLERS = "\n".join([
    _fn("target", "@Nat.0"),
    _fn("handled", _HANDLED),
    _fn("partial", _PARTIAL),
    _fn("unhandled", "target(@Nat.0)"),
])

# Two shapes that must NOT bound propagation: a call inside a handler
# *clause* (clause bodies run outside their own handler, so the effect
# still escapes) and a handler for an unrelated effect.
HANDLER_EDGES = "\n".join([
    _fn("target", "@Nat.0"),
    _fn("in_clause", """handle[State<Nat>](@Nat = 0) {
    get(@Unit) -> { resume(target(@Nat.0)) },
    put(@Nat) -> { resume(()) }
  } in {
    put(1);
    get(())
  }"""),
    _fn("other_effect", """handle[Exn<Int>] {
    throw(@Int) -> { 0 }
  } in {
    target(@Nat.0)
  }"""),
])

# A handler whose effect INSTANCE differs from the propagated one, in
# the handler *body* where pruning would otherwise apply.  The checker
# discharges against `EffectInstance`, whose equality includes
# `type_args`, so `handle[State<Nat>]` leaves `State<Int>` escaping and
# the caller still needs the row.  Asking the same fixture for
# `State<Nat>` is the positive control: this handler key does match
# something, so the surviving `State<Int>` edge is the type argument
# and not an unmatchable key.
MISMATCHED_INSTANCE = "\n".join([
    _fn("target", "@Nat.0"),
    _fn("nat_handled", """handle[State<Nat>](@Nat = 0) {
    get(@Unit) -> { resume(@Nat.0) },
    put(@Nat) -> { resume(()) }
  } in {
    put(1);
    target(@Nat.0)
  }"""),
])

# `where`-block calls attribute to their containing top-level function
# (pre-#725 behaviour), and the handler bound applies inside a helper
# body just as it does in the top-level body.
WHERE_HANDLERS = "\n".join([
    _fn("target", "@Nat.0"),
    _fn("via_where_handled", "helper(@Nat.0)") + f"""where {{
  fn helper(@Nat -> @Nat)
    requires(true)
    ensures(true)
    effects(pure)
  {{
    {_HANDLED}
  }}
}}
""",
    _fn("via_where_bare", "helper2(@Nat.0)") + """where {
  fn helper2(@Nat -> @Nat)
    requires(true)
    ensures(true)
    effects(pure)
  {
    target(@Nat.0)
  }
}
""",
])

# Refinement type arguments, top-level and nested.  Both handlers
# type-check (`vera check` is clean on this program), and neither
# discharges plain `Exn<Int>` — a call needing it inside either body
# fails E125.  `format_type_expr` renders a refinement as its bare base
# type, so a key built straight from it would spell `Exn<Int>` for both
# and prune those edges.
REFINED_INSTANCE = "\n".join([
    _fn("target", "@Nat.0"),
    _fn("refined", """handle[Exn<{ @Int | @Int.0 >= 0 }>] {
    throw(@Int) -> { 0 }
  } in {
    target(@Nat.0)
  }"""),
    _fn("nested_refined", """handle[Exn<Array<{ @Int | @Int.0 >= 0 }>>] {
    throw(@Array<Int>) -> { 0 }
  } in {
    target(@Nat.0)
  }"""),
])

# An unparameterised handler: `handle[IO]` really does discharge `IO`,
# and `IO`/`Async` are what addEffect propagates most often.
BARE_HANDLER = "\n".join([
    _fn("target", "@Nat.0"),
    _fn("io_handled", """handle[IO] {
    print(@String) -> { resume(()) }
  } in {
    target(@Nat.0)
  }"""),
    _fn("io_unhandled", "target(@Nat.0)"),
])

# Nesting, both orders.  A matching handler inside a foreign one still
# bounds the closure; a foreign handler inside a matching one does not
# un-bound it, because the call still sits in the matching handler's
# body sub-tree.
NESTED_HANDLERS = "\n".join([
    _fn("target", "@Nat.0"),
    _fn("inner_match", """handle[Exn<Nat>] {
    throw(@Nat) -> { 0 }
  } in {
    handle[Exn<Int>] {
      throw(@Int) -> { 0 }
    } in {
      target(@Nat.0)
    }
  }"""),
    _fn("outer_match", """handle[Exn<Int>] {
    throw(@Int) -> { 0 }
  } in {
    handle[Exn<Nat>] {
      throw(@Nat) -> { 0 }
    } in {
      target(@Nat.0)
    }
  }"""),
])

# The handler's STATE INITIALISER, the third sub-tree of a HandleExpr
# and the one with its own reason for propagating.  A clause body runs
# outside the handler because that is what a clause IS; the initialiser
# runs outside it because it is evaluated in the ENCLOSING scope,
# before the handler is installed at all — `_check_handle` synths
# `state.init_expr` before it extends `env.current_effect_row` with the
# handled effect (`vera/checker/control.py`), and codegen evaluates the
# init expression before pushing the cell (`_translate_handle_state`
# step 1, `vera/wasm/calls_handlers.py`).  `body_call` is the positive
# control: the same handler spelling DOES prune a call in its body.
STATE_INIT = "\n".join([
    _fn("target", "@Nat.0"),
    _fn("init_call", """handle[State<Int>](@Int = nat_to_int(target(@Nat.0))) {
    get(@Unit) -> { resume(@Int.0) },
    put(@Int) -> { resume(()) }
  } in {
    get(());
    @Nat.0
  }"""),
    _fn("body_call", _HANDLED),
])

# The same boundary as the checker states it, in a program whose caller
# is `pure`: a `State<Int>`-effectful call in the initialiser of a
# `handle[State<Int>]` is an E125 against the enclosing row, while the
# identical call in that handler's body is clean.  This is the fact the
# closure rule above rests on, so it is pinned rather than asserted in
# a comment.
_STATE_INIT_BUMP = """private fn bump(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(<State<Int>>)
{
  get(())
}
"""

STATE_INIT_UNDISCHARGED = _STATE_INIT_BUMP + """
private fn caller_init(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Int>](@Int = bump(())) {
    get(@Unit) -> { resume(@Int.0) },
    put(@Int) -> { resume(()) }
  } in {
    get(())
  }
}
"""

STATE_BODY_DISCHARGED = _STATE_INIT_BUMP + """
private fn caller_body(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Int>](@Int = 5) {
    get(@Unit) -> { resume(@Int.0) },
    put(@Int) -> { resume(()) }
  } in {
    bump(())
  }
}
"""

# An ALIAS-spelled handler.  `target` DECLARES `<State<Int>>` (a
# declared-but-unused row is legal), so `alias_handled` staying `pure`
# is only possible if `handle[State<MyAlias>]` discharges `State<Int>`
# — which it does, `type MyAlias = Int` resolving to the same instance.
# The bound, though, compares the handler's SOURCE SPELLING to the
# request string, so a `State<Int>` request does not match it and the
# edge survives: an under-prune, in the safe direction.  Documented
# behaviour until #1292 swaps the comparison onto resolved instances.
ALIAS_HANDLER = "type MyAlias = Int;\n\n" + "\n".join([
    _fn("target", "@Nat.0", "<State<Int>>"),
    _fn("alias_handled", """handle[State<MyAlias>](@MyAlias = 0) {
    get(@Unit) -> { resume(@MyAlias.0) },
    put(@MyAlias) -> { resume(()) }
  } in {
    put(1);
    target(@Nat.0)
  }"""),
])


# #1558: inside `module ma;`, `ma::target(...)` is the call to `target` its
# bare spelling is, so its caller is on the closure too.
OWN_PATH = "module ma;\n\n" + "\n".join([
    _fn("target", "@Nat.0"),
    _fn("by_path", "ma::target(@Nat.0)"),
    _fn("bare", "target(@Nat.0)"),
    _fn("lone", "@Nat.0"),
])


class TestTransitiveCallers:
    def test_diamond_closure_in_declaration_order(self) -> None:
        prog = _program(DIAMOND)
        assert transitive_callers(prog, "target") == [
            "target", "left", "right", "top",
        ]

    def test_leaf_only_includes_itself(self) -> None:
        assert transitive_callers(_program(DIAMOND), "lone") == ["lone"]

    def test_unknown_fn_is_none(self) -> None:
        assert transitive_callers(_program(DIAMOND), "ghost") is None

    def test_recursive_fn_appears_once(self) -> None:
        src = _fn("rec", "rec(@Nat.0)")
        assert transitive_callers(_program(src), "rec") == ["rec"]

    def test_no_effect_argument_is_handler_unaware(self) -> None:
        """The bare call-graph query is unchanged: every caller."""
        assert transitive_callers(_program(HANDLERS), "target") == [
            "target", "handled", "partial", "unhandled",
        ]

    def test_handler_bounds_the_closure(self) -> None:
        """#725: a caller whose only call site sits inside a
        handle[E] body is dropped; a caller that also reaches the
        callee on an unhandled path is kept."""
        assert transitive_callers(
            _program(HANDLERS), "target", "State<Int>",
        ) == ["target", "partial", "unhandled"]

    def test_handler_clause_and_foreign_handler_do_not_bound(self) -> None:
        """Only a handler's ``body`` prunes: a call in a *clause* still
        propagates, as does one under a handler for another effect.

        Propagating State<Nat> — the instance ``in_clause`` handles — so
        the only reason its edge survives is that the call sits in a
        clause, not the body.  Asking for a *different* instance would
        keep the edge for that reason instead and stop discriminating
        the clause boundary at all.
        """
        assert transitive_callers(
            _program(HANDLER_EDGES), "target", "State<Nat>",
        ) == ["target", "in_clause", "other_effect"]

    def test_state_initialiser_call_keeps_the_edge(self) -> None:
        """A handler's STATE INITIALISER is not discharged by that
        handler, so the only call site there still propagates.

        `body_call` is the positive control: the same handler spelling
        prunes a call in its *body*, so the surviving `init_call` edge
        is the initialiser boundary and not a key nothing matches.
        Pruning the initialiser is the unsafe direction — the caller
        would be left `pure` and its own call site would fail E125, as
        the companion test below shows.
        """
        assert transitive_callers(
            _program(STATE_INIT), "target", "State<Int>",
        ) == ["target", "init_call"]

    def test_state_initialiser_is_undischarged_at_the_checker(self) -> None:
        """The language fact the rule above rests on.

        The initialiser is evaluated in the enclosing scope, before the
        handler is installed, so a `State<Int>` call there is an E125
        against a `pure` caller's row.  The body half is the contrast:
        the identical call inside the handler's body is clean, which is
        what makes E125 the *initialiser's* property rather than the
        handler's.
        """
        init = analyze(VerificationSession(), URI, STATE_INIT_UNDISCHARGED)
        assert "E125" in [d.error_code for d in init.diagnostics]
        body = analyze(VerificationSession(), URI, STATE_BODY_DISCHARGED)
        assert not [
            d for d in body.diagnostics if d.severity == "error"
        ], body.diagnostics

    def test_alias_spelled_handler_does_not_bound(self) -> None:
        """#1292: the bound compares source spellings, not resolved
        effect instances.

        Both halves are pinned on the one fixture.  The checker's: the
        program is error-free, and it can only be — `alias_handled` is
        `pure` around a call to a `<State<Int>>`-declaring `target` —
        if `handle[State<MyAlias>]` discharges `State<Int>`.  The
        closure's: a `State<Int>` request does not match the key that
        handler spells, so the caller keeps an edge it does not need.

        An under-prune writes a row the program can live without and
        still type-checks, so this is the safe side of the same
        asymmetry that keeps a mismatched type argument's edge.  The
        alias-spelled request is the discriminating control: it *does*
        prune, so the surviving `State<Int>` edge is the spelling
        comparison and not an unmatchable key.
        """
        a = analyze(VerificationSession(), URI, ALIAS_HANDLER)
        assert a.program is not None
        assert not [
            d for d in a.diagnostics if d.severity == "error"
        ], a.diagnostics
        assert transitive_callers(a.program, "target", "State<Int>") == [
            "target", "alias_handled",
        ]
        assert transitive_callers(a.program, "target", "State<MyAlias>") == [
            "target",
        ]

    def test_matching_type_argument_prunes_the_edge(self) -> None:
        """Positive control for the fixture below: the same
        `handle[State<Nat>]` body DOES prune a `State<Nat>`
        propagation.  Without this, an unmatchable key for every
        parameterised handler would leave the mismatch test green."""
        assert transitive_callers(
            _program(MISMATCHED_INSTANCE), "target", "State<Nat>",
        ) == ["target"]

    def test_mismatched_type_argument_keeps_the_edge(self) -> None:
        """handle[State<Nat>] does not discharge State<Int>, so the
        edge survives and the caller stays in the closure."""
        assert transitive_callers(
            _program(MISMATCHED_INSTANCE), "target", "State<Int>",
        ) == ["target", "nat_handled"]

    def test_where_helper_attribution_survives_the_bound(self) -> None:
        """A helper's bare call still attributes to its containing
        top-level function; a helper that discharges the effect itself
        bounds the closure there."""
        prog = _program(WHERE_HANDLERS)
        assert transitive_callers(prog, "target") == [
            "target", "via_where_handled", "via_where_bare",
        ]
        assert transitive_callers(prog, "target", "State<Int>") == [
            "target", "via_where_bare",
        ]

    def test_refinement_argument_keeps_the_edge(self) -> None:
        """A refinement argument must not collapse into its base type:
        `handle[Exn<{ @Int | p }>]` does not discharge `Exn<Int>`
        (E125 at the call site), nested inside a type argument
        included."""
        assert transitive_callers(
            _program(REFINED_INSTANCE), "target", "Exn<Int>",
        ) == ["target", "refined", "nested_refined"]

    def test_bare_handler_bounds_the_closure(self) -> None:
        """An unparameterised `handle[IO]` bounds an `IO`
        propagation."""
        assert transitive_callers(
            _program(BARE_HANDLER), "target", "IO",
        ) == ["target", "io_unhandled"]

    def test_whitespace_in_the_request_still_matches(self) -> None:
        """Request and handler are compared whitespace-insensitively,
        so a spelled-out `State< Int >` still bounds the closure."""
        assert transitive_callers(
            _program(HANDLERS), "target", "State< Int >",
        ) == ["target", "partial", "unhandled"]

    def test_nesting_bounds_in_either_order(self) -> None:
        """A matching handler nested inside a foreign one still bounds
        the closure, and a foreign handler nested inside a matching one
        does not un-bound it."""
        assert transitive_callers(
            _program(NESTED_HANDLERS), "target", "Exn<Int>",
        ) == ["target"]

    def test_qualified_handler_key_keeps_its_module(self) -> None:
        """`handle[Mod.IO]` spells `Mod.IO`, not `IO`.

        Pinned at the key rather than through `transitive_callers`:
        effects are only ever registered under an unqualified name
        (`effect_decl` takes a single UPPER_IDENT), so a qualified
        handler always fails E330 and no program in which this key
        could prune ever type-checks.
        """
        ref = QualifiedEffectRef(module="Mod", name="IO", type_args=None)
        assert _handled_effect_key(ref) == "Mod.IO"

    @pytest.mark.parametrize("effect", [None, "Async"])
    def test_a_call_by_the_own_path_is_an_edge(
        self, effect: str | None,
    ) -> None:
        """#1558: with the document's own path `ma`, `by_path`'s
        `ma::target(...)` calls `target` and is on the closure, in the
        handler-unaware query and the bounded one alike.  Without an own
        path the same call names another module, and is no edge."""
        prog = _program(OWN_PATH)
        assert transitive_callers(
            prog, "target", effect, own_path=("ma",),
        ) == ["target", "by_path", "bare"]
        assert transitive_callers(prog, "target", effect) == [
            "target", "bare",
        ]


class TestEffectRowRewrite:
    def _decl(self, src: str, name: str) -> object:
        prog = _program(src)
        for top in prog.declarations:  # type: ignore[attr-defined]
            if getattr(top.decl, "name", None) == name:
                return top.decl
        raise AssertionError(name)

    def test_pure_becomes_singleton_set(self) -> None:
        src = _fn("f", "@Nat.0")
        start, end, repl = effect_row_rewrite(
            src, self._decl(src, "f"), "Async",
        )
        assert src[start:end] == "pure"
        assert repl == "<Async>"

    def test_set_appends_preserving_source(self) -> None:
        src = _fn("f", "@Nat.0", effects="<IO, State<Int>>")
        start, end, repl = effect_row_rewrite(
            src, self._decl(src, "f"), "Async",
        )
        assert src[start:end] == "<IO, State<Int>>"
        assert repl == "<IO, State<Int>, Async>"

    def test_already_present_is_none(self) -> None:
        src = _fn("f", "@Nat.0", effects="<Async>")
        assert effect_row_rewrite(
            src, self._decl(src, "f"), "Async",
        ) is None

    def test_identity_is_base_name(self) -> None:
        """State<Bool> blocks adding State<Int>: effect identity is
        the base name before type arguments."""
        src = _fn("f", "@Nat.0", effects="<State<Bool>>")
        assert effect_row_rewrite(
            src, self._decl(src, "f"), "State<Int>",
        ) is None


class TestAddEffect:
    def _server(self, src: str) -> _FakeServer:
        server = _FakeServer("accept")
        server.open(URI, src, version=1)
        server.published.clear()
        return server

    def test_diamond_propagation_applies(self) -> None:
        """The Phase F3 pin: the whole transitive-caller closure is
        rewritten in one candidate, the bystander untouched."""
        server = self._server(DIAMOND)
        out = _settle(server, lambda: add_effect(server, URI, "target", "Async"))
        assert out["applied"] is True
        assert out["rewritten"] == ["target", "left", "right", "top"]
        doc = server.store.get(URI)
        assert doc is not None
        assert doc.text.count("effects(<Async>)") == 4
        assert doc.text.count("effects(pure)") == 1  # lone
        assert server.published == [URI]

    def test_mixed_rows_append_and_replace(self) -> None:
        """pure callers gain <E>; effect-set callers append; callers
        already naming the effect are skipped but still verified."""
        src = "\n".join([
            _fn("target", "@Nat.0"),
            _fn("io_caller", "target(@Nat.0)", effects="<IO>"),
            _fn("done_caller", "target(@Nat.0)", effects="<Async>"),
        ])
        server = self._server(src)
        out = _settle(server, lambda: add_effect(server, URI, "target", "Async"))
        assert out["applied"] is True
        assert out["rewritten"] == ["target", "io_caller"]
        doc = server.store.get(URI)
        assert doc is not None
        assert "effects(<IO, Async>)" in doc.text
        assert doc.text.count("effects(<Async>)") == 2

    def test_handled_caller_is_not_rewritten(self) -> None:
        """#725: `handled` discharges State<Int> around its only call
        site, so it keeps `pure`; `partial` and `unhandled` still need
        the row."""
        server = self._server(HANDLERS)
        out = _settle(server, lambda: add_effect(server, URI, "target", "State<Int>"))
        assert out["applied"] is True
        assert out["rewritten"] == ["target", "partial", "unhandled"]
        doc = server.store.get(URI)
        assert doc is not None
        assert doc.text.count("effects(<State<Int>>)") == 3
        assert doc.text.count("effects(pure)") == 1  # handled

    def test_mismatched_type_argument_caller_is_rewritten(self) -> None:
        """The bound must not refuse an edit that worked before it:
        `handle[State<Nat>]` leaves `State<Int>` undischarged, so
        `nat_handled` needs the row and the candidate applies."""
        server = self._server(MISMATCHED_INSTANCE)
        out = _settle(server, lambda: add_effect(server, URI, "target", "State<Int>"))
        assert out["applied"] is True
        assert out["ok"] is True
        assert out["diagnostics"] == 0
        assert out["rewritten"] == ["target", "nat_handled"]
        doc = server.store.get(URI)
        assert doc is not None
        assert doc.text.count("effects(<State<Int>>)") == 2

    def test_refinement_argument_caller_is_rewritten(self) -> None:
        """Same shape, one step narrower: a refinement argument reads as
        its base type when rendered, but does not discharge the base
        instance.  Collapse the two and both callers keep `pure`, the
        call sites fail E125, and the gate refuses the whole edit."""
        server = self._server(REFINED_INSTANCE)
        out = _settle(server, lambda: add_effect(server, URI, "target", "Exn<Int>"))
        assert out["applied"] is True
        assert out["ok"] is True
        assert out["diagnostics"] == 0
        assert out["rewritten"] == ["target", "refined", "nested_refined"]
        doc = server.store.get(URI)
        assert doc is not None
        assert doc.text.count("effects(<Exn<Int>>)") == 3

    def test_a_caller_by_the_own_path_is_rewritten(self) -> None:
        """#1558: the caller that calls `target` by the document's own path
        is rewritten with the rest, and the candidate applies.  Left out,
        `by_path` keeps `pure`, its call site fails E125, and the gate
        refuses the whole edit."""
        server = self._server(OWN_PATH)
        out = _settle(server, lambda: add_effect(server, URI, "target", "Async"))
        assert out["applied"] is True
        assert out["ok"] is True
        assert out["rewritten"] == ["target", "by_path", "bare"]
        doc = server.store.get(URI)
        assert doc is not None
        assert doc.text.count("effects(<Async>)") == 3
        assert doc.text.count("effects(pure)") == 1  # lone

    def test_fully_satisfied_is_noop(self) -> None:
        src = _fn("f", "@Nat.0", effects="<Async>")
        server = self._server(src)
        out = _settle(server, lambda: add_effect(server, URI, "f", "Async"))
        assert out == {
            "applied": False,
            "ok": True,
            "proof_delta": None,
            "diagnostics": 0,
            "client": None,
            "client_reason": None,
            "rewritten": [],
        }
        assert server.requests == []
        assert server.published == []

    def test_unknown_fn_raises(self) -> None:
        server = self._server(DIAMOND)
        with pytest.raises(ValueError, match="ghost"):
            _settle(server, lambda: add_effect(server, URI, "ghost", "Async"))

    def test_no_analysis_raises(self) -> None:
        server = _FakeServer()
        with pytest.raises(ValueError, match="open the document"):
            _settle(server, lambda: add_effect(server, URI, "f", "Async"))


# =====================================================================
# #1444 — no edit is verified against, or derived from, a stale analysis
# =====================================================================

def _refusal(server: _FakeServer, script: Callable[[], Any]) -> str:
    """The message of the ``ValueError`` *script* is refused with, or
    ``""`` if it is not refused -- read after the fact, so a cell states
    what happened to the buffer before it states why."""
    try:
        _settle(server, script)
    except ValueError as exc:
        return str(exc)
    return ""


def _stale_after_typing(server: _FakeServer, typed: str) -> None:
    """The user types *typed* and its analysis raises: the handler has
    already stored *typed* at the next version, and the analysis of the
    text before is gone rather than left standing for it."""
    server.unanalysable.add(typed)
    server.type(URI, typed)
    doc = server.store.get(URI)
    assert doc is not None and doc.text == typed
    assert URI not in server.analyses
    assert server.failed == [URI]


#: Each edit workflow, as (the document it runs on, the call).  The two
#: derived ones build their candidate FROM the canonical analysis's text;
#: proposeEdit takes its text whole but is gated against that analysis.
STALE_CASES = {
    "strengthenContract": (CALL_BASE, lambda s: strengthen_contract(
        s, URI, "callee", "ensures", "@Nat.0 >= 0",
    )),
    "addEffect": (DIAMOND, lambda s: add_effect(s, URI, "target", "Async")),
    "proposeEdit": (SPEC_BASE, lambda s: apply_propose_edit(
        s, URI, SHIFTED_BASE,
    )),
    "proposeEdit, forced": (SPEC_BASE, lambda s: apply_propose_edit(
        s, URI, SHIFTED_BASE, force=True,
    )),
}


class TestNoEditFromAnAnalysisTheBufferHasLeft:
    """#1444 review: the store and the analysis table are written one
    after the other by the same ``didChange`` handler, so an analysis
    that RAISES leaves the table describing the text before the buffer's
    current one.  An edit built from that analysis -- a contract spliced
    into it, effect rows rewritten in it -- and guarded by the store's
    version passes the client's version check and overwrites the newer
    text.  An edit gated against it is judged against a text the client
    no longer has.  So every workflow refuses, and sends nothing, unless
    the analysis it reads describes the open document's text."""

    @pytest.mark.parametrize("case", list(STALE_CASES))
    def test_an_edit_on_a_stale_analysis_is_refused(self, case: str) -> None:
        source, call = STALE_CASES[case]
        server = _FakeServer("accept")
        server.open(URI, source, version=1)
        typed = "-- the user's newest line\n" + source
        _stale_after_typing(server, typed)
        refusal = _refusal(server, lambda: call(server))
        assert server.buffers[URI] == (typed, 11)  # the newest line stands
        assert server.requests == []
        assert _doc_state(server) == (typed, 11)
        assert "does not describe the open document" in refusal

    def test_a_no_op_verdict_is_not_read_off_a_stale_analysis(self) -> None:
        """addEffect answers "nothing to do" without building an edit,
        and that answer is read off the analysis too: here the user has
        just taken the row away, and the stale analysis still shows it.
        The workflow refuses before it reads anything, rather than tell
        the agent the row is already there."""
        source = _fn("f", "@Nat.0", effects="<Async>")
        server = _FakeServer("accept")
        server.open(URI, source, version=1)
        typed = source.replace("effects(<Async>)", "effects(pure)")
        _stale_after_typing(server, typed)
        refusal = _refusal(
            server, lambda: add_effect(server, URI, "f", "Async"),
        )
        assert "does not describe the open document" in refusal
        assert server.requests == []

    def test_an_open_document_never_analysed_is_refused(self) -> None:
        """The first analysis raised: the document is open and has no
        analysis at all, so there is no baseline to gate against -- not
        an empty one, which would judge every obligation as new."""
        server = _FakeServer("accept")
        server.unanalysable.add(SPEC_BASE)
        server.open(URI, SPEC_BASE, version=1)
        assert URI not in server.analyses
        refusal = _refusal(
            server, lambda: apply_propose_edit(server, URI, SHIFTED_BASE),
        )
        assert server.requests == []
        assert server.buffers[URI] == (SPEC_BASE, 1)
        assert "does not describe the open document" in refusal

    def test_a_candidate_derived_from_another_text_is_refused(self) -> None:
        """The derivation is pinned on its own: a candidate built from a
        text that is not the open document's is refused even when the
        analysis in the table is current -- the case a workflow that
        awaited between its splice and its request would create."""
        server = _FakeServer("accept")
        server.open(URI, SPEC_BASE, version=1)
        refusal = _refusal(server, lambda: apply_propose_edit(
            server, URI, SHIFTED_BASE, base_text=TYPED_BASE,
        ))
        assert server.requests == []
        assert _doc_state(server) == (SPEC_BASE, 1)
        assert "no longer the open document" in refusal

    @pytest.mark.parametrize("case", ["strengthenContract", "addEffect"])
    def test_a_candidate_is_refused_once_the_document_moves_past_it(
        self, case: str, monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        """The two derived workflows pass the text they built from, so
        the derivation is checked where the edit is sent, not only where
        it was built.  Modelled by a ``didChange`` -- one that analyses
        cleanly, leaving nothing stale in the table -- landing between
        the build and the request: the candidate is then made from a text
        the buffer has left, and must not go out under the new version."""
        import vera.lsp.workflows as workflows

        source, call = STALE_CASES[case]
        server = _FakeServer("accept")
        server.open(URI, source, version=1)
        typed = "-- the user's newest line\n" + source
        send_for_real = workflows.apply_propose_edit

        def moved_first(*args: Any, **kwargs: Any) -> Any:
            server.type(URI, typed)  # analyses cleanly: nothing is stale
            return send_for_real(*args, **kwargs)

        monkeypatch.setattr(workflows, "apply_propose_edit", moved_first)
        refusal = _refusal(server, lambda: call(server))
        assert server.buffers[URI] == (typed, 11)
        assert server.requests == []
        assert "no longer the open document" in refusal

    def test_a_current_analysis_is_not_refused(self) -> None:
        """Premise: the same calls on a document whose analysis is
        current go through, so the refusals above are about staleness."""
        for case, (source, call) in STALE_CASES.items():
            server = _FakeServer("accept")
            server.open(URI, source, version=1)
            out = _settle(server, lambda: call(server))
            assert out["client"] == "applied", (case, out)


class TestARequestMadeFromAnOlderVersion:
    """#1444 review: a proposal the AGENT made from an older text.  The
    server guards the edit with the version it has seen, so without a
    word from the client it cannot know that the agent's text predates
    typing the server already has.  The optional ``version`` says which
    version the request was made from; when it is not the open
    document's, every edit workflow refuses and sends nothing.  Absent,
    nothing changes -- the risk the documentation names."""

    @pytest.mark.parametrize("case", list(STALE_CASES))
    def test_an_older_version_is_refused(self, case: str) -> None:
        source, _ = STALE_CASES[case]
        server = _FakeServer("accept")
        server.open(URI, source, version=1)
        typed = "-- the user's newest line\n" + source
        server.type(URI, typed)  # analysed cleanly, at version 11
        refusal = _refusal(server, lambda: _with_version(case, server, 1))
        assert server.buffers[URI] == (typed, 11)
        assert server.requests == []
        assert "made from version 1" in refusal
        assert "is at version 11" in refusal

    @pytest.mark.parametrize("case", list(STALE_CASES))
    def test_the_current_version_goes_through(self, case: str) -> None:
        source, _ = STALE_CASES[case]
        server = _FakeServer("accept")
        server.open(URI, source, version=1)
        out = _settle(server, lambda: _with_version(case, server, 1))
        assert out["client"] == "applied", out

    def test_the_version_is_checked_before_a_no_op_verdict(self) -> None:
        """addEffect answers "nothing to do" without sending an edit, and
        that answer is still about the version the client asked about:
        a request made from an older version is refused, not told the
        rows are already there."""
        source = _fn("f", "@Nat.0", effects="<Async>")
        server = _FakeServer("accept")
        server.open(URI, source, version=1)
        server.type(URI, "-- the user's newest line\n" + source)
        refusal = _refusal(server, lambda: add_effect(
            server, URI, "f", "Async", version=1,
        ))
        assert "made from version 1" in refusal

    def test_a_version_of_an_unopened_document_is_refused(self) -> None:
        server = _FakeServer("accept")
        refusal = _refusal(server, lambda: apply_propose_edit(
            server, URI, SPEC_BASE, version=0,
        ))
        assert server.requests == []
        assert "open the document first" in refusal

    def test_no_version_is_the_behaviour_without_one(self) -> None:
        """Absent, the request is judged exactly as before: the typing
        the server has seen is replaced, which is the risk a client that
        cannot send ``version`` accepts."""
        server = _FakeServer("accept")
        server.open(URI, SPEC_BASE, version=1)
        server.type(URI, TYPED_BASE)
        out = _settle(
            server, lambda: apply_propose_edit(server, URI, SHIFTED_BASE),
        )
        assert out["client"] == "applied"
        assert server.buffers[URI] == (SHIFTED_BASE, 21)


def _with_version(case: str, server: _FakeServer, version: int) -> Any:
    """The *case* workflow call of ``STALE_CASES``, with ``version``."""
    if case == "strengthenContract":
        return strengthen_contract(
            server, URI, "callee", "ensures", "@Nat.0 >= 0", version=version,
        )
    if case == "addEffect":
        return add_effect(server, URI, "target", "Async", version=version)
    return apply_propose_edit(
        server, URI, SHIFTED_BASE, force=case.endswith("forced"),
        version=version,
    )


class TestEveryReaderAnswersFromTheOpenText:
    """#1444 review: after a failed analysis the table holds no entry for
    a text the store has left, and every reader of the table answers
    only from an entry that describes the open text."""

    def test_the_accessor_returns_only_the_open_texts_analysis(self) -> None:
        from vera.lsp.documents import Document
        from vera.lsp.features import current_analysis

        analysis = analyze(VerificationSession(), URI, SPEC_BASE)
        assert current_analysis(None, analysis) is None  # not open
        assert current_analysis(
            Document(uri=URI, text=SPEC_BASE, version=1), analysis,
        ) is analysis
        assert current_analysis(
            Document(uri=URI, text=TYPED_BASE, version=2), analysis,
        ) is None  # stale
        assert current_analysis(
            Document(uri=URI, text=SPEC_BASE, version=1), None,
        ) is None  # none at all

    def test_a_forced_stale_entry_reaches_no_reader(self) -> None:
        """Each of the real server's readers, handed a table whose entry
        describes a text the store has left -- the invariant broken on
        purpose -- answers as for a document with no analysis, or, for a
        proof delta, refuses as ``vera/proposeEdit`` does.  Every probe
        sits where the stale analysis HAS an answer, so a reader that
        used it would return one: hover and definition on `@Nat.0`, and
        completion inside a typed hole."""
        from vera.lsp.server import create_server

        server = create_server()
        features = server.protocol.fm.features
        doc = lsp.TextDocumentIdentifier(uri=URI)
        at = lsp.Position(line=5, character=3)  # `@Nat.0` in SPEC_BASE
        hole = lsp.Position(line=6, character=2)  # the `?` in FEATURE_SRC

        def answers() -> tuple[Any, Any, Any]:
            return (
                features[lsp.TEXT_DOCUMENT_HOVER](
                    lsp.HoverParams(text_document=doc, position=at)),
                features[lsp.TEXT_DOCUMENT_DEFINITION](
                    lsp.DefinitionParams(text_document=doc, position=at)),
                features[lsp.TEXT_DOCUMENT_COMPLETION](
                    lsp.CompletionParams(text_document=doc, position=hole)),
            )

        # The stale entry for hover/definition: SPEC_BASE, with
        # TYPED_BASE open.
        old = analyze(server.session, URI, SPEC_BASE)
        assert hover_at(old, at) is not None
        assert definition_at(old, at) is not None
        server.store.open(URI, TYPED_BASE, 2)
        server.analyses[URI] = old
        assert answers()[:2] == (None, None)
        with pytest.raises(JsonRpcInvalidParams, match="does not describe"):
            features["vera/speculativeEdit"]({"uri": URI, "text": SPEC_BASE})
        # The stale entry for completion: a text with a typed hole.
        holed = analyze(server.session, URI, FEATURE_SRC)
        assert completion_at(holed, hole) is not None
        server.store.change(URI, "-- typed\n" + FEATURE_SRC, 3)
        server.analyses[URI] = holed
        assert answers()[2] is None
        # Controls: the same readers DO answer from a current entry.
        server.store.change(URI, SPEC_BASE, 4)
        server.analyses[URI] = old
        assert answers()[0] is not None
        assert features["vera/speculativeEdit"](
            {"uri": URI, "text": SPEC_BASE},
        )["proof_delta"]["unchanged"] == len(old.obligations)
        server.store.change(URI, FEATURE_SRC, 5)
        server.analyses[URI] = holed
        assert answers()[2] is not None

    def test_a_proof_delta_needs_an_open_current_document(self) -> None:
        """``vera/speculativeEdit`` is refused on the terms
        ``vera/proposeEdit`` is: an unopened document, an open one with
        no analysis of its text, and a request made from another
        version.  An empty baseline would read as "every proof kept"
        about a text nothing was measured against."""
        from vera.lsp.server import create_server

        server = create_server()
        speculate = server.protocol.fm.features["vera/speculativeEdit"]
        with pytest.raises(JsonRpcInvalidParams, match="open the document"):
            speculate({"uri": URI, "text": SPEC_BASE})
        server.store.open(URI, SPEC_BASE, 1)  # open, never analysed
        with pytest.raises(JsonRpcInvalidParams, match="does not describe"):
            speculate({"uri": URI, "text": SPEC_BASE})
        server.analyses[URI] = analyze(server.session, URI, SPEC_BASE)
        with pytest.raises(JsonRpcInvalidParams, match="made from version 0"):
            speculate({"uri": URI, "text": SPEC_BASE, "version": 0})
        out = speculate({"uri": URI, "text": SPEC_BASE, "version": 1})
        assert out["proof_delta"]["unchanged"] > 0


# =====================================================================
# #728 — LSP diagnostics carry the full instruction contract
# =====================================================================

VIOLATING_CALL = (
    "private fn need_pos(@Int -> @Int)\n"
    "  requires(@Int.0 > 0)\n"
    "  ensures(true)\n"
    "  effects(pure)\n"
    "{\n"
    "  @Int.0\n"
    "}\n"
    "\n"
    "public fn caller(-> @Int)\n"
    "  requires(true)\n"
    "  ensures(true)\n"
    "  effects(pure)\n"
    "{\n"
    "  let @Int = need_pos(0);\n"
    "  @Int.0\n"
    "}\n"
)


class TestDiagnosticInstructionContract:
    def test_message_carries_rationale_and_fix(self) -> None:
        """The editor surface honours the same diagnostics-as-
        instructions contract as --json: description, rationale, and
        the Fix: paragraph all reach the LSP message (#728)."""
        a = analyze(VerificationSession(), URI, VIOLATING_CALL)
        e501 = [
            d for d in to_lsp_diagnostics(a) if d.code == "E501"
        ]
        assert len(e501) == 1  # also pins #727 at the LSP surface
        message = e501[0].message
        assert "may violate the callee's precondition" in message
        assert "At this call site: 0 > 0" in message
        assert "Fix:" in message
        # The fix is concrete code in call-site terms, not generic
        # advice: the guard renders the actual call and the
        # substituted precondition.
        assert "Guard the call so the precondition holds" in message
        assert "if 0 > 0 then { need_pos(0) } else { ... }" in message
        assert "requires(0 > 0)" in message
        # The rationale paragraph travels too.
        assert "SMT solver could not prove" in message

    def test_message_without_fix_or_rationale_is_bare(self) -> None:
        """A diagnostic carrying neither rationale nor fix maps to the
        bare description — no stray labels or separators appear."""
        from vera.errors import Diagnostic, SourceLocation
        from vera.lsp.convert import LineIndex

        from vera.lsp.features import Analysis

        bare = Diagnostic(
            description="bare description",
            location=SourceLocation(file=URI, line=1, column=0),
        )
        a = Analysis(
            uri=URI, text="x\n", index=LineIndex("x\n"),
            diagnostics=[bare],
        )
        msgs = [d.message for d in to_lsp_diagnostics(a)]
        assert msgs[0] == "bare description"
