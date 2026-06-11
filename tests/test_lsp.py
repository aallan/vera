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
        a = _analyze(FEATURE_SRC)
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
        session = VerificationSession()
        result = session.verify_source(SPEC_BASE, file="file:///s.vera")
        assert result.ok
        return session, result.obligations

    def test_identical_text_reports_all_unchanged(self) -> None:
        session, baseline = self._baseline()
        out = speculative_edit(
            session, baseline, "file:///s.vera", SPEC_BASE,
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
            session, baseline, "file:///s.vera", broken,
        )
        und = out["proof_delta"]["newly_undischarged"]
        assert any(
            i["kind"] == "nat_sub" and i["status_after"] == "violated"
            for i in und
        )
        # The edit must NOT have been committed anywhere — the session
        # still replays the ORIGINAL source fully from cache.
        again = session.verify_source(SPEC_BASE, file="file:///s.vera")
        assert again.ok
        assert session.last_run_stats.replayed_fns >= 1

    def test_strengthening_edit_reports_newly_discharged(self) -> None:
        """The reverse direction: starting from the weak (violated)
        state, the speculative strong contract discharges the
        subtraction obligation."""
        weak = SPEC_BASE.replace("requires(@Nat.0 >= 1)", "requires(true)")
        session = VerificationSession()
        result = session.verify_source(weak, file="file:///w.vera")
        baseline = result.obligations
        out = speculative_edit(
            session, baseline, "file:///w.vera", SPEC_BASE,
        )
        dis = out["proof_delta"]["newly_discharged"]
        assert any(i["kind"] == "nat_sub" for i in dis)

    def test_parse_error_reports_not_ok(self) -> None:
        session, baseline = self._baseline()
        out = speculative_edit(
            session, baseline, "file:///s.vera", "public fn broken(",
        )
        assert out["ok"] is False
        assert out["proof_delta"] is None
        assert out["diagnostics"] >= 1

    def test_type_error_reports_not_ok_with_count(self) -> None:
        session, baseline = self._baseline()
        bad = SPEC_BASE.replace("@Nat.0 - 1", '"not a nat"')
        out = speculative_edit(
            session, baseline, "file:///s.vera", bad,
        )
        assert out["ok"] is False
        assert out["proof_delta"] is None
        assert out["diagnostics"] >= 1

    def test_deleted_function_reports_removed(self) -> None:
        session, baseline = self._baseline()
        out = speculative_edit(
            session, baseline, "file:///s.vera",
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

import concurrent.futures  # noqa: E402
import threading  # noqa: E402
import types  # noqa: E402

from vera.lsp.server import _param  # noqa: E402
from vera.lsp.workflows import (  # noqa: E402
    apply_propose_edit,
    full_document_range,
    propose_edit,
)

# Same program, every span shifted one line: parses identically but all
# obligation content keys change, so the delta is removed+rediscovered
# with nothing undischarged — a "clean different text" fixture that
# needs no new Vera semantics.
SHIFTED_BASE = "-- shifted\n" + SPEC_BASE
BROKEN_BASE = SPEC_BASE.replace("requires(@Nat.0 >= 1)", "requires(true)")
URI = "file:///p.vera"


class _FakeServer:
    """Structural stand-in for ``VeraLanguageServer``.

    ``apply_propose_edit`` touches exactly these members, so the
    wiring tests stay transport-free; the stdio e2e test owns real
    handler registration.  ``analyze_and_publish`` mirrors the real
    method's lock-then-publish shape, and ``workspace_apply_edit``
    mirrors pygls' real signature by returning a resolved Future
    carrying the client's verdict (``client_applies``).
    """

    def __init__(self) -> None:
        self.store = DocumentStore()
        self.session = VerificationSession()
        self.analysis_lock = threading.Lock()
        self.analyses: dict[str, object] = {}
        self.applied_edits: list[lsp.ApplyWorkspaceEditParams] = []
        self.published: list[str] = []
        self.client_applies = True

    def workspace_apply_edit(
        self, params: lsp.ApplyWorkspaceEditParams,
    ) -> concurrent.futures.Future[lsp.ApplyWorkspaceEditResult]:
        self.applied_edits.append(params)
        fut: concurrent.futures.Future[lsp.ApplyWorkspaceEditResult]
        fut = concurrent.futures.Future()
        fut.set_result(
            lsp.ApplyWorkspaceEditResult(applied=self.client_applies),
        )
        return fut

    def analyze_and_publish(self, uri: str, text: str) -> None:
        with self.analysis_lock:
            self.analyses[uri] = analyze(self.session, uri, text)
        self.published.append(uri)


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


class TestProposeEditWiring:
    def _server(self) -> _FakeServer:
        server = _FakeServer()
        server.store.open(URI, SPEC_BASE, version=1)
        server.analyze_and_publish(URI, SPEC_BASE)
        server.published.clear()
        return server

    def test_apply_path_round_trips(self) -> None:
        server = self._server()
        out = apply_propose_edit(server, URI, SHIFTED_BASE)
        assert out["applied"] is True
        # One workspace/applyEdit, full-document replacement.
        assert len(server.applied_edits) == 1
        (edit,) = server.applied_edits[0].edit.changes[URI]
        assert edit.new_text == SHIFTED_BASE
        assert edit.range.start == lsp.Position(line=0, character=0)
        # SPEC_BASE ends with a newline: end is the virtual line past
        # the last, column 0.
        assert edit.range.end == lsp.Position(
            line=SPEC_BASE.count("\n"), character=0,
        )
        # Canonical state updated and republished.
        doc = server.store.get(URI)
        assert doc is not None
        assert doc.text == SHIFTED_BASE
        assert doc.version == 2
        assert server.published == [URI]

    def test_refuse_path_touches_nothing(self) -> None:
        server = self._server()
        before = server.analyses[URI]
        out = apply_propose_edit(server, URI, BROKEN_BASE)
        assert out["applied"] is False
        assert server.applied_edits == []
        assert server.published == []
        doc = server.store.get(URI)
        assert doc is not None
        assert doc.text == SPEC_BASE
        assert doc.version == 1
        assert server.analyses[URI] is before

    def test_client_refusal_does_not_roll_back(self) -> None:
        """workspace/applyEdit is fire-and-forget by design: the
        response's ``applied`` reports the GATE verdict, canonical
        state reflects the request immediately, and a client that
        declines re-converges on its next full-sync didChange.  Pinned
        so a future move to await-the-client semantics is a conscious
        change, not drift."""
        server = self._server()
        server.client_applies = False
        out = apply_propose_edit(server, URI, SHIFTED_BASE)
        assert out["applied"] is True
        doc = server.store.get(URI)
        assert doc is not None
        assert doc.text == SHIFTED_BASE  # no rollback
        assert server.published == [URI]
        # The heal path: the editor's unchanged buffer full-syncs back
        # and simply wins, exactly like any other didChange.
        server.store.change(URI, SPEC_BASE, version=3)
        doc = server.store.get(URI)
        assert doc is not None
        assert doc.text == SPEC_BASE

    def test_apply_to_unopened_document_uses_clamp_range(self) -> None:
        """proposeEdit on a URI the client never opened: empty
        baseline, sentinel whole-file range (clients clamp), and the
        store learns the document."""
        server = _FakeServer()
        out = apply_propose_edit(server, URI, SPEC_BASE)
        assert out["applied"] is True
        (edit,) = server.applied_edits[0].edit.changes[URI]
        assert edit.range.end.line == 2**31 - 1
        doc = server.store.get(URI)
        assert doc is not None
        assert doc.text == SPEC_BASE
        assert doc.version == 0


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


class TestFullDocumentRange:
    def test_none_document_is_clamp_sentinel(self) -> None:
        r = full_document_range(None)
        assert r.start == lsp.Position(line=0, character=0)
        assert r.end.line == 2**31 - 1

    def test_trailing_newline_ends_on_virtual_line(self) -> None:
        from vera.lsp.documents import Document

        r = full_document_range(Document(uri=URI, text="a\nb\n"))
        assert r.end == lsp.Position(line=2, character=0)

    def test_no_trailing_newline_ends_in_utf16_units(self) -> None:
        from vera.lsp.documents import Document

        # ASTRAL_LINE = "ab🎉cd": 5 code points, 6 UTF-16 units.
        r = full_document_range(Document(uri=URI, text=ASTRAL_LINE))
        assert r.end == lsp.Position(line=0, character=6)
